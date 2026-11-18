// Integration regression for the pptxgenjs Notes Master PowerPoint discards on save.
// Run with: node tests/test_apply_theme.js
const assert = require("assert");
const fs = require("fs");
const os = require("os");
const path = require("path");
const { spawnSync } = require("child_process");
const PptxGenJS = require("pptxgenjs");
const JSZip = require(require.resolve("jszip", { paths: [require.resolve("pptxgenjs")] }));
const { applyTheme } = require("../scripts/apply_theme");

async function main() {
	const dir = fs.mkdtempSync(path.join(os.tmpdir(), "pptx-notes-master-"));
	const deckPath = path.join(dir, "deck.pptx");
	try {
		const pptx = new PptxGenJS();
		pptx.layout = "LAYOUT_WIDE";
		const slide = pptx.addSlide();
		slide.addText("Notes Master regression");
		slide.addNotes("Speaker notes survive PowerPoint save.");
		await pptx.writeFile({ fileName: deckPath });
		const originalZip = await JSZip.loadAsync(fs.readFileSync(deckPath));
		const originalPresentation = await originalZip.file("ppt/presentation.xml").async("string");
		assert(originalPresentation.indexOf("<p:notesMasterIdLst") > originalPresentation.indexOf("<p:sldIdLst"), "fixture reproduces pptxgenjs element order");
		const originalMaster = Object.keys(originalZip.files).find((name) => /^ppt\/notesMasters\/notesMaster\d+\.xml$/.test(name));
		assert(originalMaster, "pptxgenjs emitted a notes master");
		const originalRels = await originalZip.file(originalMaster.replace(/(notesMaster\d+\.xml)$/, "_rels/$1.rels")).async("string");
		assert.match(originalRels, /Target="\.\.\/theme\/theme1\.xml"/, "fixture reproduces the shared notes theme");
		await applyTheme(deckPath, {
			name: "Regression",
			colors: {
				dk1: "000000", lt1: "FFFFFF", dk2: "333333", lt2: "EEEEEE",
				accent1: "4472C4", accent2: "ED7D31", accent3: "A5A5A5", accent4: "FFC000",
				accent5: "5B9BD5", accent6: "70AD47", hlink: "0563C1", folHlink: "954F72",
			},
		});

		const zip = await JSZip.loadAsync(fs.readFileSync(deckPath));
		assert.equal(Object.values(zip.files).filter((entry) => entry.dir).length, 0, "post-processing leaves no ZIP folder entries");
		const presentation = await zip.file("ppt/presentation.xml").async("string");
		assert(presentation.indexOf("<p:notesMasterIdLst") < presentation.indexOf("<p:sldIdLst"), "notesMasterIdLst follows schema order");
		assert.match(presentation, /<p:notesSz cx="6858000" cy="9144000"\/>/, "notes page uses the PowerPoint page size");

		const masterName = Object.keys(zip.files).find((name) => /^ppt\/notesMasters\/notesMaster\d+\.xml$/.test(name));
		assert(masterName, "pptxgenjs emitted a notes master");
		const master = await zip.file(masterName).async("string");
		for (const type of ["sldImg", "body", "sldNum"]) {
			assert(master.includes(`<p:ph type="${type}"`), `notes master has ${type} placeholder`);
		}
		const shapes = [...master.matchAll(/<p:sp>[\s\S]*?<\/p:sp>/g)].map(([xml]) => xml);
		assert.equal(shapes.length, 3, "notes master contains only the three supported placeholders");
		assert(shapes.every((xml) => xml.includes("<a:xfrm>")), "each notes placeholder has an explicit transform");
		assert(shapes.every((xml) => xml.includes('<a:spLocks noGrp="1"/>') || xml.includes('<a:spLocks noGrp="1" noRot="1" noChangeAspect="1"/>')), "Notes Page placeholders have PowerPoint shape locks");
		assert(shapes.find((xml) => xml.includes('<p:ph type="sldImg"')).includes('noChangeAspect="1"'), "slide image placeholder preserves its aspect ratio");

		const relsPath = masterName.replace(/(notesMaster\d+\.xml)$/, "_rels/$1.rels");
		const rels = await zip.file(relsPath).async("string");
		const target = rels.match(/<Relationship\b(?=[^>]*\bType="[^"]*\/theme")(?=[^>]*\bTarget="([^"]+)")[^>]*\/?\s*>/)[1];
		assert.notEqual(path.posix.basename(target), "theme1.xml", "notes master has its own theme part");
		assert(zip.file(`ppt/theme/${path.posix.basename(target)}`), "notes theme part exists");
		const contentTypes = await zip.file("[Content_Types].xml").async("string");
		assert(contentTypes.includes(`/ppt/theme/${path.posix.basename(target)}`), "notes theme has a content type override");

		const python = process.env.PYTHON || (process.platform === "win32" ? "python" : "python3");
		const xmlCheck = spawnSync(python, ["-c", "import sys, zipfile, xml.etree.ElementTree as ET; z=zipfile.ZipFile(sys.argv[1]); [ET.fromstring(z.read(n)) for n in z.namelist() if n.endswith(('.xml', '.rels'))]", deckPath], { encoding: "utf8" });
		assert.equal(xmlCheck.status, 0, `all package XML is well formed:\n${xmlCheck.stdout}\n${xmlCheck.stderr}`);
		const schema = path.join(__dirname, "../scripts/office/schemas/ISO-IEC29500-4_2016/pml.xsd");
		const xsdScript = [
			"import sys, zipfile",
			"from lxml import etree",
			"schema = etree.XMLSchema(etree.parse(sys.argv[2]))",
			"with zipfile.ZipFile(sys.argv[1]) as package:",
			"    for part in ('ppt/presentation.xml', 'ppt/notesMasters/notesMaster1.xml'):",
			"        document = etree.fromstring(package.read(part))",
			"        if not schema.validate(document): raise AssertionError(f'{part}: {schema.error_log}')",
		].join("\n");
		const xsdCheck = spawnSync(python, ["-c", xsdScript, deckPath, schema], { encoding: "utf8" });
		assert.equal(xsdCheck.status, 0, `presentation and notes master pass the bundled XSD:\n${xsdCheck.stdout}\n${xsdCheck.stderr}`);
		const validation = spawnSync(python, [path.join(__dirname, "../scripts/office/validate.py"), deckPath], { encoding: "utf8" });
		assert.equal(validation.status, 0, `office validator accepts output:\n${validation.stdout}\n${validation.stderr}`);
		console.log("PASS - pptxgenjs Notes Master meets schema order, has a dedicated theme and retained placeholders, and passes package validation");
	} finally {
		fs.rmSync(dir, { recursive: true, force: true });
	}
}

main().catch((error) => {
	console.error(error);
	process.exitCode = 1;
});
