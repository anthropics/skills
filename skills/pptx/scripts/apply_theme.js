// Give a deck pptxgenjs wrote its own theme colors and theme name. pptxgenjs sets the theme's
// two fonts (pres.theme) but hard-codes Office's palette, so scheme colors resolve to Office
// blue and orange until the deck's colors are written into ppt/theme/theme1.xml.
//
//   const { applyTheme } = require("<this skill's directory>/scripts/apply_theme.js");
//   await pres.writeFile({ fileName: "deck.pptx" });
//   await applyTheme("deck.pptx", {
//     name: "Northwind",
//     colors: { dk1, lt1, dk2, lt2, accent1, accent2, accent3, accent4, accent5, accent6, hlink, folHlink },
//   });   // extra keys (headFontFace, ...) are ignored, and the twelve colors may sit beside name instead
//
//   node scripts/apply_theme.js deck.pptx theme.json [out.pptx]     # the same, from a shell
//
// Colors are six hex digits, no "#". The deck is rewritten in place unless a third argument
// names another file. It throws, changing nothing, if a color anywhere in the deck is not six
// hex digits, which is what a scheme color passed to a hex-only option turns into.
//
// As the step that rewrites the deck after pres.writeFile(), it also handles two faults pptxgenjs writes
// that make PowerPoint offer to repair the deck: it mends <c:crossesAt val="autoZero"/>, and it
// throws on a line dash that is not a dash style.
const fs = require("fs");

// jszip comes with pptxgenjs but is not always installed where a bare require("jszip") finds
// it, so it is loaded from beside pptxgenjs. Both are found the way any require() in this file
// would find them: from this file's directory upward, then NODE_PATH and Node's global folders.
// No search starts at the working directory or the calling script's directory.
function loadJSZip() {
	try {
		return require(require.resolve("jszip", { paths: [require.resolve("pptxgenjs")] }));
	} catch {
		throw new Error(`pptxgenjs and the jszip that comes with it cannot be found from ${__filename}. If pptxgenjs is installed beside your own script, run node with NODE_PATH set to that node_modules folder. Nothing was changed.`);
	}
}

const SLOTS = ["dk1", "lt1", "dk2", "lt2", "accent1", "accent2", "accent3", "accent4", "accent5", "accent6", "hlink", "folHlink"];
// A name or value from the deck, for an error a model reads: quoted, cut, and with nothing unprintable left raw.
const shown = (s) => JSON.stringify(String(s).slice(0, 80)).replace(/[\p{C}\u2028\u2029]/gu, (c) => "\\u{" + c.codePointAt(0).toString(16) + "}");
const DASHES = ["solid", "dot", "dash", "lgDash", "dashDot", "lgDashDot", "lgDashDotDot", "sysDash", "sysDot", "sysDashDot", "sysDashDotDot"];

function themeXml(xml, theme) {
	if (!theme || !theme.name) throw new Error("theme.name is required. Nothing was changed.");
	// The name goes into XML attributes: drop control characters, escape & < > and the double quote.
	const name = String(theme.name).replace(/[\x00-\x08\x0B\x0C\x0E-\x1F]/g, "").replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
	const colors = theme.colors || theme; // { name, colors: {...} }, or flat { name, dk1, ... }
	for (const k of SLOTS) {
		if (!/^[0-9A-Fa-f]{6}$/.test(String(colors[k]))) throw new Error(`theme.colors.${k} is ${JSON.stringify(colors[k])}; it must be six hex digits with no "#" (slots: ${SLOTS.join(" ")}). Nothing was changed.`);
	}
	const scheme = `<a:clrScheme name="${name}">` + SLOTS.map((k) => `<a:${k}><a:srgbClr val="${String(colors[k]).toUpperCase()}"/></a:${k}>`).join("") + "</a:clrScheme>";
	// Function replacements, so a "$" in the name is not read as a replacement pattern.
	// The theme, its color scheme and its font scheme each carry a name; none should still say Office.
	const out = xml
		.replace(/<a:clrScheme\b[\s\S]*?<\/a:clrScheme>/, () => scheme)
		.replace(/(<a:(?:theme|fontScheme)\b[^>]*?\bname=")[^"]*"/g, (_, head) => `${head}${name}"`);
	if (!out.includes(scheme)) throw new Error("ppt/theme/theme1.xml has no <a:clrScheme> to replace; this script expects the theme part pptxgenjs writes. Nothing was changed.");
	return out;
}

async function applyTheme(deckPath, theme, outPath = deckPath) {
	const zip = await loadJSZip().loadAsync(fs.readFileSync(deckPath));
	const part = "ppt/theme/theme1.xml"; // the one theme part pptxgenjs writes; the slide master and the notes master share it
	if (!zip.file(part)) throw new Error(`${deckPath} has no ${part}; this script is for decks pptxgenjs wrote. Nothing was changed.`);
	zip.file(part, themeXml(await zip.file(part).async("string"), theme));

	// A scheme color given to a hex-only option is written as <a:srgbClr val="bg2"/>, which is
	// not a color. pptxgenjs does not warn; stop here instead.
	for (const name of Object.keys(zip.files)) {
		if (!name.endsWith(".xml")) continue;
		const xml = await zip.file(name).async("string");
		const bad = xml.match(/<a:srgbClr val="((?![0-9A-Fa-f]{6}")[^"]*)"/);
		if (bad) throw new Error(`${shown(name)} has an <a:srgbClr> whose val is ${shown(bad[1])}, not six hex digits. Usually a scheme color was given to an option that takes hex only (valGridLine.color, catGridLine.color, shadow.color, or chartColors / invertedColors on a one-series bar chart). Pass the six-digit hex from your theme object there and rebuild. Nothing was changed.`);

		// pptxgenjs writes a dash option through unchecked, and an array as "solid,dash".
		const dash = [...xml.matchAll(/<a:prstDash val="([^"]*)"/g)].find((m) => !DASHES.includes(m[1].trim()));
		if (dash) throw new Error(`${shown(name)} has an <a:prstDash> whose val is ${shown(dash[1])}, which is not a dash style, and PowerPoint would offer to repair the deck. Give line.dashType, a chart's lineDash (one word for the whole chart, not an array), catAxisLineStyle or valAxisLineStyle one of: ${DASHES.join(" ")}. Then rebuild. Nothing was changed.`);

		// pptxgenjs writes valAxisCrossesAt: 0 as <c:crossesAt val="autoZero"/>. <c:crossesAt> takes
		// a number; the word belongs in <c:crosses>, where it means the same: cross at zero.
		if (xml.includes('<c:crossesAt val="autoZero"/>')) zip.file(name, xml.replaceAll('<c:crossesAt val="autoZero"/>', '<c:crosses val="autoZero"/>'));
	}
	// A ZIP entry for a folder ("ppt/slides/") is not a part, and pptxgenjs writes one per folder.
	// A cloud co-editing service reported issues editing decks that carry them. They are dropped
	// here for that reason, not to save space. (zip.remove() would take the folder's files too.)
	for (const name of Object.keys(zip.files)) if (zip.files[name].dir) delete zip.files[name];

	fs.writeFileSync(outPath, await zip.generateAsync({ type: "nodebuffer", compression: "DEFLATE" }));
}

module.exports = { applyTheme };

if (require.main === module) {
	const [deck, themeFile, out] = process.argv.slice(2);
	if (!deck || !themeFile) {
		console.error("usage: node apply_theme.js deck.pptx theme.json [out.pptx]");
		process.exit(2);
	}
	let theme;
	try {
		theme = JSON.parse(fs.readFileSync(themeFile, "utf8"));
	} catch (e) {
		console.error(`Error: cannot read ${themeFile} as JSON (${e.message}). Nothing was changed.`);
		process.exit(1);
	}
	applyTheme(deck, theme, out || deck).then(
		() => console.log(`Theme written to ${out || deck}`),
		(e) => { console.error(`Error: ${e.message}`); process.exit(1); }
	);
}
