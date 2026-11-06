#!/usr/bin/env node
/*
 * Recalculate an .xlsx/.xlsm workbook in place with the xlcalc formula engine, for
 * environments without LibreOffice. writeKept stores the calculated values over the
 * file it read and leaves every part the workbook does not model (charts, shapes,
 * themes, printer settings, vbaProject.bin) as the file has it.
 *
 *   node recalc_xlcalc.mjs <file.xlsx>
 *
 * Prints one JSON object on stdout. On failure that object carries an `error` key and
 * the exit code is 3 (the xlcalc package is missing) or 2 (anything else).
 */

import { readFile, rename, writeFile } from "node:fs/promises";
import { createRequire } from "node:module";
import { delimiter, dirname, join, resolve } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";

const SUBPATHS = ["xlcalc", "xlcalc/xlsx/keep"];

function fail(error, extra) {
  process.stdout.write(JSON.stringify(Object.assign({ error }, extra || {})) + "\n");
  process.exit(error === "xlcalc-not-found" ? 3 : 2);
}

function localBases(file) {
  const scriptDir = dirname(fileURLToPath(import.meta.url));
  return [process.env.XLSX_XLCALC_PATH, scriptDir, dirname(resolve(file)), process.cwd()];
}

function globalRoots() {
  const roots = [];
  if (process.platform === "win32" && process.env.APPDATA) {
    roots.push(join(process.env.APPDATA, "npm", "node_modules"));
  }
  const prefix = process.env.PREFIX || process.env.npm_config_prefix || "/usr/local";
  roots.push(join(prefix, "lib", "node_modules"), join(prefix, "node_modules"));
  roots.push(join(dirname(process.execPath), "..", "lib", "node_modules")); // nvm and mise layouts
  if (process.env.NODE_PATH) roots.push(...process.env.NODE_PATH.split(delimiter));
  return roots;
}

async function fromBase(base) {
  const requireFromBase = createRequire(resolve(base, "probe.js"));
  const modules = await Promise.all(
    SUBPATHS.map((spec) => import(pathToFileURL(requireFromBase.resolve(spec)).href)),
  );
  return { compute: modules[0].compute, keep: modules[1] };
}

async function loadXlcalc(file) {
  const bases = localBases(file);
  bases.push(dirname(resolve(file))); // one more level, for a project that hoists the package
  for (const base of Array.from(new Set(bases.filter(Boolean)))) {
    try {
      return await fromBase(base);
    } catch {
      /* try the next place */
    }
  }
  for (const root of globalRoots()) {
    try {
      return await fromBase(root);
    } catch {
      /* fall through to the bare import */
    }
  }
  try {
    const loaded = await Promise.all(SUBPATHS.map((spec) => import(spec)));
    return { compute: loaded[0].compute, keep: loaded[1] };
  } catch {
    return null;
  }
}

function countAnswers(book, result) {
  let formulas = 0;
  const missing = [];
  result.sheets.forEach((sheet, index) => {
    const bookCells = (book.sheets[index] || {}).cells || {};
    for (const [address, cell] of Object.entries(bookCells)) {
      if (!cell || !cell.formula) continue;
      formulas += 1;
      const answer = (sheet.cells || {})[address];
      if (!answer || (answer.value === undefined && answer.held === undefined)) {
        missing.push(sheet.name + "!" + address);
      }
    }
  });
  return { formulas: formulas, missing: missing };
}

async function main() {
  const target = process.argv[2];
  if (!target) fail("usage: node recalc_xlcalc.mjs <file.xlsx>");

  const major = Number(process.versions.node.split(".")[0]);
  if (major < 20) fail("xlcalc needs Node 20.19 or newer; this is Node " + process.versions.node);

  const engine = await loadXlcalc(target);
  if (!engine) {
    fail("xlcalc-not-found", {
      hint: "npm install xlcalc (in the working directory or in the skill folder), or set XLSX_XLCALC_PATH to a directory that resolves it",
    });
  }

  const original = await readFile(target);
  let opened;
  try {
    opened = await engine.keep.openKept(original);
  } catch (e) {
    fail("could not read the workbook: " + e.message);
  }
  const book = opened.book, cached = opened.cached, issues = opened.issues;

  const startedAt = performance.now();
  const result = engine.compute(book, { cached: cached });
  const counted = countAnswers(book, result);

  let written;
  try {
    // values: "preserve" so a formula the engine cannot answer leaves the rest of the
    // workbook recalculated; `missing` below reports which cells stayed blank.
    written = await engine.keep.writeKept(original, { book: book, result: result }, {
      writeValues: true,
      values: "preserve",
    });
  } catch (e) {
    fail("could not write the recalculated workbook: " + e.message, {
      kind: e.constructor && e.constructor.name,
      code: e.code,
    });
  }

  const temp = resolve(dirname(resolve(target)), ".recalc-xlcalc-" + process.pid + ".xlsx");
  try {
    await writeFile(temp, written.data);
    await rename(temp, resolve(target));
  } catch (e) {
    fail("could not replace " + target + ": " + e.message);
  }

  process.stdout.write(JSON.stringify({
    backend: "xlcalc",
    total_formulas: counted.formulas,
    values_written: counted.formulas - counted.missing.length,
    values_missing: counted.missing.length,
    missing_locations: counted.missing.slice(0, 100),
    missing_locations_truncated: Math.max(0, counted.missing.length - 100),
    engine_diagnostics: (result.diagnostics || []).length,
    unchanged: Buffer.compare(original, written.data) === 0,
    bytes_in: original.length,
    bytes_out: written.data.length,
    compute_ms: Math.round(performance.now() - startedAt),
    issues: (issues || []).concat(written.issues || []),
  }) + "\n");
}

main().catch((e) => fail("unexpected failure: " + (e.stack || e.message)));
