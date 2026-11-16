---
name: xlcalc-xlsx
description: Create, edit, recalculate and verify Excel workbooks (.xlsx, .xlsm) with the xlcalc formula engine — no LibreOffice, no Excel. Every file it writes carries calculated values, correct _xlfn. prefixes and dynamic-array spill metadata, and every run reports formula errors with their root cause, circular references, formulas Excel would show as #NAME?, and number formats that stop Excel from opening the file. Use this whenever a spreadsheet is the input or the output — financial models, reports, trackers, "make me an Excel with formulas", "add a column to this xlsx", "why does this sheet show #REF!", "recalculate this file openpyxl made", fixing or checking a workbook someone sent — even if the user never says "xlcalc".
compatibility: Node 20.19+; the xlcalc npm package (MIT), installed into scripts/. Python with openpyxl only for charts.
---

# Workbooks with xlcalc

xlcalc is an Excel formula engine checked case by case against real Excel. Here it does all three jobs that usually need three tools: it writes the file, computes every formula, and tells you what Excel would show differently.

Everything goes through one script. Paths below are relative to this skill's directory.

```bash
npm install --prefix scripts            # once, if scripts/node_modules is missing
node scripts/xl.mjs build  spec.mjs out.xlsx        # a new workbook
node scripts/xl.mjs edit   file.xlsx ops.json        # change one, keeping charts, pictures, pivots, macros
node scripts/xl.mjs recalc file.xlsx                 # store values in a file another tool wrote
node scripts/xl.mjs check  file.xlsx                 # report only, writes nothing
node scripts/xl.mjs show   file.xlsx --formulas      # read cells: displayed text and formulas
```

`--out other.xlsx` writes `edit`/`recalc` elsewhere; `--clock 2026-01-31T00:00:00Z` pins `TODAY()`/`NOW()`/`RAND()`.

## Read the report, every time

`build`, `edit`, `recalc` and `check` print one JSON report. **`status: "clean"` is the only success.** Exit codes: 0 clean, 2 written but with problems, 1 failed and nothing was written (JSON with `error`), 3 xlcalc missing.

`problems` are things Excel will show or do differently from what you intended — fix each, then run again:

| kind | meaning | usual fix |
|---|---|---|
| `error` | the cell where an error *starts*, with `reason` (`division by zero`, `value not found`…) and how many cells it poisons (`dependents`) | fix the origin only; dependents clear themselves |
| `cycle` | circular reference: the cells are not calculated | break the loop, or set `iteration: {}` on the workbook if it is meant |
| `noPrefix` | a newer function (XLOOKUP, FILTER…) stored without `_xlfn.` — another tool wrote it; Excel shows `#NAME?` | see "Files from openpyxl" |
| `numberFormat` | a format code Excel refuses to open the file over (`0 kg`) | quote the text: `0 "kg"` |
| `notCalculated` | a function the engine does not know; the value stored in the file is kept | rewrite with known functions, or accept and say so |
| `name` | a defined name that is invalid or returns an error | fix its `ref` |
| `userFunction`, `formula`, `externalLink`, `part` | macro functions, unparsable formulas, links without stored values, damage | report to the user |

`notes` are informational: parts xlcalc keeps byte-for-byte but does not model (`drawing`, `print`, `macros`…), `dataTable` (what-if tables keep stored values; Excel recalculates them on open), `externalBooks` (links computed from the values cached in the file — that is correct and the links survive), and from `check` only, `staleValues` (cached values that differ from a fresh calculation: the file was saved before inputs changed, or a real engine difference worth a look).

A clean report proves formulas *evaluate*, not that they are *right*. After building, `show` the key outputs and sanity-check a couple of numbers by hand.

## Creating a workbook: `build`

Write a spec — a BookInput object — as `.json`, or as `.mjs` whose default export is the object or a function returning it (use `.mjs` for anything generated from data or loops). Full field reference: [references/spec.md](references/spec.md).

```js
// spec.mjs
const rows = [['North', 120], ['South', 80], ['North', 45]]
const cells = { A1: { value: 'Region', style: 0 }, B1: { value: 'Amount', style: 0 } }
rows.forEach(([r, a], i) => { cells[`A${i + 2}`] = { value: r }; cells[`B${i + 2}`] = { value: a, numberFormat: '#,##0' } })
cells.D1 = { value: 'Region', style: 0 }; cells.E1 = { value: 'Total', style: 0 }
cells.D2 = { formula: 'SORT(UNIQUE(A2:A4))' }
cells.E2 = { formula: 'SUMIFS(B:B,A:A,D2#)', numberFormat: '#,##0' }
export default {
  styles: [{ font: { bold: true }, fill: { color: '#DDEBF7' } }],
  sheets: [{ name: 'Sales', cells, columns: { A: { width: 14 }, D: { width: 14 } }, frozen: { rows: 1 } }],
}
```

Things that differ from openpyxl habits, on purpose:

- **Formulas are written without `=`** (a leading one is tolerated) and with plain function names. The writer adds `_xlfn.` itself, so **XLOOKUP, XMATCH, FILTER, SORT, UNIQUE, SEQUENCE, LET, LAMBDA, TEXTJOIN, IFS work** and spill properly (`D2#` refers to a spill). Do not add prefixes yourself.
- Data goes in `value`, formulas in `formula`; text from data never turns into a formula. Dates: `{ value: { date: '2026-01-31' } }` plus a date `numberFormat`.
- Styles are a workbook-level list; cells, rows and columns point at them by index (`style: 0`).
- Keep inputs in cells and reference them (`=B2*(1+$B$1)`), rather than hardcoding numbers computed in your head — the point of a workbook is that it recalculates.
- Charts: xlcalc does not create them. See "Charts".

## Changing a workbook: `edit`

`edit` opens the original file, applies operations, recomputes, and writes only what changed over the original — charts, pictures, pivot tables, slicers, macros, themes, print settings stay as they were, and references in them follow inserted/deleted rows. Ops are a JSON array (or an `.mjs` exporting the array, or a function `(session, xlcalc) => { … }` for full access to the xlcalc session API). Full list: [references/ops.md](references/ops.md).

```json
[
  { "op": "setCells", "edits": [
    { "sheet": "Sales", "cell": "B5", "input": { "value": 99 } },
    { "sheet": "Sales", "cell": "C2", "input": { "formula": "B2*1.2" } } ] },
  { "op": "insertRows", "sheet": "Sales", "row": 3, "count": 2 },
  { "op": "patchCells", "patches": [ { "sheet": "Sales", "range": "B2:B9", "set": { "numberFormat": "#,##0.00" } } ] },
  { "op": "setCellText", "sheet": "Sales", "cell": "A10", "text": "15/03/2026" }
]
```

Operations apply in order. If one is refused (deleting the last sheet, splitting a merged area, cutting a table…) or `writeKept` cannot keep the file consistent, nothing is written and the `error` says why.

Before editing an unfamiliar file, look at it: `show file.xlsx --formulas` (add `--sheet`, `--range` for big ones), and `check` it so you know which problems were already there.

## Files from openpyxl or other tools: `recalc`

openpyxl saves formulas with no values, so pandas, `data_only=True` and previewers read `None`. `recalc` computes and stores them (charts and everything else kept; file permissions kept; a second run changes nothing).

Two traps `recalc` will report but cannot fix:

- **`noPrefix`**: openpyxl writes formulas verbatim, so `=XLOOKUP(...)` lands in the file without `_xlfn.` and Excel shows `#NAME?`. Re-entering the same text through `edit` does not change the file. Fix at the source: create those formulas with xlcalc (`build`/`edit`), or in openpyxl write `=_xlfn.XLOOKUP(...)` (`=_xlfn._xlws.FILTER(...)`, `=_xlfn._xlws.SORT(...)`).
- **Spills lost**: openpyxl drops dynamic-array metadata from files it re-saves, so an existing UNIQUE/FILTER becomes a fixed-size legacy array. Prefer not to round-trip xlcalc-built files through openpyxl; when you must (charts), do it in the order below.

## Charts

xlcalc keeps charts but does not draw new ones. Use openpyxl for the chart **first**, then let xlcalc fill the data:

1. openpyxl: create the sheet(s) with headers and the chart pointing at the ranges the data will occupy; save.
2. `edit` that file with ops that write the data and formulas (`setCells`). The chart is kept, spill formulas get proper metadata, values are stored.

The reverse order (xlcalc build → openpyxl adds chart → `recalc`) also works for workbooks without spilling formulas.

## When things go wrong

- `xlcalc is not installed` / too old → `npm install --prefix scripts`.
- `invalid workbook: …` from `build` → the spec breaks a rule (sheet name over 31 chars or with `/ \ ? * [ ] :`, overlapping merges or tables, a style index out of range); the message names it.
- `.xls`, `.xlsb`, password-protected files are refused by the reader; convert first or tell the user.
- xlcalc documentation for anything beyond this skill: `scripts/node_modules/xlcalc/docs/` (`xlsx.md`, `edits.md`, `structure.md`, `formulas.md`, `limitations.md`).
