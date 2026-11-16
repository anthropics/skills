# Edit operations

`edit` takes a JSON array applied in order. Cell addresses are A1 without `$` or sheet; sheets by name. Authoritative types: `scripts/node_modules/xlcalc/docs/api.md` (`SessionOperation`, `StructureOp`, `LayoutEdit`, `CellPatch`).

## Cells

```json
{ "op": "setCells", "edits": [ { "sheet": "S", "cell": "B2", "input": { "value": 5 } },
                               { "sheet": "S", "cell": "C2", "input": { "formula": "B2*2", "numberFormat": "0.00" } },
                               { "sheet": "S", "cell": "D2", "input": null } ] }
```
Given fields replace the cell's, `null` removes a field, omitted fields stay (a value typed over keeps the formatting). `input: null` clears content like the Delete key.

```json
{ "op": "replaceCells", "edits": [ { "sheet": "S", "cell": "B2", "input": { "value": 1 } } ] }
{ "op": "clearCells", "ranges": [ { "sheet": "S", "range": "A10:F20" } ], "what": "contents" }
```
`what`: `contents`, `formats`, `all`.

Typed text, parsed as Excel parses keyboard input in the workbook's locale (dates, `12%`, `1,250.5`, `=formula` with `=`):
```json
{ "op": "setCellText", "sheet": "S", "cell": "A1", "text": "3/15/2026" }
{ "op": "setCellTexts", "entries": [ { "sheet": "S", "cell": "A2", "text": "=A1+7" } ] }
{ "op": "fillCellText", "sheet": "S", "range": "C2:C50", "text": "=A2*B2" }
{ "op": "pasteText", "sheet": "S", "cell": "A1", "text": "a\tb\r\n1\t2\r\n" }
```
`fillCellText` adjusts relative references per row, like Ctrl+Enter over a selection.

## Formatting

```json
{ "op": "patchCells", "patches": [ { "sheet": "S", "range": "A1:F1",
  "set": { "style": { "font": { "bold": true }, "fill": { "color": "#DDEBF7" } }, "numberFormat": "#,##0" } } ] }
```
`style` given by fields is merged over each cell's current style; `null` removes a field. Ranges may be `B:D` or `2:5`.

## Layout

```json
{ "op": "setLayout", "edits": [
  { "sheet": "S", "columns": "A:C", "set": { "width": 16 } },
  { "sheet": "S", "columns": "D", "fit": true },
  { "sheet": "S", "rows": "1", "set": { "height": 30 } },
  { "sheet": "S", "frozen": { "rows": 1 } },
  { "sheet": "S", "merges": ["A1:F1"] },
  { "sheet": "S", "tabColor": "#00B050" },
  { "sheet": "S", "conditionalFormats": [ ] },
  { "sheet": "S", "validations": [ ] },
  { "sheet": "S", "autoFilter": { "range": "A1:F100" } } ] }
```
`merges`, `conditionalFormats`, `validations` replace the sheet's whole list — read the current one with `show --json` or a function op first.

## Names and styles

```json
{ "op": "setNames", "names": [ { "name": "TaxRate", "ref": "'Inputs'!$B$2" } ] }
```
Replaces all names. A file opened by `edit` carries hidden names starting `_xlcalc.keep.` — keep them; use a function op (`session.getBook().names`) to add to the list rather than replace it.

## Structure

```json
{ "op": "insertRows", "sheet": "S", "row": 5, "count": 2 }
{ "op": "deleteRows", "sheet": "S", "row": 5 }
{ "op": "insertColumns", "sheet": "S", "column": "C" }
{ "op": "deleteColumns", "sheet": "S", "column": "C", "count": 3 }
{ "op": "moveRange", "from": { "sheet": "S", "range": "A1:B5" }, "to": { "sheet": "S", "cell": "D1" } }
{ "op": "copyRange", "from": { "sheet": "S", "range": "C2" }, "to": { "sheet": "S", "range": "C3:C50" } }
{ "op": "fillRange", "sheet": "S", "range": "A2:A3", "to": "A2:A20" }
{ "op": "insertSheet", "name": "Summary", "before": "S" }
{ "op": "renameSheet", "sheet": "S", "name": "Sales" }
{ "op": "deleteSheet", "sheet": "Old" }
{ "op": "moveSheet", "sheet": "Summary" }
{ "op": "hideSheet", "sheet": "Lists" }
{ "op": "mergeCells", "sheet": "S", "range": "A1:F1", "center": true }
{ "op": "addTable", "sheet": "S", "table": { "name": "Sales", "range": "A1:D10", "columns": [ { "name": "Region" }, { "name": "Qty" }, { "name": "Price" }, { "name": "Amount" } ] } }
{ "op": "group", "sheet": "S", "rows": "5:9" }
```
Formulas, names, tables, charts, pivot sources and print areas follow these like Excel. `copyRange` adjusts relative references (fill down = copy one row over many).

## Function ops

For anything conditional on the file's contents, export a function from `ops.mjs`; it receives the xlcalc session and the xlcalc module, and whatever it changes is written:

```js
export default (s) => {
  const last = s.getUsedRange('Data').rows
  s.setCells([{ sheet: 'Data', cell: `B${last + 1}`, input: { formula: `SUM(B2:B${last})` } }])
  const names = s.getBook().names || []
  s.setNames([...names, { name: 'Total', ref: `'Data'!$B$${last + 1}` }])
}
```

Useful reads: `s.getCell(sheet, 'B2')` (value, text, formula), `s.getCells(sheet, 'A1:F20')`, `s.getValues(sheet, range)`, `s.explain(sheet, cell).text` (where a number comes from), `s.getCellIssue(sheet, cell)`, `s.findCells([{ sheet, range: 'A:Z' }], 'Total')`.
