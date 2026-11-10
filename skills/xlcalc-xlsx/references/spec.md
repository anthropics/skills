# Spec reference (BookInput)

The shapes xlcalc accepts, trimmed to what workbooks usually need. Authoritative types: `scripts/node_modules/xlcalc/docs/api.md` (search for `### \`SheetInput\`` etc.).

## Workbook

```js
{
  sheets: [ /* SheetInput, at least one visible */ ],
  styles: [ /* CellStyle; referenced by index */ ],
  names: [ { name: 'TaxRate', ref: "'Inputs'!$B$2" }, { name: 'Local', ref: "'S'!$A$1", scope: 'S' } ],
  locale: 'ru-RU',        // optional: calculates and displays as Russian Excel; formulas stay English with commas
  iteration: {},          // optional: allow intended circular references (maxIterations, maxChange)
  activeSheet: 'Summary', // optional
}
```

## Sheet

```js
{
  name: 'Sales',                       // ≤31 chars, none of : \ / ? * [ ]
  cells: { A1: CellInput, ... },
  columns: { A: { width: 14 }, 'B:D': { width: 12, numberFormat: '#,##0' }, F: { hidden: true } },
  rows: { 1: { height: 24, style: 0 }, '5:9': { outlineLevel: 1 } },
  looks: [ { range: 'A1:H1', style: 0 } ],   // formatting for many empty cells without an entry each
  merges: ['A1:D1'],
  frozen: { rows: 1, columns: 1 },
  tables: [ /* TableInput */ ],
  conditionalFormats: [ /* rules, highest priority first */ ],
  validations: [ /* DataValidation */ ],
  autoFilter: { range: 'A1:F100' },
  tabColor: '#FFC000',
  hidden: true,                        // or 'very'
}
```

Width is in characters of the default font's digit (Excel's number), height in points.

## Cell

```js
{ value: 42 }                        // number, string, boolean, null
{ value: { date: '2026-01-31' }, numberFormat: 'dd.mm.yyyy' }
{ formula: 'SUM(B2:B9)' }            // no '=', English names, ',' separators, '.' decimals
{ formula: 'B2*TaxRate', numberFormat: '0.0%', style: 1 }
{ formula: 'TRANSPOSE(A1:A3)', array: 'C1:E1' }    // legacy Ctrl+Shift+Enter array, only if asked
{ value: 'see note', note: { text: 'Source: 10-K', author: 'Analyst' } }
{ value: 'docs', link: { url: 'https://example.com' } }     // or { location: "'Data'!A1" }
{ value: 'Bold plain', richText: [ { start: 0, font: { bold: true } }, { start: 4 } ] }   // a run lasts until the next; font is whole, not a patch
```

Errors as values: a formula like `NA()`; never put `'#N/A'` strings in cells.

## Style

```js
{
  font: { name: 'Arial', size: 10, bold: true, italic: true, underline: 'single', strike: true, color: '#0000FF' },
  fill: { color: '#FFF2CC' },                       // solid fills only
  border: { top: { style: 'thin', color: '#999999' }, bottom: { style: 'double' } },
  alignment: { horizontal: 'center', vertical: 'top', wrap: true, indent: 1, rotation: 90 },
  protection: { locked: false },
}
```

Number formats are Excel codes on the cell/row/column (`numberFormat`), not part of the style: `'#,##0'`, `'#,##0.00;[Red]-#,##0.00'`, `'0.0%'`, `'$#,##0;($#,##0);"-"'`, `'dd.mm.yyyy'`, `'0 "kg"'`. Literal words must be quoted — unquoted letters (`0 kg`) make Excel refuse the whole file, and `build` refuses to write them.

Financial-model convention, if the user has none: inputs blue font (`#0000FF`), formulas black, links to other sheets green (`#008000`); negatives in parentheses; years as text or a `0` format so they do not show `2,026`.

## Table

```js
{
  name: 'Sales',                     // unique among tables and names
  range: 'A1:D10',                   // header row included
  columns: [ { name: 'Region' }, { name: 'Qty' }, { name: 'Price' },
             { name: 'Amount', formula: 'Sales[[#This Row],[Qty]]*Sales[[#This Row],[Price]]' } ],
  totals: true,                      // last row of range is the totals row
  style: { name: 'TableStyleMedium2', rowStripes: true },
}
```

Header cells must hold the column names; calculated-column cells still need their own `formula` in `cells` (`[@Qty]*[@Price]` is accepted). Structured references work everywhere: `SUM(Sales[Amount])`.

## Conditional formats

```js
{ type: 'cellIs', ranges: ['B2:B20'], operator: 'lessThan', formulas: ['0'], style: { font: { color: '#9C0006' }, fill: { color: '#FFC7CE' } } }
{ type: 'expression', ranges: ['A2:F20'], formula: '$F2="Late"', style: { fill: { color: '#FCE4D6' } } }
{ type: 'containsText', ranges: ['C2:C20'], text: 'error', style: { font: { bold: true } } }
{ type: 'colorScale', ranges: ['D2:D20'], points: [ { value: { type: 'min' }, color: '#F8696B' }, { value: { type: 'max' }, color: '#63BE7B' } ] }
{ type: 'dataBar', ranges: ['E2:E20'], min: { type: 'min' }, max: { type: 'max' }, color: '#638EC6' }
```

Formulas are relative to the first cell of the first range.

## Data validation

```js
{ range: 'C2:C100', type: 'list', formula1: '"Open,Closed,Blocked"' }
{ range: 'D2:D100', type: 'list', formula1: "'Lists'!$A$1:$A$20" }
{ range: 'E2:E100', type: 'whole', operator: 'between', formula1: '1', formula2: '10', error: '1 to 10' }
{ range: 'F2:F100', type: 'date', operator: 'greaterThan', formula1: 'DATE(2026,1,1)' }
```
