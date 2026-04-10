---
name: odt
description: "Use this skill whenever the user wants to create, fill, read, or convert OpenDocument Format files (.odt, .ods). Triggers include: any mention of 'ODT', 'ODS', 'ODF', 'OpenDocument', 'LibreOffice document', or requests to produce documents in open-source or ISO standard formats. Also use when converting HTML, Markdown, or TipTap/ProseMirror JSON to ODT, filling ODT templates with data, reading or extracting content from ODT files, generating ODS spreadsheets, or creating formal documents like resolutions, reports, letters, contracts, invoices, or memos as .odt files. Use this skill instead of the docx skill when the user explicitly requests .odt output or mentions LibreOffice/OpenOffice as their target application. Do NOT use for .docx files (use the docx skill), PDFs, presentations, or general coding tasks unrelated to document generation."
license: Apache-2.0
---

# ODT and ODS — OpenDocument Format

## Overview

OpenDocument Format (ODF) is the ISO standard (ISO/IEC 26300) for documents. `.odt` is the text document format, `.ods` is the spreadsheet format. Both are the native formats for LibreOffice and are mandatory for many governments and public sector organisations.

**odf-kit** is the JavaScript/TypeScript library for working with ODF files. It covers eight capability modes:

| Mode | Function | Description |
|------|----------|-------------|
| Build ODT | `OdtDocument` | Generate text documents from scratch |
| Convert HTML → ODT | `htmlToOdt()` | Convert HTML strings to ODT |
| Convert Markdown → ODT | `markdownToOdt()` | Convert Markdown to ODT |
| Convert TipTap → ODT | `tiptapToOdt()` | Convert TipTap/ProseMirror JSON to ODT |
| Fill template | `fillTemplate()` | Fill existing .odt templates with data |
| Read ODT | `readOdt()` / `odtToHtml()` | Parse .odt files to model or HTML |
| Build ODS | `OdsDocument` | Generate spreadsheets from scratch |
| Convert ODT → Typst | `odtToTypst()` | Convert ODT to Typst for PDF generation |

### Installation

```bash
npm install odf-kit
```

Node.js 22+ required. ESM only.

```javascript
import { OdtDocument, htmlToOdt, markdownToOdt, tiptapToOdt, fillTemplate } from "odf-kit";
import { OdsDocument } from "odf-kit/ods";
import { readOdt, odtToHtml } from "odf-kit/reader";
import { odtToTypst } from "odf-kit/typst";
import { writeFileSync, readFileSync } from "fs";
```

---

## Build: ODT Documents

### Basic document

```javascript
import { OdtDocument } from "odf-kit";
import { writeFileSync } from "fs";

const doc = new OdtDocument();
doc.setMetadata({ title: "Report", creator: "Alice" });
doc.addHeading("Quarterly Report", 1);
doc.addParagraph("Revenue exceeded expectations.");
doc.addTable([
  ["Division", "Q4 Revenue", "Growth"],
  ["North", "$2.1M", "+12%"],
  ["South", "$1.8M", "+8%"],
]);
const bytes = await doc.save();
writeFileSync("report.odt", bytes);
```

### Page layout

```javascript
// A4 portrait (default for Europe)
doc.setPageLayout({ marginTop: "2.5cm", marginBottom: "2.5cm" });

// US Letter
doc.setPageLayout({ width: "8.5in", height: "11in", marginTop: "1in", marginBottom: "1in" });

// Landscape
doc.setPageLayout({ orientation: "landscape" });
```

**Page format presets via `htmlToOdt`/`markdownToOdt`/`tiptapToOdt`:**
`"A4"` (default), `"letter"`, `"legal"`, `"A3"`, `"A5"`

### Headers and footers

```javascript
doc.setHeader("Confidential — Page ###");  // ### = page number
doc.setFooter("© 2026 Acme Corp");

// Formatted
doc.setHeader((h) => {
  h.addText("Report", { bold: true });
  h.addText(" — Page ");
  h.addPageNumber();
});
```

### Text formatting

```javascript
doc.addParagraph((p) => {
  p.addText("Bold", { bold: true });
  p.addText(", italic", { italic: true });
  p.addText(", colored", { color: "#FF0000", fontSize: 14 });
  p.addText(", underlined", { underline: true });
  p.addText(", highlighted", { highlightColor: "yellow" });
});

// Superscript/subscript
doc.addParagraph((p) => {
  p.addText("H");
  p.addText("2", { subscript: true });
  p.addText("O and E = mc");
  p.addText("2", { superscript: true });
});
```

### Tables

```javascript
// Simple
doc.addTable([["Name", "Age"], ["Alice", "30"], ["Bob", "25"]]);

// With widths and borders
doc.addTable([["Item", "Price"], ["Widget", "$9.99"]], {
  columnWidths: ["8cm", "4cm"],
  border: "0.5pt solid #000000",
});

// Full control
doc.addTable((t) => {
  t.addRow((r) => {
    r.addCell("Header", { bold: true, backgroundColor: "#DDDDDD" });
    r.addCell("Value",  { bold: true, backgroundColor: "#DDDDDD" });
  });
  t.addRow((r) => {
    r.addCell("Status");
    r.addCell("Complete", { color: "green" });
  });
}, { columnWidths: ["8cm", "4cm"] });
```

### Lists

```javascript
doc.addList(["Apples", "Bananas", "Cherries"]);
doc.addList(["First", "Second", "Third"], { type: "numbered" });

// Nested
doc.addList((l) => {
  l.addItem((p) => { p.addText("Important: ", { bold: true }); p.addText("read the docs"); });
  l.addItem("Main topic");
  l.addNested((sub) => { sub.addItem("Subtopic A"); sub.addItem("Subtopic B"); });
});
```

### Images

```javascript
import { readFile } from "fs/promises";
const logo = await readFile("logo.png");

doc.addImage(logo, { width: "10cm", height: "6cm", mimeType: "image/png" });

// Inline
doc.addParagraph((p) => {
  p.addText("Logo: ");
  p.addImage(logo, { width: "2cm", height: "1cm", mimeType: "image/png" });
});
```

### Links and bookmarks

```javascript
doc.addParagraph((p) => {
  p.addBookmark("intro");
  p.addText("Introduction");
});
doc.addParagraph((p) => {
  p.addLink("our website", "https://example.com", { bold: true });
  p.addText(" or go back to the ");
  p.addLink("intro", "#intro");
});
```

### Method chaining

```javascript
const bytes = await new OdtDocument()
  .setMetadata({ title: "Report" })
  .setPageLayout({ orientation: "landscape" })
  .setHeader("Confidential")
  .setFooter("Page ###")
  .addHeading("Summary", 1)
  .addParagraph("All systems operational.")
  .addTable([["System", "Status"], ["API", "OK"]])
  .save();
```

---

## Convert: HTML → ODT

```javascript
import { htmlToOdt } from "odf-kit";

const html = `
  <h1>Meeting Notes</h1>
  <p>Attendees: <strong>Alice</strong>, Bob</p>
  <ul><li>Project status</li><li>Budget review</li></ul>
`;

const bytes = await htmlToOdt(html);                               // A4 default
const bytes2 = await htmlToOdt(html, { pageFormat: "letter" });   // US Letter
const bytes3 = await htmlToOdt(html, {
  pageFormat: "A4",
  orientation: "landscape",
  marginTop: "1.5cm",
  metadata: { title: "Meeting Notes", creator: "Alice" },
});
writeFileSync("notes.odt", bytes);
```

Supported: `h1`–`h6`, `p`, `ul`, `ol`, `li` (nested), `table`/`tr`/`td`/`th`, `blockquote`, `pre`, `hr`, `strong`, `em`, `u`, `s`, `sup`, `sub`, `a`, `code`, `mark`, `span` (inline CSS), `br`.

---

## Convert: Markdown → ODT

```javascript
import { markdownToOdt } from "odf-kit";

const markdown = `# Report\n\n**Date:** 2026-04-10\n\n## Items\n\n- First\n- Second`;
const bytes = await markdownToOdt(markdown, { pageFormat: "A4" });
writeFileSync("report.odt", bytes);
```

Accepts all `htmlToOdt` options. Supports full CommonMark: headings, bold, italic, lists, tables, links, code blocks, blockquotes, horizontal rules.

---

## Convert: TipTap/ProseMirror JSON → ODT

For TipTap-based editors (dDocs, Outline, Novel, BlockNote etc.). No dependency on `@tiptap/core` — walks JSON as plain object. **Conversion runs entirely locally — no document content sent to external services.**

```javascript
import { tiptapToOdt } from "odf-kit";

// Basic
const bytes = await tiptapToOdt(editor.getJSON(), { pageFormat: "A4" });

// With pre-fetched images (e.g. from IPFS or S3)
const images = { [imageUrl]: imageBytes };
const bytes2 = await tiptapToOdt(editor.getJSON(), { images });

// Custom node handler for app-specific extensions
const bytes3 = await tiptapToOdt(editor.getJSON(), {
  unknownNodeHandler: (node, doc) => {
    if (node.type === "callout") doc.addParagraph(`⚠️ ${node.content?.[0]?.content?.[0]?.text}`);
  },
});
writeFileSync("document.odt", bytes);
```

Supported nodes: `paragraph`, `heading` (1–6), `bulletList`, `orderedList`, `listItem` (nested), `blockquote`, `codeBlock`, `horizontalRule`, `hardBreak`, `image`, `table`, `tableRow`, `tableCell`, `tableHeader`.
Supported marks: `bold`, `italic`, `underline`, `strike`, `code`, `link`, `textStyle`, `highlight`, `superscript`, `subscript`.

---

## Fill: ODT Templates

Create a `.odt` template in LibreOffice with `{placeholder}` syntax, then fill it programmatically.

```javascript
import { fillTemplate } from "odf-kit";
import { readFileSync, writeFileSync } from "fs";

const template = readFileSync("invoice-template.odt");
const result = fillTemplate(template, {
  customer: "Acme Corp",
  date: "2026-04-10",
  items: [
    { product: "Widget", qty: 5, price: "$125" },
    { product: "Gadget", qty: 3, price: "$120" },
  ],
  showNotes: true,
  notes: "Net 30",
});
writeFileSync("invoice.odt", result);
```

| Syntax | Description |
|--------|-------------|
| `{tag}` | Simple replacement |
| `{object.property}` | Dot notation |
| `{#tag}...{/tag}` | Loop (array) or conditional (truthy/falsy) |

`fillTemplate` is **synchronous** — no `await` needed. Automatically heals placeholders fragmented by LibreOffice editing.

---

## Read: ODT Files

```javascript
import { readOdt, odtToHtml } from "odf-kit/reader";
import { readFileSync } from "fs";

const bytes = readFileSync("report.odt");

// Structured model
const model = readOdt(bytes);
console.log(model.body);        // BodyNode[]
console.log(model.pageLayout);  // PageLayout

// HTML string
const html = odtToHtml(bytes);

// Tracked changes
const final    = odtToHtml(bytes, {}, { trackedChanges: "final" });
const original = odtToHtml(bytes, {}, { trackedChanges: "original" });
const marked   = odtToHtml(bytes, {}, { trackedChanges: "changes" });
```

---

## Build: ODS Spreadsheets

```javascript
import { OdsDocument } from "odf-kit/ods";
import { writeFileSync } from "fs";

const doc = new OdsDocument();
doc.setMetadata({ title: "Sales Report" });

const sheet = doc.addSheet("Q1");
sheet.setTabColor("#4CAF50");

// Header row
sheet.addRow(["Month", "Revenue", "Growth"], { bold: true, backgroundColor: "#DDDDDD" });

// Data rows
sheet.addRow(["January", 12500, 0.08]);
sheet.addRow(["February", 14200, 0.136]);

// Formula
sheet.addRow(["Total", { value: "=SUM(B2:B3)", type: "formula" }]);

// Number formats
sheet.addRow([{ value: 1234567, type: "float", numberFormat: "integer" }]);         // 1,234,567
sheet.addRow([{ value: 0.1234, type: "percentage", numberFormat: "percentage:1" }]);// 12.3%
sheet.addRow([{ value: 9999.99, type: "currency", numberFormat: "currency:EUR" }]); // €9,999.99

// Merged cell
sheet.addRow([{ value: "Q1 Summary", type: "string", colSpan: 3, bold: true }]);

// Freeze header row
sheet.freezeRows(1);

// Column widths
sheet.setColumnWidth(0, "4cm");
sheet.setColumnWidth(1, "5cm");

const bytes = await doc.save();
writeFileSync("sales.ods", bytes);
```

### Cell types

| JavaScript type | ODS type | Example |
|-----------------|----------|---------|
| `number` | float | `42`, `1234.56` |
| `Date` | date | `new Date("2026-01-15")` |
| `boolean` | boolean | `true`, `false` |
| `string` | string | `"Hello"` |
| `null` / `undefined` | empty | — |
| `{ value, type: "formula" }` | formula | `{ value: "=SUM(A1:A10)", type: "formula" }` |
| `{ value, type: "percentage" }` | percentage | `{ value: 0.1234, type: "percentage" }` |
| `{ value, type: "currency" }` | currency | `{ value: 99.99, type: "currency" }` |

### Number formats

```javascript
{ value: 9999, type: "float", numberFormat: "integer" }          // 9,999
{ value: 1234.567, type: "float", numberFormat: "decimal:2" }    // 1,234.57
{ value: 0.1234, type: "percentage", numberFormat: "percentage" }// 12.34%
{ value: 0.075, type: "percentage", numberFormat: "percentage:1"}// 7.5%
{ value: 1234.56, type: "currency", numberFormat: "currency:EUR"}// €1,234.56
{ value: 99.99, type: "currency", numberFormat: "currency:USD:0"}// $100
```

### Merged cells

```javascript
sheet.addRow([{ value: "Q1 Report", type: "string", colSpan: 3, bold: true }]);
sheet.addRow([{ value: "Region", type: "string", rowSpan: 2 }, "Jan", "Feb"]);
```

### Hyperlinks in cells

```javascript
sheet.addRow([{ value: "odf-kit", type: "string", href: "https://github.com/GitHubNewbie0/odf-kit" }]);
```

### Date formatting

```javascript
doc.setDateFormat("DD/MM/YYYY");  // document default
sheet.addRow([{ value: new Date("2026-12-25"), type: "date", dateFormat: "MM/DD/YYYY" }]);
```

---

## Convert: ODT → Typst → PDF

```javascript
import { odtToTypst } from "odf-kit/typst";
import { execSync } from "child_process";
import { readFileSync, writeFileSync } from "fs";

const typst = odtToTypst(readFileSync("letter.odt"));
writeFileSync("letter.typ", typst);
execSync("typst compile letter.typ letter.pdf");
```

---

## Critical Rules

- **Always `await doc.save()`** — returns `Promise<Uint8Array>`
- **`fillTemplate()` is synchronous** — no await
- **ESM only** — use `import`, not `require`; `"type": "module"` in package.json
- **Write with `writeFileSync`** — `writeFileSync("out.odt", bytes)`
- **`fontSize` as number = points** — `14` means `14pt`
- **Images require `width`, `height`, and `mimeType`** — all three required
- **`###` in header/footer** = page number placeholder
- **A4 is the default page size** — use `pageFormat: "letter"` for US
- **Formula cells require explicit type** — `{ value: "=SUM(...)", type: "formula" }`

---

## Complete Example — Invoice

```javascript
import { OdtDocument } from "odf-kit";
import { writeFileSync } from "fs";

async function createInvoice() {
  const doc = new OdtDocument();

  doc.setMetadata({ title: "Invoice #1042", creator: "Acme Corp" });
  doc.setPageLayout({ width: "8.5in", height: "11in", marginTop: "1in", marginBottom: "1in", marginLeft: "1in", marginRight: "1in" });
  doc.setHeader("Acme Corp — Invoice");
  doc.setFooter("Page ###");

  doc.addHeading("Invoice #1042", 1);
  doc.addParagraph((p) => {
    p.addText("Date: ", { bold: true });
    p.addText("April 10, 2026");
  });
  doc.addParagraph((p) => {
    p.addText("Bill to: ", { bold: true });
    p.addText("Globex Corporation");
  });

  doc.addHeading("Items", 2);
  doc.addTable((t) => {
    t.addRow((r) => {
      r.addCell("Description", { bold: true, backgroundColor: "#DDDDDD" });
      r.addCell("Qty",         { bold: true, backgroundColor: "#DDDDDD" });
      r.addCell("Unit Price",  { bold: true, backgroundColor: "#DDDDDD" });
      r.addCell("Total",       { bold: true, backgroundColor: "#DDDDDD" });
    });
    t.addRow((r) => { r.addCell("Widget Pro"); r.addCell("5"); r.addCell("$125.00"); r.addCell("$625.00"); });
    t.addRow((r) => { r.addCell("Gadget Plus"); r.addCell("3"); r.addCell("$120.00"); r.addCell("$360.00"); });
  }, { columnWidths: ["8cm", "2cm", "3cm", "3cm"], border: "0.5pt solid #000000" });

  doc.addParagraph((p) => {
    p.addText("Total Due: ", { bold: true, fontSize: 14 });
    p.addText("$985.00", { bold: true, fontSize: 14, color: "#006600" });
  });

  writeFileSync("invoice-1042.odt", await doc.save());
}

createInvoice();
```
