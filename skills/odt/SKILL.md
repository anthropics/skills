---
name: odt
description: "Use this skill whenever the user wants to create, fill, read, or convert OpenDocument Format files (.odt, .ods). Triggers include: any mention of 'ODT', 'ODS', 'ODF', 'OpenDocument', 'LibreOffice document', or requests to produce documents in open-source or ISO standard formats. Also use when converting HTML, Markdown, or TipTap/ProseMirror JSON to ODT, filling ODT templates with data, reading or extracting content from ODT files, generating ODS spreadsheets, reading ODS files, converting XLSX to ODS, converting DOCX to ODT, or creating formal documents like resolutions, reports, letters, contracts, invoices, or memos as .odt files. Use this skill instead of the docx skill when the user explicitly requests .odt output or mentions LibreOffice/OpenOffice as their target application. Do NOT use for .docx files (use the docx skill), PDFs, presentations, or general coding tasks unrelated to document generation."
license: Apache-2.0
---

# odf-kit — OpenDocument Format for JavaScript and TypeScript

## Overview

An `.odt` file is an OpenDocument Format text document — an ISO standard (ISO/IEC 26300) ZIP archive containing XML files. It is the native format for LibreOffice, Apache OpenOffice, Collabora, OnlyOffice, and is supported by Google Docs and Microsoft Office.

odf-kit is the only actively maintained JavaScript/TypeScript library for ODF generation. It produces spec-validated output (validated against the OASIS ODF Validator on every CI run). Works in Node.js 22+ and browsers. No LibreOffice dependency.

## Quick Reference

| Task | Import | Function |
|------|--------|----------|
| Create new ODT document | `"odf-kit"` | `new OdtDocument()` |
| Fill existing ODT template | `"odf-kit"` | `fillTemplate(bytes, data)` |
| HTML → ODT | `"odf-kit"` | `htmlToOdt(html, options?)` |
| Markdown → ODT | `"odf-kit"` | `markdownToOdt(markdown, options?)` |
| TipTap/ProseMirror JSON → ODT | `"odf-kit"` | `tiptapToOdt(json, options?)` |
| Build ODS spreadsheet | `"odf-kit"` | `new OdsDocument()` |
| Read ODT / convert to HTML | `"odf-kit/reader"` | `readOdt(bytes)` / `odtToHtml(bytes)` |
| Read ODS | `"odf-kit/ods-reader"` | `readOds(bytes)` / `odsToHtml(bytes)` |
| XLSX → ODS | `"odf-kit/xlsx"` | `xlsxToOds(bytes)` |
| DOCX → ODT | `"odf-kit/docx"` | `docxToOdt(bytes, options?)` |
| ODT → Typst / PDF | `"odf-kit/typst"` | `odtToTypst(bytes)` |

### Installation

```bash
npm install odf-kit
```

Requires Node.js 22 or later. ESM only.

---

## Creating New ODT Documents

Generate .odt files with JavaScript using odf-kit's builder API.

### Setup

```javascript
import { OdtDocument } from "odf-kit";
import { writeFileSync } from "fs";

const doc = new OdtDocument();
doc.addHeading("Document Title", 1);
doc.addParagraph("Body text goes here.");

const bytes = await doc.save();
writeFileSync("output.odt", bytes);
```

### Metadata

```javascript
doc.setMetadata({
  title: "Quarterly Report",
  creator: "Jane Doe",
  description: "Q4 2026 financial summary",
});
```

### Page Layout

```javascript
doc.setPageLayout({
  orientation: "landscape",       // or "portrait" (default)
  width: "21cm",                  // default A4
  height: "29.7cm",
  marginTop: "2cm",
  marginBottom: "2cm",
  marginLeft: "2cm",
  marginRight: "2cm",
});
```

**For US Letter:** Use `width: "8.5in"` and `height: "11in"`.

### Headers and Footers

```javascript
// Simple string (### = page number)
doc.setHeader("Confidential — Page ###");
doc.setFooter("© 2026 Acme Corp — Page ###");

// Builder for formatted headers
doc.setHeader((h) => {
  h.addText("Confidential", { bold: true, color: "gray" });
  h.addText(" — Page ");
  h.addPageNumber();
});
```

### Headings

```javascript
// Basic heading (levels 1–6)
doc.addHeading("Chapter Title", 1);
doc.addHeading("Section Title", 2);

// With paragraph options
doc.addHeading("Centered Title", 1, { align: "center" });
doc.addHeading("Title with Space", 1, { spaceBefore: "0.5cm", spaceAfter: "0.5cm" });
```

### Paragraphs

```javascript
// Plain text
doc.addParagraph("Simple paragraph.");

// With paragraph options
doc.addParagraph("Right-aligned text.", { align: "right" });

// Builder for mixed formatting
doc.addParagraph((p) => {
  p.addText("Normal and ");
  p.addText("bold", { bold: true });
  p.addText(" text.");
});

// Builder with paragraph options
doc.addParagraph((p) => {
  p.addText("Indented paragraph content.");
}, { indentLeft: "1cm", indentFirst: "0.5cm" });
```

**Paragraph options:**

| Option | Type | Example | Description |
|--------|------|---------|-------------|
| `align` | string | `"left"`, `"center"`, `"right"`, `"justify"` | Text alignment |
| `spaceBefore` | string | `"0.5cm"` | Space above paragraph |
| `spaceAfter` | string | `"0.5cm"` | Space below paragraph |
| `lineHeight` | number or string | `1.5` or `"150%"` | Line spacing (number = multiplier) |
| `indentLeft` | string | `"1cm"` | Left indent |
| `indentRight` | string | `"1cm"` | Right indent |
| `indentFirst` | string | `"0.5cm"` | First-line indent (positive) or hanging indent (negative) |
| `tabStops` | array | `[{ position: "6cm", type: "right" }]` | Tab stop positions |

### Text Formatting

```javascript
doc.addParagraph((p) => {
  p.addText("Bold", { bold: true });
  p.addText("Italic", { italic: true });
  p.addText("Underline", { underline: true });
  p.addText("Strikethrough", { strikethrough: true });
  p.addText("Super", { superscript: true });
  p.addText("Sub", { subscript: true });
  p.addText("Arial 14pt red", { fontFamily: "Arial", fontSize: 14, color: "#CC0000" });
  p.addText("Highlighted", { highlightColor: "#FFFF00" });
  p.addText("UPPERCASE", { textTransform: "uppercase" });
  p.addText("Small Caps", { smallCaps: true });
  p.addText("Weight 300", { fontWeight: 300 });   // numeric 100–900
  p.addText("Weight bold", { fontWeight: "bold" });
});
```

**All text formatting options:**

| Option | Type | Example |
|--------|------|---------|
| `bold` | boolean | `true` |
| `italic` | boolean | `true` |
| `underline` | boolean | `true` |
| `strikethrough` | boolean | `true` |
| `superscript` | boolean | `true` |
| `subscript` | boolean | `true` |
| `fontSize` | number or string | `14` or `"14pt"` |
| `fontFamily` | string | `"Arial"` |
| `fontWeight` | string or number | `"bold"`, `300`, `700` |
| `fontStyle` | string | `"normal"`, `"italic"` |
| `color` | string | `"#FF0000"` or `"red"` |
| `highlightColor` | string | `"#FFFF00"` or `"yellow"` |
| `textTransform` | string | `"uppercase"`, `"lowercase"`, `"capitalize"` |
| `smallCaps` | boolean | `true` |

### Tables

```javascript
// Simple — array of arrays
doc.addTable([
  ["Name", "Role", "Department"],
  ["Alice", "Engineer", "R&D"],
  ["Bob", "Designer", "UX"],
]);

// With options
doc.addTable([
  ["Item", "Price"],
  ["Widget", "$9.99"],
], { columnWidths: ["8cm", "4cm"], border: "0.5pt solid #000000" });

// Full control — builder callback
doc.addTable((t) => {
  t.addRow((r) => {
    r.addCell("Header", {
      bold: true,
      backgroundColor: "#DDDDDD",
      verticalAlign: "middle",
      padding: "0.15cm",
    });
    r.addCell("Value", {
      bold: true,
      backgroundColor: "#DDDDDD",
      colSpan: 2,
    });
  }, { backgroundColor: "#DDDDDD" });

  t.addRow((r) => {
    r.addCell("Status");
    r.addCell("Complete", { color: "green" });
    r.addCell("Verified", { border: "0.5pt solid #000000" });
  });

  // Row spanning
  t.addRow((r) => {
    r.addCell("Tall", { rowSpan: 2, verticalAlign: "top" });
    r.addCell("Normal");
  });
  t.addRow((r) => {
    r.addCell("Adjacent to rowspan");
  });
}, { columnWidths: ["4cm", "4cm", "4cm"] });
```

**Cell options** (extends all text formatting options, plus):

| Option | Type | Example |
|--------|------|---------|
| `backgroundColor` | string | `"#EEEEEE"` |
| `border` | string | `"0.5pt solid #000000"` |
| `borderTop` / `borderBottom` / `borderLeft` / `borderRight` | string | Per-side borders |
| `colSpan` | number | `2` |
| `rowSpan` | number | `3` |
| `verticalAlign` | string | `"top"`, `"middle"`, `"bottom"` |
| `padding` | string | `"0.15cm"` |

### Lists

```javascript
// Simple bullet list
doc.addList(["Apples", "Bananas", "Cherries"]);

// Numbered list
doc.addList(["First", "Second", "Third"], { type: "numbered" });

// Alpha / roman / custom formats
doc.addList(["Item a", "Item b"], { type: "numbered", numFormat: "a" });
doc.addList(["Item A", "Item B"], { type: "numbered", numFormat: "A" });
doc.addList(["Item i", "Item ii"], { type: "numbered", numFormat: "i" });
doc.addList(["Step 5", "Step 6"], { type: "numbered", startValue: 5 });
doc.addList(["Item", "Item"], { type: "numbered", numPrefix: "(", numSuffix: ")" });

// Nested with formatting — builder callback
doc.addList((l) => {
  l.addItem((p) => {
    p.addText("Important: ", { bold: true });
    p.addText("read the documentation");
  });
  l.addItem("Main topic");
  l.addNested((sub) => {
    sub.addItem("Subtopic A");
    sub.addItem("Subtopic B");
  });
});
```

**List options:**

| Option | Type | Example | Description |
|--------|------|---------|-------------|
| `type` | string | `"numbered"` | `"bullet"` (default) or `"numbered"` |
| `numFormat` | string | `"a"`, `"A"`, `"i"`, `"I"` | Number format; default `"1"` |
| `numPrefix` | string | `"("` | Text before number |
| `numSuffix` | string | `")"` | Text after number; default `"."` |
| `startValue` | number | `5` | Starting number |

### Images

```javascript
import { readFile } from "fs/promises";
const logo = await readFile("logo.png");

// Standalone
doc.addImage(logo, { width: "10cm", height: "6cm", mimeType: "image/png" });

// Inline in text
doc.addParagraph((p) => {
  p.addText("Logo: ");
  p.addImage(logo, { width: "2cm", height: "1cm", mimeType: "image/png" });
});
```

**Image options:**

| Option | Type | Required | Description |
|--------|------|----------|-------------|
| `width` | string | Yes | `"10cm"`, `"4in"` |
| `height` | string | Yes | `"6cm"`, `"3in"` |
| `mimeType` | string | Yes | `"image/png"`, `"image/jpeg"` |
| `anchor` | string | No | `"as-character"` or `"paragraph"` |

### Links and Bookmarks

```javascript
// External URL
doc.addParagraph((p) => {
  p.addText("Visit ");
  p.addLink("our website", "https://example.com", { bold: true });
});

// Internal bookmark target
doc.addParagraph((p) => {
  p.addBookmark("section-one");
  p.addText("Section 1: Introduction");
});

// Link to internal bookmark
doc.addParagraph((p) => {
  p.addLink("Go to Section 1", "#section-one");
});
```

### Tab Stops

```javascript
doc.addParagraph((p) => {
  p.addText("Item");
  p.addTab();
  p.addText("Qty");
  p.addTab();
  p.addText("$100.00");
}, {
  tabStops: [
    { position: "6cm" },
    { position: "12cm", type: "right" },
  ],
});
```

### Page Breaks

```javascript
doc.addPageBreak();
```

### Method Chaining

Every method returns the document for chaining:

```javascript
const bytes = await new OdtDocument()
  .setMetadata({ title: "Report" })
  .setPageLayout({ orientation: "landscape" })
  .setHeader("Confidential")
  .setFooter("Page ###")
  .addHeading("Summary", 1)
  .addParagraph("All systems operational.")
  .addTable([["System", "Status"], ["API", "OK"], ["DB", "OK"]])
  .addList(["No incidents", "No alerts"], { type: "numbered" })
  .save();
```

---

## Template Filling

Fill existing `.odt` templates created in LibreOffice with dynamic data. Templates use `{placeholder}` syntax.

### Basic Usage

```javascript
import { fillTemplate } from "odf-kit";
import { readFileSync, writeFileSync } from "fs";

const template = readFileSync("template.odt");
const result = fillTemplate(template, {
  name: "Alice",
  company: "Acme Corp",
  date: "2026-03-01",
});
writeFileSync("output.odt", result);
```

### Template Syntax

| Syntax | Description | Example |
|--------|-------------|---------|
| `{tag}` | Simple replacement | `Dear {name},` |
| `{object.property}` | Dot notation for nested data | `{company.address.city}` |
| `{#tag}...{/tag}` | Loop over array | `{#items}...{/items}` |
| `{#tag}...{/tag}` | Conditional (truthy/falsy) | `{#showNotes}...{/showNotes}` |

Loop items inherit parent data. Item properties override parent properties of the same name. Falsy values (`false`, `null`, `undefined`, `0`, `""`, `[]`) remove conditional sections.

### Placeholder Healing

LibreOffice often fragments `{placeholder}` text across multiple XML elements due to editing history or spell-check. odf-kit automatically reassembles fragmented placeholders before replacement — no manual XML cleanup needed.

---

## HTML → ODT

```javascript
import { htmlToOdt } from "odf-kit";

const bytes = await htmlToOdt(`
  <h1>Meeting Notes</h1>
  <p>Attendees: <strong>Alice</strong>, Bob</p>
  <ul><li>Project status</li><li>Budget review</li></ul>
  <table>
    <tr><th>Action</th><th>Owner</th></tr>
    <tr><td>Send report</td><td>Alice</td></tr>
  </table>
`, {
  pageFormat: "A4",        // "A4" | "letter" | "legal" | "A3" | "A5"
  orientation: "portrait", // "portrait" | "landscape"
  metadata: { title: "Meeting Notes", creator: "Alice" },
});
```

Supports: headings (h1–h6), paragraphs, bold, italic, underline, lists (ordered/unordered, nested), tables, blockquotes, code blocks, horizontal rules, inline CSS (color, font-size, font-family, text-align, background-color on cells).

---

## Markdown → ODT

```javascript
import { markdownToOdt } from "odf-kit";

const bytes = await markdownToOdt(`
# Report Title

Revenue **exceeded** expectations.

## Action Items
- Send report by Friday
- Review budget

| Region | Revenue |
|--------|---------|
| North  | $2.1M   |
`, { pageFormat: "A4" });
```

Full CommonMark support. Accepts the same options as `htmlToOdt`.

---

## TipTap / ProseMirror JSON → ODT

```javascript
import { tiptapToOdt } from "odf-kit";

// editor.getJSON() returns TipTap JSONContent
const bytes = await tiptapToOdt(editor.getJSON(), {
  pageFormat: "A4",
  images: { [imageUrl]: imageBytes },           // pre-fetched image bytes
  unknownNodeHandler: (node, doc) => {           // handle custom extensions
    if (node.type === "callout") doc.addParagraph(`⚠️ ${extractText(node)}`);
  },
});
```

No `@tiptap/core` dependency — walks the JSON tree directly. Supports all standard TipTap nodes and marks including tables, images, and nested lists.

---

## Build ODS Spreadsheets

```javascript
import { OdsDocument } from "odf-kit";
import { writeFileSync } from "fs";

const doc = new OdsDocument();
const sheet = doc.addSheet("Sales");

sheet.addRow(["Month", "Revenue", "Growth"], { bold: true, backgroundColor: "#DDDDDD" });
sheet.addRow(["January",  12500, 0.08]);
sheet.addRow(["February", 14200, 0.136]);
sheet.addRow(["Total", { value: "=SUM(B2:B3)", type: "formula" }]);
sheet.addRow([{ value: 0.1234, type: "percentage", numberFormat: "percentage:1" }]);
sheet.addRow([{ value: 1234.56, type: "currency", numberFormat: "currency:EUR" }]);
sheet.addRow([{ value: "odf-kit", type: "string", href: "https://github.com/GitHubNewbie0/odf-kit" }]);
sheet.addRow([{ value: "Q1 Report", type: "string", colSpan: 3 }]);

sheet.setColumnWidth(0, "4cm");
sheet.setColumnWidth(1, "4cm");
sheet.freezeRows(1);        // freeze top row
sheet.freezeColumns(1);     // freeze left column
sheet.setTabColor("#4CAF50");

const bytes = await doc.save();
writeFileSync("sales.ods", bytes);
```

**Cell value auto-types:** `number` → float · `Date` → date · `boolean` → boolean · `null`/`undefined` → empty · `string` → string. Use `{ value, type }` object for formula/percentage/currency.

**Number formats:** `"integer"` · `"decimal:N"` · `"percentage"` / `"percentage:N"` · `"currency:CODE"` / `"currency:CODE:N"`

---

## Read ODT / Convert to HTML

```javascript
import { readOdt, odtToHtml } from "odf-kit/reader";
import { readFileSync } from "fs";

const bytes = readFileSync("document.odt");
const doc = readOdt(bytes);

// Render to HTML string
const html = odtToHtml(bytes);                         // full HTML document
const fragment = odtToHtml(bytes, { fragment: true }); // body content only

// Walk the structured document model
for (const node of doc.body) {
  if (node.kind === "heading")   console.log(`H${node.level}:`, node.spans[0].text);
  if (node.kind === "paragraph") console.log(node.spans.map(s => s.text).join(""));
}
console.log(doc.metadata.title);
```

---

## Read ODS

```javascript
import { readOds, odsToHtml } from "odf-kit/ods-reader";
import { readFileSync } from "fs";

const bytes = readFileSync("data.ods");

// Parse to structured model — typed JavaScript values
const model = readOds(bytes);
for (const row of model.sheets[0].rows) {
  for (const cell of row.cells) {
    console.log(cell.type, cell.value);
    // type: "string" | "float" | "boolean" | "date" | "formula" | "empty" | "covered"
    // value: string | number | boolean | Date | null — never a display-formatted string
  }
}

// Or convert to an HTML table
const html = odsToHtml(bytes);
```

---

## XLSX → ODS

```javascript
import { xlsxToOds } from "odf-kit/xlsx";
import { readFileSync, writeFileSync } from "fs";

const ods = await xlsxToOds(readFileSync("report.xlsx"));
writeFileSync("report.ods", ods);

// Also works in browser
const ods2 = await xlsxToOds(await file.arrayBuffer());
```

Preserves: strings, numbers, booleans, dates, formulas (cached result), merged cells, freeze panes, multiple sheets. No SheetJS dependency — own parser built on fflate.

---

## DOCX → ODT

```javascript
import { docxToOdt } from "odf-kit/docx";
import { readFileSync, writeFileSync } from "fs";

const { bytes, warnings } = await docxToOdt(readFileSync("report.docx"), {
  pageFormat: "letter",             // override page format (default: read from DOCX)
  preservePageLayout: true,         // read size/margins from DOCX sectPr (default: true)
  styleMap: { "Section Title": 1, "Sub Title": 2 }, // custom style → heading level
  metadata: { title: "My Report" }, // override metadata
});
writeFileSync("report.odt", bytes);
if (warnings.length) console.warn(warnings);  // log during development

// Also works in browser — pure ESM, zero new dependencies
const { bytes: odt } = await docxToOdt(await file.arrayBuffer());
```

Preserves: headings, paragraphs, all text formatting (bold, italic, underline, font sizes, colors), lists (bullet/numbered/nested), tables (merged cells, column widths), hyperlinks, bookmarks, images (actual dimensions), page layout, headers/footers, footnotes, tracked changes (final-text mode).

---

## ODT → Typst / PDF

```javascript
import { odtToTypst, modelToTypst } from "odf-kit/typst";
import { readOdt } from "odf-kit/reader";
import { readFileSync, writeFileSync } from "fs";
import { execSync } from "child_process";

const bytes = new Uint8Array(readFileSync("document.odt"));

// One-call convenience
const typ = odtToTypst(bytes);
writeFileSync("document.typ", typ);
execSync("typst compile document.typ document.pdf"); // Typst CLI installed separately

// Parse once, emit to multiple formats
const model = readOdt(bytes);
const typst = modelToTypst(model);
```

`odf-kit/typst` is zero-dependency and browser-safe. The Typst CLI is only needed when compiling to PDF.

---

## Critical Rules for odf-kit

- **Always use `await` with `save()`** — it returns a `Promise<Uint8Array>`
- **ESM only** — use `import`, not `require`. File must use `.mjs` extension or `"type": "module"` in `package.json`
- **Use `writeFileSync`** (or `writeFile`) to write the `Uint8Array` to disk
- **`fontSize` as number = points** — `14` means 14pt
- **Images require all three options** — `width`, `height`, and `mimeType` are all required
- **`fillTemplate` is synchronous** — returns `Uint8Array` directly, no `await` needed
- **`###` in header/footer strings** is replaced with page numbers automatically
- **A4 is the default page size** — set explicit dimensions for US Letter (`8.5in` × `11in`)
- **`fontWeight` numeric** — accepts CSS-style values 100–900 as well as `"bold"` / `"normal"`
- **`lineHeight` as number** — `1.5` means 150% line height; strings like `"150%"` also accepted
- **`docxToOdt` returns `{ bytes, warnings }`** — always destructure, log warnings in development
- **`readOds` cell values are typed** — `cell.value` is `string | number | boolean | Date | null`, never a display-formatted string

---

## Complete Example

```javascript
import { OdtDocument } from "odf-kit";
import { writeFileSync } from "fs";

async function createReport() {
  const doc = new OdtDocument();

  doc.setMetadata({ title: "Monthly Report", creator: "Operations Team" });
  doc.setPageLayout({
    width: "8.5in", height: "11in",
    marginTop: "1in", marginBottom: "1in",
    marginLeft: "1in", marginRight: "1in",
  });
  doc.setHeader((h) => {
    h.addText("Monthly Operations Report", { bold: true });
    h.addText(" — Page ");
    h.addPageNumber();
  });
  doc.setFooter("© 2026 Acme Corp");

  doc.addHeading("Executive Summary", 1, { spaceBefore: "0.5cm" });
  doc.addParagraph(
    "All operations performed within expected parameters.",
    { align: "justify", lineHeight: 1.5 }
  );

  doc.addHeading("Key Metrics", 2);
  doc.addTable((t) => {
    t.addRow((r) => {
      ["Metric", "Target", "Actual", "Status"].forEach((h) =>
        r.addCell(h, { bold: true, backgroundColor: "#DDDDDD", verticalAlign: "middle" })
      );
    }, { backgroundColor: "#DDDDDD" });
    t.addRow((r) => {
      r.addCell("Uptime"); r.addCell("99.9%"); r.addCell("99.95%");
      r.addCell("✓", { color: "green" });
    });
  }, { columnWidths: ["5cm", "3cm", "3cm", "2cm"], border: "0.5pt solid #000000" });

  doc.addHeading("Action Items", 2);
  doc.addList([
    "Complete infrastructure audit by March 15",
    "Deploy monitoring upgrade to production",
    "Review disaster recovery procedures",
  ], { type: "numbered" });

  doc.addHeading("Notes", 2);
  doc.addParagraph((p) => {
    p.addText("Priority: ", { bold: true, color: "red" });
    p.addText("Database migration scheduled for next maintenance window. ");
    p.addLink("See migration plan", "https://docs.example.com/migration");
    p.addText(" for details.");
  }, { indentLeft: "0.5cm" });

  const bytes = await doc.save();
  writeFileSync("report.odt", bytes);
}

createReport();
```
