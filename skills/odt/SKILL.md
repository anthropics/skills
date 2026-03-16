---
name: odt
description: "Use this skill whenever the user wants to create, fill, read, convert, or export OpenDocument Format text files (.odt files). Triggers include: any mention of 'ODT', 'ODF', 'OpenDocument', 'LibreOffice document', or requests to produce documents in open-source or ISO standard formats. Also use when filling ODT templates with data, reading or parsing .odt files, converting .odt to HTML, exporting .odt to Typst for PDF generation, or creating formal documents like resolutions, reports, letters, contracts, or memos as .odt files. Use this skill instead of the docx skill when the user explicitly requests .odt output or mentions LibreOffice/OpenOffice as their target application. Do NOT use for .docx files (use the docx skill), spreadsheets, presentations, or general coding tasks unrelated to document generation."
license: Apache-2.0
---

# ODT creation, template filling, reading, and conversion

## Overview

An `.odt` file is an OpenDocument Format text document — an ISO standard (ISO/IEC 26300) ZIP archive containing XML files. It is the native format for LibreOffice, Apache OpenOffice, Collabora, OnlyOffice, and is supported by Google Docs and Microsoft Office.

## Quick Reference

| Task | Approach |
|------|----------|
| Create new document | Use `odf-kit` — see Creating New Documents below |
| Fill existing template | Use `odf-kit` `fillTemplate()` — see Template Filling below |
| Read / convert to HTML | Use `odf-kit/reader` `odtToHtml()` — see Reading .odt Files below |
| Export to Typst for PDF | Use `odf-kit/typst` `odtToTypst()` — see Exporting to Typst below |
| Convert to PDF (LibreOffice) | `libreoffice --headless --convert-to pdf document.odt` |

### Dependencies

```bash
npm install -g odf-kit
```

Requires Node.js 22 or later. ESM only.

---

## Creating New Documents

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

### Formatted Text

```javascript
doc.addParagraph((p) => {
  p.addText("This is ");
  p.addText("bold", { bold: true });
  p.addText(", ");
  p.addText("italic", { italic: true });
  p.addText(", and ");
  p.addText("colored", { color: "#FF0000", fontSize: 14 });
  p.addText(".");
});
```

Available text formatting options:

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
| `color` | string | `"#FF0000"` or `"red"` |
| `highlightColor` | string | `"#FFFF00"` or `"yellow"` |

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
    r.addCell("Header", { bold: true, backgroundColor: "#DDDDDD" });
    r.addCell("Value", { bold: true, backgroundColor: "#DDDDDD" });
  });
  t.addRow((r) => {
    r.addCell("Status");
    r.addCell("Complete", { color: "green" });
  });
}, { columnWidths: ["8cm", "4cm"] });
```

Cell options extend text formatting with:

| Option | Type | Example |
|--------|------|---------|
| `backgroundColor` | string | `"#EEEEEE"` |
| `border` | string | `"0.5pt solid #000000"` |
| `borderTop`, `borderBottom`, `borderLeft`, `borderRight` | string | Per-side borders |
| `colSpan` | number | `2` |
| `rowSpan` | number | `3` |

### Lists

```javascript
// Simple bullet list
doc.addList(["Apples", "Bananas", "Cherries"]);

// Numbered list
doc.addList(["First", "Second", "Third"], { type: "numbered" });

// Nested with formatting
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

Image options:

| Option | Type | Required | Description |
|--------|------|----------|-------------|
| `width` | string | Yes | `"10cm"`, `"4in"` |
| `height` | string | Yes | `"6cm"`, `"3in"` |
| `mimeType` | string | Yes | `"image/png"`, `"image/jpeg"` |
| `anchor` | string | No | `"as-character"` or `"paragraph"` |

### Links and Bookmarks

```javascript
// Create a bookmark target
doc.addParagraph((p) => {
  p.addBookmark("section-one");
  p.addText("Section 1: Introduction");
});

// Link to external URL
doc.addParagraph((p) => {
  p.addText("Visit ");
  p.addLink("our website", "https://example.com", { bold: true });
});

// Link to internal bookmark
doc.addParagraph((p) => {
  p.addText("Go back to ");
  p.addLink("Section 1", "#section-one");
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
doc.addHeading("Chapter 1", 1);
doc.addParagraph("First chapter content.");
doc.addPageBreak();
doc.addHeading("Chapter 2", 1);
doc.addParagraph("Second chapter content.");
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

Fill existing `.odt` templates created in LibreOffice with dynamic data. Templates use `{placeholder}` syntax in the document text.

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

### Loops

In the template document:
```
{#items}
Product: {product} — Qty: {qty} — Price: {price}
{/items}
```

In code:
```javascript
fillTemplate(template, {
  items: [
    { product: "Widget", qty: 5, price: "$125" },
    { product: "Gadget", qty: 3, price: "$120" },
  ],
});
```

Loop items inherit parent data. Item properties override parent properties of the same name.

### Conditionals

Falsy values (`false`, `null`, `undefined`, `0`, `""`, `[]`) remove the section. Truthy values include it.

```javascript
fillTemplate(template, {
  showDiscount: true,
  discount: "10%",
  showNotes: false,  // {#showNotes}...{/showNotes} section removed
});
```

### Nesting

Loops and conditionals nest freely to any depth.

### Placeholder Healing

LibreOffice often fragments `{placeholder}` text across multiple XML elements due to editing history or spell-check. odf-kit automatically reassembles fragmented placeholders before replacement — no manual XML cleanup needed.

---

## Reading .odt Files

Parse existing `.odt` files into a structured document model or convert directly to HTML. Import from `odf-kit/reader`.

### Convert to HTML

```javascript
import { odtToHtml } from "odf-kit/reader";
import { readFileSync, writeFileSync } from "node:fs";

const bytes = new Uint8Array(readFileSync("document.odt"));

// Full HTML document
const html = odtToHtml(bytes);
writeFileSync("document.html", html);

// Inner fragment only (for embedding in an existing page)
const fragment = odtToHtml(bytes, { fragment: true });
```

### Parse to Document Model

```javascript
import { readOdt } from "odf-kit/reader";

const bytes = new Uint8Array(readFileSync("document.odt"));
const doc = readOdt(bytes);

// Metadata
console.log(doc.metadata.title);
console.log(doc.metadata.creator);

// Page geometry
console.log(doc.pageLayout?.orientation);  // "portrait" | "landscape"
console.log(doc.pageLayout?.width);        // "21cm"

// Walk the body
for (const node of doc.body) {
  if (node.kind === "heading")   console.log(`h${node.level}:`, node.spans[0].text);
  if (node.kind === "paragraph") console.log(node.spans.map(s => s.text).join(""));
  if (node.kind === "table")     console.log(`table: ${node.rows.length} rows`);
  if (node.kind === "list")      console.log(`list: ${node.items.length} items`);
  if (node.kind === "section")   console.log(`section: ${node.name}`);
}
```

### BodyNode types

| `kind` | Description |
|--------|-------------|
| `"paragraph"` | Text paragraph with `spans: InlineNode[]` |
| `"heading"` | Heading with `level: 1–6` and `spans` |
| `"list"` | Ordered or unordered list with `items` |
| `"table"` | Table with `rows` → `cells` → `spans` |
| `"section"` | Named document section with nested `body` |
| `"tracked-change"` | Tracked change with `changeType`, `author`, `date`, `body` |

### Inline node types

Each `spans` array contains `InlineNode` values. Narrow by `"kind"`:

```javascript
for (const span of node.spans) {
  if ("kind" in span) {
    if (span.kind === "image")    // ImageNode — span.data is base64
    if (span.kind === "note")     // NoteNode — footnote/endnote
    if (span.kind === "bookmark") // BookmarkNode
    if (span.kind === "field")    // FieldNode — page number, date, etc.
  } else {
    // TextSpan — span.text, span.bold, span.italic, span.href, span.style
  }
}
```

### Tracked changes

```javascript
import { readOdt, odtToHtml } from "odf-kit/reader";

// "final" (default) — show document as if all changes accepted
const doc = readOdt(bytes);

// "original" — show document as if all changes rejected
const doc = readOdt(bytes, { trackedChanges: "original" });

// "changes" — expose TrackedChangeNode values in the body
const doc = readOdt(bytes, { trackedChanges: "changes" });
const html = doc.toHtml({ trackedChanges: "changes" });
// insertions → <ins>, deletions → <del>
```

---

## Exporting to Typst for PDF

Convert `.odt` files to [Typst](https://typst.app/) markup, then compile to PDF with the Typst CLI. Import from `odf-kit/typst`. Zero new dependencies — works in Node.js, browsers, and any JavaScript environment.

### Basic usage

```javascript
import { odtToTypst } from "odf-kit/typst";
import { readFileSync, writeFileSync } from "node:fs";
import { execSync } from "node:child_process";

const bytes = new Uint8Array(readFileSync("document.odt"));

// Convert to Typst markup
const typ = odtToTypst(bytes);
writeFileSync("document.typ", typ);

// Compile to PDF (requires Typst CLI installed separately)
execSync("typst compile document.typ document.pdf");
```

### Parse once, emit to multiple formats

Use `modelToTypst()` when you already have a parsed model — avoids re-reading the file:

```javascript
import { readOdt } from "odf-kit/reader";
import { modelToTypst } from "odf-kit/typst";

const bytes = new Uint8Array(readFileSync("document.odt"));
const model = readOdt(bytes);

const html  = model.toHtml({ fragment: true });  // HTML
const typst = modelToTypst(model);               // Typst markup
```

### Installing the Typst CLI

```bash
# macOS
brew install typst

# Windows
winget install --id Typst.Typst

# Linux / via npm
npm install -g typst
```

### Typst coverage

Headings, paragraphs (with text-align via `#align()`), bold, italic, underline, strikethrough, superscript, subscript, hyperlinks via `#link()`, footnotes via `#footnote[]`, bookmarks as Typst labels, text fields (page number → `#counter(page).display()`), unordered and ordered lists with nesting, tables with column widths, named sections, tracked changes (final/original/changes modes), page geometry via `#set page()`, and character styles (color, font size, font family, highlight).

**Images** are emitted as comment placeholders — Typst does not support inline base64 without filesystem access:

```typst
/* [image: logo.png 10cm × 6cm] */
```

To include images in the PDF, extract `ImageNode.data` (base64) from the model, write files alongside the `.typ`, then substitute placeholders with `#image("logo.png")`.

### TypstEmitOptions

| Option | Values | Default | Description |
|--------|--------|---------|-------------|
| `trackedChanges` | `"final"` \| `"original"` \| `"changes"` | `"final"` | How tracked changes are emitted in Typst output |

---

## Validation

After creating a file, verify it opens correctly:

```bash
# Convert to PDF as a validation step
libreoffice --headless --convert-to pdf output.odt

# Or use the Typst path (no LibreOffice needed)
# See Exporting to Typst above
```

---

## Critical Rules for odf-kit

- **Always use `await` with `save()`** — it returns a `Promise<Uint8Array>`
- **ESM only** — use `import`, not `require`. File must use `.mjs` extension or `"type": "module"` in package.json
- **Use `writeFileSync`** (or `writeFile`) to write the Uint8Array to disk
- **`fontSize` as number = points** — `14` means 14pt
- **Images require all three options** — `width`, `height`, and `mimeType` are all required
- **Template `fillTemplate` is synchronous** — returns `Uint8Array` directly (no await needed)
- **`###` in header/footer strings** is replaced with page numbers automatically
- **A4 is the default page size** — set explicit dimensions for US Letter (`8.5in` × `11in`)
- **Reader and Typst are separate sub-exports** — import from `odf-kit/reader` and `odf-kit/typst`, not from `odf-kit`

---

## Complete Example

```javascript
import { OdtDocument } from "odf-kit";
import { writeFileSync } from "fs";

async function createReport() {
  const doc = new OdtDocument();

  doc.setMetadata({ title: "Monthly Report", creator: "Operations Team" });
  doc.setPageLayout({
    width: "8.5in",
    height: "11in",
    marginTop: "1in",
    marginBottom: "1in",
    marginLeft: "1in",
    marginRight: "1in",
  });
  doc.setHeader((h) => {
    h.addText("Monthly Operations Report", { bold: true });
    h.addText(" — Page ");
    h.addPageNumber();
  });
  doc.setFooter("© 2026 Acme Corp");

  doc.addHeading("Executive Summary", 1);
  doc.addParagraph("All operations performed within expected parameters.");

  doc.addHeading("Key Metrics", 2);
  doc.addTable([
    ["Metric", "Target", "Actual", "Status"],
    ["Uptime", "99.9%", "99.95%", "✓"],
    ["Response Time", "<200ms", "145ms", "✓"],
    ["Error Rate", "<0.1%", "0.08%", "✓"],
  ], {
    columnWidths: ["5cm", "3cm", "3cm", "2cm"],
    border: "0.5pt solid #000000",
  });

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
    p.addText("See ", { italic: true });
    p.addLink("migration plan", "https://docs.example.com/migration");
    p.addText(" for details.", { italic: true });
  });

  const bytes = await doc.save();
  writeFileSync("report.odt", bytes);
}

createReport();
```

---

## Dependencies

- **odf-kit**: `npm install -g odf-kit` — document creation, template filling, reading, and Typst export
- **Typst CLI** (optional): PDF compilation only — `npm install -g typst` or via system package manager
- **LibreOffice** (optional): alternative PDF conversion — `libreoffice --headless`
