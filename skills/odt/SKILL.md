---
name: odt
description: "Use this skill whenever the user wants to create, fill, or manipulate OpenDocument Format text files (.odt files). Triggers include: any mention of 'ODT', 'ODF', 'OpenDocument', 'LibreOffice document', or requests to produce documents in open-source or ISO standard formats. Also use when the user asks for a document and specifies LibreOffice compatibility, when filling ODT templates with data, or when creating formal documents like resolutions, reports, letters, contracts, or memos as .odt files. Use this skill instead of the docx skill when the user explicitly requests .odt output or mentions LibreOffice/OpenOffice as their target application. Do NOT use for .docx files (use the docx skill), PDFs, spreadsheets, presentations, or general coding tasks unrelated to document generation."
license: Apache-2.0
---

# ODT creation and template filling

## Overview

An `.odt` file is an OpenDocument Format text document — an ISO standard (ISO/IEC 26300) ZIP archive containing XML files. It is the native format for LibreOffice, Apache OpenOffice, Collabora, OnlyOffice, and is supported by Google Docs and Microsoft Office. odf-kit works in Node.js and browsers, but in this environment it runs in Node.js.

## Quick Reference

| Task | Approach |
|------|----------|
| Create new document | Use `odf-kit` — see Creating New Documents below |
| Fill existing template | Use `odf-kit` `fillTemplate()` — see Template Filling below |
| Read/extract content | Unzip and parse `content.xml` |
| Convert to PDF | `libreoffice --headless --convert-to pdf document.odt` |

### Dependencies

```bash
npm install -g odf-kit
```

Requires Node.js 18 or later. ESM only.

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

## Validation

After creating a file, verify it opens correctly:

```bash
# Convert to PDF as a validation step
libreoffice --headless --convert-to pdf output.odt

# Or convert to images for visual inspection
libreoffice --headless --convert-to pdf output.odt
pdftoppm -jpeg -r 150 output.pdf preview
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

- **odf-kit**: `npm install -g odf-kit` (document creation and template filling)
- **LibreOffice**: PDF conversion and validation (`libreoffice --headless`)
