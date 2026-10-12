---
name: academic-manuscript
description: "Use this skill for creating, formatting, or editing scientific manuscripts and academic papers as Word documents (.docx). Triggers include: writing or rewriting a research paper, generating a manuscript from data/results, formatting a paper for journal submission, adding real references from DOIs or BibTeX, injecting Zotero/Mendeley-style field codes into citations, creating supplementary materials, cover letters, or reviewer responses. Also use when the user mentions 'paper', 'manuscript', 'journal submission', 'references', 'bibliography', 'citation style', 'Vancouver', 'APA', or discusses integrating analysis results (ML, metabolomics, clinical trials, omics) into a publication. Use this skill even when the user just uploads data and asks to 'write up the results'. This skill extends the docx skill with academic-specific features: real reference fetching, Zotero field code injection, journal-style formatting, and structured scientific sections."
---

# Academic Manuscript Skill

Generate publication-ready scientific manuscripts as .docx files with real references, Zotero-compatible field codes, and journal-quality formatting.

## Overview

This skill produces Word documents that look like they came from a professional reference manager workflow. The key differentiator is that citations are embedded as Word field codes (`ADDIN ZOTERO_ITEM CSL_CITATION`) so they highlight grey on click in Word, exactly like Zotero or Mendeley output.

## When to Use

- User wants to write or rewrite a scientific paper
- User has analysis results and needs them in manuscript form
- User asks for "real references" or "proper citations"
- User mentions Zotero, Mendeley, or reference management
- User wants journal-formatted output (Nature, Cell, Lancet, etc.)
- User uploads data/figures and asks to "write up" or "prepare for submission"

## Dependencies

Before starting, ensure these are available:
```bash
npm list -g docx 2>/dev/null || npm install -g docx
pip install requests --break-system-packages -q
```

Also read the base docx skill first for core formatting patterns:
```
Read /mnt/skills/public/docx/SKILL.md
```

## Pipeline Overview

The full academic manuscript pipeline has 4 stages:

| Stage | What It Does | Script |
|-------|-------------|--------|
| 1. Content Assembly | Structure manuscript sections from user input | Manual (guided by SKILL.md) |
| 2. Reference Fetching | Get real citation metadata from CrossRef API | `scripts/fetch_references.py` |
| 3. Document Generation | Build docx with docx-js, tables, formatting | Node.js with docx package |
| 4. Zotero Field Injection | Add Word field codes for citation highlighting | `scripts/inject_zotero_fields.py` |

Stages can be used independently. For example, stage 4 alone can add Zotero field codes to any existing manuscript.

---

## Stage 1: Content Assembly

### Manuscript Structure

Use this standard structure for biomedical/life science papers (Cell/Nature style). Adapt sections based on the target journal.

```
Title
Authors + Affiliations
Summary/Abstract
Keywords
Introduction
Results
  - Subsections per finding
  - Tables and figure legends inline
Discussion
  - Interpretation
  - Limitations
  - Future directions
Conclusions
STAR★Methods (or Materials and Methods)
  - Study design
  - Data collection
  - Analysis methods
Resource Availability
Acknowledgments
Author Contributions
Declaration of Interests
References
```

For other journal styles, adjust the order (e.g., IMRaD: Introduction, Methods, Results, Discussion).

### Writing Guidelines

When generating manuscript text:
- Use past tense for methods and results, present tense for established facts
- Report statistics precisely: effect sizes, confidence intervals, p-values
- Avoid first person in methods; use sparingly elsewhere
- Define abbreviations on first use
- Reference figures/tables as "Figure 1" or "Table 1" (capitalised)
- Use inline citations as `[N]` or `[N,N,N]` for numbered styles

---

## Stage 2: Reference Fetching

Use `scripts/fetch_references.py` to retrieve real citation metadata from CrossRef.

### Input Format

Prepare a JSON array of references with DOIs where available:

```json
[
  {"id": 1, "doi": "10.1016/j.jacc.2020.11.010", "fallback": "Roth et al., JACC, 2020"},
  {"id": 2, "doi": null, "fallback": "Murray et al., Ann. Rheum. Dis., 2014"}
]
```

- `id`: Sequential reference number (matches inline citation numbers)
- `doi`: DOI string if known. The script fetches metadata from CrossRef.
- `fallback`: Pre-formatted citation string used when DOI is missing or CrossRef returns wrong data

### Running

```bash
python3 scripts/fetch_references.py --input refs_input.json --output references.json --style vancouver
```

### Output

The script produces a JSON file with verified, formatted citations:
```json
[
  {"id": 1, "doi": "10.1016/...", "formatted": "Roth G. A., Mensah G. A., ...", "source": "crossref"},
  {"id": 2, "doi": null, "formatted": "Murray et al., ...", "source": "fallback"}
]
```

### Handling CrossRef Mismatches

CrossRef sometimes returns wrong papers for a DOI (especially for DOIs with special characters or old publications). After fetching, verify key references and correct mismatches by updating the `formatted` field and setting `source` to `manual_fix`.

### Citation Styles

The script supports these output styles (set via `--style`):

| Style | Format | Use For |
|-------|--------|---------|
| `vancouver` | Author A. B., Author C. D. Title. Journal. Year;Vol(Issue):Pages. doi:xxx | Most biomedical journals, numbered references |
| `apa` | Author, A. B., & Author, C. D. (Year). Title. *Journal*, *Vol*(Issue), Pages. | Psychology, social sciences |
| `nature` | Author, A. B., Author, C. D. Title. *Journal* **Vol**, Pages (Year). | Nature family journals |

Default is `vancouver` (numbered references). The style only affects the bibliography formatting; inline citations are always `[N]` for numbered styles.

---

## Stage 3: Document Generation

Build the manuscript using Node.js with the docx package. Follow these academic-specific patterns in addition to the base docx skill rules.

### Academic Document Template

```javascript
const fs = require("fs");
const {
  Document, Packer, Paragraph, TextRun, Table, TableRow, TableCell,
  Header, Footer, AlignmentType, HeadingLevel, BorderStyle,
  WidthType, ShadingType, PageNumber, PageBreak, TabStopType
} = require("docx");

// Load references
const refs = JSON.parse(fs.readFileSync("references.json", "utf-8"));

// ── Helpers ──
const txt = (t, opts = {}) => new TextRun({ text: t, font: "Times New Roman", size: 24, ...opts });
const bold = (t, opts = {}) => txt(t, { bold: true, ...opts });
const italic = (t, opts = {}) => txt(t, { italics: true, ...opts });
const sup = (t) => new TextRun({ text: t, font: "Times New Roman", size: 24, superScript: true });

const para = (runs, opts = {}) => new Paragraph({
  spacing: { after: 120, line: 360 },  // 1.5 line spacing for manuscripts
  ...opts,
  children: Array.isArray(runs) ? runs : [txt(runs)],
});

const heading = (text, level) => new Paragraph({
  heading: level,
  spacing: { before: 240, after: 160 },
  children: [new TextRun({
    text, font: "Times New Roman", bold: true,
    size: level === HeadingLevel.HEADING_1 ? 28
        : level === HeadingLevel.HEADING_2 ? 26 : 24
  })],
});

// ── Reference paragraph (Zotero-style hanging indent) ──
function makeRefParagraph(ref) {
  return new Paragraph({
    spacing: { after: 80, line: 276 },
    indent: { left: 567, hanging: 567 },  // 1cm hanging indent
    tabStops: [{ type: TabStopType.LEFT, position: 567 }],
    children: [
      new TextRun({ text: `${ref.id}. \t`, font: "Times New Roman", size: 20 }),
      new TextRun({ text: ref.formatted, font: "Times New Roman", size: 20 }),
    ],
  });
}
```

### Key Formatting Rules for Academic Manuscripts

1. **Font**: Times New Roman 12pt body, 10pt for references and table content
2. **Line spacing**: 1.5 (line: 360 in docx-js) for body text, single for references
3. **Margins**: 1 inch all sides (1440 DXA)
4. **Page size**: US Letter (12240 x 15840) or A4 depending on journal
5. **Headers**: Running title (shortened) + page numbers
6. **Tables**: Professional academic style with light borders, header shading
7. **References**: Hanging indent (567 DXA = ~1cm), numbered, 10pt font

### Table Style for Academic Papers

```javascript
const border = { style: BorderStyle.SINGLE, size: 1, color: "999999" };
const borders = { top: border, bottom: border, left: border, right: border };
const cellMargins = { top: 60, bottom: 60, left: 80, right: 80 };

// Header cell
const hCell = (text, width) => new TableCell({
  borders, width: { size: width, type: WidthType.DXA }, margins: cellMargins,
  shading: { fill: "D5E8F0", type: ShadingType.CLEAR },
  children: [new Paragraph({ children: [bold(text, { size: 20 })] })],
});

// Body cell
const cell = (text, width) => new TableCell({
  borders, width: { size: width, type: WidthType.DXA }, margins: cellMargins,
  children: [new Paragraph({ children: [txt(text, { size: 20 })] })],
});
```

### Author Affiliations

Use superscript numbers for multi-affiliation papers:

```javascript
// Author line
new Paragraph({
  alignment: AlignmentType.CENTER,
  children: [
    txt("First Author", { size: 22 }), sup("1,2"), txt(", ", { size: 22 }),
    txt("Second Author", { size: 22 }), sup("1"),
  ],
}),
// Affiliation lines
new Paragraph({
  alignment: AlignmentType.CENTER,
  children: [sup("1"), italic("Department, University, City, Country", { size: 20 })],
}),
```

---

## Stage 4: Zotero Field Code Injection

This is the critical stage that makes citations behave like Zotero/Mendeley output. Use `scripts/inject_zotero_fields.py` to add Word field codes.

### What It Does

Transforms plain `[1]` citations into Word complex field codes:
```xml
<w:fldChar fldCharType="begin"/>
<w:instrText> ADDIN ZOTERO_ITEM CSL_CITATION {"citationID":"...", ...} </w:instrText>
<w:fldChar fldCharType="separate"/>
<w:t>[1]</w:t>
<w:fldChar fldCharType="end"/>
```

This produces:
- Grey highlighting when you click a citation in Word
- Alt+F9 toggles to show the underlying JSON (just like real Zotero)
- The bibliography section is wrapped in `ADDIN ZOTERO_BIBL` field

### Running

```bash
# Step 1: Unpack the docx
python3 /mnt/skills/public/docx/scripts/office/unpack.py manuscript.docx unpacked/

# Step 2: Inject Zotero fields
python3 scripts/inject_zotero_fields.py --unpacked unpacked/ --refs references.json

# Step 3: Repack
python3 /mnt/skills/public/docx/scripts/office/pack.py unpacked/ output.docx --original manuscript.docx
```

If validation fails with namespace issues (common after XML manipulation), the script automatically fixes missing namespace declarations. If it still fails, use `--validate false` on the pack step — the document will still open correctly in Word.

### Important Technical Notes

- Field code runs (`<w:fldChar>`) must NOT contain `<w:rPr>` elements — keep them bare
- The script uses ElementTree for proper XML manipulation (never regex on raw XML containing tables)
- `<w:instrText>` must have `xml:space="preserve"` attribute
- Bibliography field wraps all reference paragraphs between `begin` and `end` field chars
- Reference paragraphs are identified by matching `^\d+\.\s` pattern in text nodes

---

## Quick Start: Full Pipeline

For a complete manuscript from scratch:

```bash
# 1. Prepare reference list as JSON (with DOIs)
# 2. Fetch real metadata
python3 scripts/fetch_references.py --input refs_input.json --output references.json

# 3. Generate manuscript (adapt the Node.js template for your content)
node generate_manuscript.js

# 4. Validate base document
python3 /mnt/skills/public/docx/scripts/office/validate.py manuscript.docx

# 5. Inject Zotero fields
python3 /mnt/skills/public/docx/scripts/office/unpack.py manuscript.docx unpacked/
python3 scripts/inject_zotero_fields.py --unpacked unpacked/ --refs references.json
python3 /mnt/skills/public/docx/scripts/office/pack.py unpacked/ final_manuscript.docx --original manuscript.docx
```

## Quick Start: Adding Zotero Fields to Existing Document

If the user already has a manuscript and just wants Zotero-style citations:

```bash
python3 /mnt/skills/public/docx/scripts/office/unpack.py their_document.docx unpacked/
python3 scripts/inject_zotero_fields.py --unpacked unpacked/ --refs references.json
python3 /mnt/skills/public/docx/scripts/office/pack.py unpacked/ output.docx --original their_document.docx
```

The script auto-detects `[N]` patterns in the document text and wraps them.

---

## Generating a BibTeX File

To export references for import into Zotero/Mendeley:

```bash
python3 scripts/fetch_references.py --input refs_input.json --output refs.bib --format bibtex
```

This creates a standard `.bib` file that can be imported into any reference manager, establishing the link between the document field codes and the user's library.

---

## Adapting for Different Journals

Read `references/journal-styles.md` for specific formatting requirements for common target journals including Nature, Cell, The Lancet, PLOS ONE, and IEEE formats.

Key differences between journals:
- **Reference style**: Vancouver (numbered) vs Author-Year (Harvard/APA)
- **Section order**: IMRaD vs STAR Methods vs custom
- **Word limits**: Abstract and main text limits
- **Figure placement**: Inline vs end-of-document
- **Line numbering**: Required by some journals (add via Word after generation)
