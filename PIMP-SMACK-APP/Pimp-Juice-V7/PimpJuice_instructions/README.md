# Pimp Formatting Skills - Legal Document Formatter

**Stop getting dismissed for formatting errors. Format legal documents perfectly using schema inheritance.**

---

## What This Skill Does

Automatically formats legal documents for ANY jurisdiction:

1. **Schema Inheritance** - 95% formatting from master schemas (FRCP/FRAP), 5% user customization
2. **Text Preservation** - ALL your content stays exactly as written
3. **Style Application** - Only formatting (font, size, spacing) changes
4. **Court-Ready Output** - Proper margins, fonts, spacing per jurisdiction

---

## Quick Start

### 1. Copy User Schema Template

```bash
cd PimpJuice_instructions/schemas
cp user_schema_template.json my_case.json
```

### 2. List Your Headings

Edit `my_case.json`:

```json
{
  "_inherits_from": "MASTER_FRCP",
  
  "headings_in_my_document": [
    "INTRODUCTION",
    "FACTUAL BACKGROUND",
    "LEGAL STANDARD",
    "ARGUMENT",
    "CONCLUSION"
  ]
}
```

**That's it!** Everything else inherits from MASTER_FRCP.json.

### 3. Run Formatter

```bash
python scripts/format_document.py \
  PimpJuice_instructions/schemas/my_case.json \
  rough_draft.docx
```

### 4. Get Formatted Doc

Output appears in `/mnt/user-data/outputs/` with timestamp.

---

## How Schema Inheritance Works

```
MASTER_FRCP.json
├── Font: California, 12pt
├── Spacing: Double
├── Margins: 1" all sides
├── H1: Bold, caps, centered
├── H2: Bold, left-aligned
├── H3: Bold, indented 0.5"
├── H4: Italic, indented 1"
└── Body: Regular, 0.5" first-line indent

    ↓ (YOU INHERIT ALL OF THIS)

YOUR_SCHEMA.json
└── headings_in_my_document: ["INTRODUCTION", "ARGUMENT", "CONCLUSION"]

    ↓ (MERGE)

FINAL CONFIG
├── All master defaults
└── Your headings list
```

**You only specify what's different!**

---

## Master Schemas

### MASTER_FRCP.json (District Court)

**Use for:** Motions, briefs, complaints, answers

**Defaults:**
- Font: California (fallback: Century Schoolbook → Times New Roman)
- Size: 12pt
- Spacing: Double
- Margins: 1" all sides
- Body indent: 0.5" first line

### MASTER_FRAP.json (Court of Appeals)

**Use for:** Appellate briefs

**Defaults:**
- Font: California
- Size: 14pt  
- Spacing: Double
- Margins: 1" all sides
- Body indent: 0.5" first line
- Word limits: 14,000 (opening/answering), 7,000 (reply)

---

## What Gets Formatted

### Heading Styles (LEGAL_H1 through LEGAL_H4)

**H1 - Main Sections:**
```
                    INTRODUCTION
```
- California, 14pt (FRAP) or 12pt (FRCP)
- Bold, all caps, centered
- Single-spaced

**H2 - Subsections:**
```
I. The District Court Erred
```
- California, same size
- Bold, left-aligned
- Single-spaced

**H3 - Sub-subsections:**
```
    A. Standard of Review
```
- California, same size
- Bold, indented 0.5"
- Single-spaced

**H4 - Paragraph headings:**
```
        1. First Point
```
- California, same size
- Italic, indented 1"
- Single-spaced

### Body Text Style (LEGAL_BODY)

```
    This is the body text. It is double-spaced with a 0.5" first-line
indent. All paragraphs use this style unless they are headings.
```
- California font
- Regular (not bold/italic)
- Double-spaced
- 0.5" first-line indent

---

## User Schema Fields

### Required

```json
{
  "_inherits_from": "MASTER_FRCP",
  
  "headings_in_my_document": [
    "INTRODUCTION",
    "ARGUMENT",
    "CONCLUSION"
  ]
}
```

### Optional Overrides

**Change Font:**

```json
"formatting_overrides": {
  "font": "Times New Roman"
}
```

**Change Size:**

```json
"formatting_overrides": {
  "font_size": "14pt"
}
```

**Custom Sections:**

```json
"custom_sections": {
  "conferral": {
    "heading_text": "LR 7-1 CONFERRAL NOTICE",
    "insert_after": "INTRODUCTION",
    "style": "LEGAL_H1",
    "enabled": true
  }
}
```

Then add to headings:

```json
"headings_in_my_document": [
  "INTRODUCTION",
  "LR 7-1 CONFERRAL NOTICE",
  "FACTUAL BACKGROUND",
  ...
]
```

---

## Taxonomy Integration

This skill integrates with Opus's comprehensive taxonomy system:

- `PimpJuice_instructions/taxonomy/build_manifest.json` - 14 filing types with build orders
- `PimpJuice_instructions/taxonomy/heading1_definitions.json` - Legal reasons for each section
- `PimpJuice_instructions/taxonomy/courts.json` - Court-specific formatting rules

The formatter uses these for validation and can be extended to auto-suggest sections based on filing type.

---

## Technical Details

### Text Preservation

Script **NEVER** modifies text content. It only:

1. Searches for heading text (case-insensitive match)
2. Applies style to paragraph (`<w:pStyle w:val="LEGAL_H1">`)
3. Leaves `<w:t>` nodes (text content) completely untouched

### No Subprocess

Uses `os.system()` only:
- Unpack: `python3 /mnt/skills/public/docx/ooxml/scripts/unpack.py`
- Pack: `python3 /mnt/skills/public/docx/ooxml/scripts/pack.py`

### Style Application

1. Adds custom LEGAL_ styles to `word/styles.xml`
2. Applies styles via paragraph properties in `word/document.xml`
3. Saves modified XML
4. Repacks to DOCX

---

## File Structure

```
pimp-formatting-skills/
├── SKILL.md                              # Skill metadata
├── LICENSE.txt                           # Apache 2.0
├── README.md                             # This file
├── scripts/
│   └── format_document.py               # Main formatter
└── PimpJuice_instructions/
    ├── MODEL_INSTRUCTIONS.md            # How Claude uses this
    ├── schemas/
    │   ├── MASTER_FRCP.json             # District defaults
    │   ├── MASTER_FRAP.json             # Appellate defaults
    │   ├── user_schema_template.json   # Template
    │   └── tyler_ninth_circuit_example.json  # Example
    └── taxonomy/
        ├── build_manifest.json          # Filing types
        ├── heading1_definitions.json    # Section defs
        ├── filing_types.json            # Simple types
        ├── courts.json                  # Court rules
        └── local_rules_override.json   # Cascading rules
```

---

## Examples

### Simple District Court Motion

```json
{
  "_inherits_from": "MASTER_FRCP",
  "headings_in_my_document": [
    "INTRODUCTION",
    "FACTUAL BACKGROUND",
    "LEGAL STANDARD",
    "ARGUMENT",
    "CONCLUSION"
  ]
}
```

**Run:** `python scripts/format_document.py my_schema.json draft.docx`

**Result:** 12pt California font, double-spaced, proper headings

### Ninth Circuit Brief

```json
{
  "_inherits_from": "MASTER_FRAP",
  "headings_in_my_document": [
    "JURISDICTIONAL STATEMENT",
    "STATEMENT OF ISSUES",
    "STATEMENT OF FACTS",
    "ARGUMENT",
    "CONCLUSION"
  ]
}
```

**Result:** 14pt California font, appellate formatting

---

## Troubleshooting

**"Missing headings" warning:**
- Check exact spelling in schema
- Headings are case-insensitive
- Underscores convert to spaces ("LEGAL_STANDARD" = "LEGAL STANDARD")

**Formatting not applied:**
- Make sure headings exist as actual text in document
- Script searches for exact text matches

**Want different font:**
- Add to `formatting_overrides`: `"font": "Your Font Name"`

---

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2024-12-20 | Initial with Opus taxonomy |
| 2.0.0 | 2024-12-21 | Schema inheritance system |
| 2.1.0 | 2024-12-21 | Fixed text preservation, proper skill structure |

---

**Built by Tyler A. Lofall for pro se litigants.**

**Stop getting dismissed. Start pimp smacking corruption with perfect formatting.**
