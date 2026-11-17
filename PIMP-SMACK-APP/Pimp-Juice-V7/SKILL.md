---
name: pimp-formatting-skills
description: Legal Document Formatter for Pro Se Litigants. Formats ANY legal document using taxonomy + jurisdiction profiles. Read PimpJuice_instructions/MODEL_INSTRUCTIONS.md first.
license: Apache-2.0
metadata:
  version: 2.1.0
  author: Tyler A. Lofall
  suite: pimp-formatting-skills
---

# Pimp Formatting Skills — Legal Document Formatter

## When to Use This Skill

Use this skill when Tyler needs to format a legal document:
- Format a motion for summary judgment
- Format a Ninth Circuit appellate brief  
- Format a complaint
- Format any legal filing with proper court formatting

## What This Does

**Automatically formats legal documents using schema inheritance:**

1. User creates simple schema listing their headings
2. Script inherits 95% of formatting from MASTER_FRCP.json or MASTER_FRAP.json
3. Script searches document for headings
4. Script applies proper formatting (fonts, spacing, styles)
5. Output = court-ready DOCX with ALL original text preserved

## Quick Start

### Step 1: Create User Schema

```bash
cd pimp-formatting-skills/PimpJuice_instructions/schemas
cp user_schema_template.json my_case.json
```

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

### Step 2: Run Formatter

```bash
python pimp-formatting-skills/scripts/format_document.py \
  my_case.json \
  rough_draft.docx
```

### Step 3: Get Formatted Doc

Output appears in `/mnt/user-data/outputs/` with timestamp.

## How It Works

### Schema Inheritance

```
MASTER_FRCP.json (district court defaults: 12pt, California font)
    OR
MASTER_FRAP.json (appellate defaults: 14pt, California font)
    ↓
USER_SCHEMA.json (only your headings list + any overrides)
    ↓
MERGED CONFIG (95% master + 5% user)
    ↓
FORMAT_DOCUMENT.PY (applies styles, preserves ALL text)
    ↓
FORMATTED DOCX (court-ready)
```

### What Gets Changed

- Heading styles (bold, caps, centered)
- Body text styles (font, size, spacing, indent)
- Only formatting properties in WordXML

### What Does NOT Get Changed

- **Your text content** (every word preserved exactly)
- **Tables, images, special formatting**
- **Document structure**

## File Structure

```
pimp-formatting-skills/
├── SKILL.md                              # THIS FILE
├── LICENSE.txt                           # Apache 2.0
├── README.md                             # Full documentation
├── scripts/
│   └── format_document.py               # Main formatter script
└── PimpJuice_instructions/
    ├── MODEL_INSTRUCTIONS.md            # How Claude should use this
    ├── schemas/
    │   ├── MASTER_FRCP.json             # District court defaults
    │   ├── MASTER_FRAP.json             # Appellate defaults
    │   └── user_schema_template.json   # Template to copy
    └── taxonomy/
        ├── build_manifest.json          # Filing types + build orders
        ├── heading1_definitions.json    # Section definitions
        └── courts.json                  # Court-specific rules
```

## Key Features

✅ Schema inheritance (user only specifies differences)  
✅ Preserves ALL text content (only changes formatting)  
✅ California font default (fallback: Century Schoolbook, Times New Roman)  
✅ H1-H4 hierarchy support  
✅ District (12pt) and Appellate (14pt) masters  
✅ Uses unzip/modify/rezip pattern (NO subprocess)  
✅ Works with taxonomy from Opus

## Master Schemas

**MASTER_FRCP.json** - District Court
- Font: California, 12pt
- Spacing: Double
- Margins: 1" all sides
- For: Motions, briefs, complaints

**MASTER_FRAP.json** - Court of Appeals  
- Font: California, 14pt
- Spacing: Double
- Margins: 1" all sides
- For: Appellate briefs
- Word limits: 14,000 (opening/answering), 7,000 (reply)

## Technical Details

### No Subprocess

Uses `os.system()` only:
- Unpack DOCX
- Pack DOCX

### Text Preservation

Script searches for headings by text match, applies style to paragraph, but NEVER modifies `<w:t>` nodes (text content).

### Style Application

Adds custom LEGAL_H1, LEGAL_H2, LEGAL_H3, LEGAL_H4, LEGAL_BODY styles to styles.xml, then applies to paragraphs via `<w:pStyle>`.

## Version History

| Version | Date | Changes |
|---------|------|---------|
| 1.0.0 | 2024-12-20 | Initial with Opus taxonomy |
| 2.0.0 | 2024-12-21 | Added schema inheritance system |
| 2.1.0 | 2024-12-21 | Fixed text preservation, proper skill structure |

## See Also

- `README.md` - Full documentation
- `PimpJuice_instructions/MODEL_INSTRUCTIONS.md` - How Claude uses this
- `scripts/format_document.py` - Main formatter code
