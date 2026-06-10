# PIMP SMACK Formatting Scripts

Central location for ALL document formatting scripts, templates, and court profiles.

## Directory Structure

```
_formatting/
├── python/                      # Python formatters
│   ├── format_document.py       # MAIN - Full DOCX formatter with court schemas
│   ├── document_builder.py      # Declaration/document builder (DOCX)
│   ├── generate_cover.py        # Ninth Circuit cover page generator
│   ├── render_docx_from_legalxml.py  # LegalXML → DOCX converter
│   ├── extract_docx_blocks.py   # Extract blocks from existing DOCX
│   ├── validate_docx.py         # Validate DOCX formatting
│   ├── template_generator.py    # Template-based generation
│   └── pimp_collector.py        # Case data extraction/persistence
│
├── typescript/                  # TypeScript (React GUI)
│   └── docxService.ts           # Browser-based DOCX generation
│
├── jurisdictions/               # Court-specific profiles
│   ├── courts.json              # All court formatting rules
│   ├── local_rules_override.json
│   └── local_rules_override.schema.json
│
├── templates/                   # DOCX templates
│   └── TEMPLATE_CAPTION.docx    # Ninth Circuit cover template
│
├── COVER_GENERATOR_GUIDE.md     # How to use cover generator
└── GENERATE_COVER.bat           # Windows batch for cover gen
```

## Quick Start

### Format Existing DOCX (Python)
```bash
python _formatting/python/format_document.py schema.json input.docx output.docx
```

### Convert Text to DOCX
```bash
python _formatting/python/format_document.py --from-text input.txt output.docx
```

### Create New Brief Template
```bash
python _formatting/python/format_document.py --new-brief output.docx
```

## Script Purposes

| Script | Purpose | Input | Output |
|--------|---------|-------|--------|
| `format_document.py` | Apply legal formatting | DOCX/TXT | Formatted DOCX |
| `document_builder.py` | Build declarations | Data | DOCX |
| `render_docx_from_legalxml.py` | Convert semantic XML | XML | DOCX |
| `validate_docx.py` | Check formatting | DOCX | Report |
| `template_generator.py` | Fill templates | JSON + Template | DOCX |
| `pimp_collector.py` | Extract case data | DOCX/TXT | JSON |

## Court-Specific Formatting

Formatting rules are defined per jurisdiction:
- **Ninth Circuit**: Century Schoolbook 14pt, double-spaced
- **District Courts**: Times New Roman 12pt, double-spaced
- **Clackamas County**: Times New Roman 12pt

Court profiles are in: `PimpJuice_instructions/jurisdictions/courts.json`

## Dependencies

```bash
pip install python-docx
```
