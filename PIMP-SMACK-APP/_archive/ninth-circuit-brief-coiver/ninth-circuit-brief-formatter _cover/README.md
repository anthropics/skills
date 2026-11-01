# Ninth Circuit Cover Page Generator

Generates perfect Ninth Circuit Court of Appeals cover pages from a template.

## Installation

Copy this entire directory to `/mnt/skills/user/`

## Structure

```
ninth-circuit-brief-formatter/
├── SKILL.md                  # Skill instructions for Claude
├── LICENSE.txt               # MIT License
├── README.md                 # This file
├── CAPTION_NINTH.docx        # Perfect template (never modified)
└── scripts/
    ├── generate_cover.py     # Cover page generator (WORKS)
    └── formatter.py          # Full brief formatter (future)
```

## Usage

### From Claude

Tell Claude: "Generate a Ninth Circuit cover page"

Claude will read SKILL.md and run `scripts/generate_cover.py` interactively.

### Direct Usage

```bash
cd ninth-circuit-brief-formatter
python scripts/generate_cover.py
```

You'll be prompted for case number, filing name, and judge name.

## What It Does

1. Uses CAPTION_NINTH.docx as a read-only template
2. Prompts for case details
3. Performs string replacement in Word XML
4. Outputs timestamped cover page

## Output

Creates: `COVER_PAGE_YYYYMMDD_HHMMSS.docx`

Ready to use immediately - perfect Ninth Circuit formatting.

## Requirements

- Python 3.x
- DOCX skill (for OOXML manipulation)
- Word for reviewing tracked changes

## License

MIT License - See LICENSE.txt
