# Ninth Circuit Brief Formatter Skill

Interactive legal brief formatting tool for Ninth Circuit Court of Appeals.

## Installation

Copy this entire `ninth-circuit-brief-formatter` directory to `/mnt/skills/user/`

## Structure

```
ninth-circuit-brief-formatter/
├── SKILL.md           # Main skill documentation
├── LICENSE.txt        # MIT License
├── README.md          # This file
└── scripts/
    └── formatter.py   # Interactive formatter tool
```

## Usage

### From Claude

When you need to format a Ninth Circuit brief, tell Claude:

"Use the ninth-circuit-brief-formatter skill to format my brief"

Claude will read SKILL.md and use the tools in scripts/ to help you.

### Direct Usage

```bash
cd ninth-circuit-brief-formatter
python scripts/formatter.py YOUR_BRIEF.docx
```

## What It Does

1. **Phase 1: Classification** - You decide what each section is (Heading, Body, etc.)
2. **Phase 2: Review** - Claude suggests improvements as tracked changes
3. **Output** - Two Word files: formatted + with suggestions

## Requirements

- Python 3.x
- DOCX skill (for OOXML manipulation)
- Word for reviewing tracked changes

## License

MIT License - See LICENSE.txt
