# Ninth Circuit Brief Formatter - Installation

## Quick Install

To install this skill so Claude can use it automatically:

```bash
# Copy to user skills directory
cp -r ninth-circuit-brief-formatter /mnt/skills/user/

# Or if you want to keep it elsewhere, use it directly:
cd ninth-circuit-brief-formatter
python scripts/formatter.py YOUR_BRIEF.docx
```

## Skill Structure

```
ninth-circuit-brief-formatter/
│
├── SKILL.md              ← Claude reads this to learn how to use the skill
├── LICENSE.txt           ← MIT License  
├── README.md             ← Human-readable documentation
│
└── scripts/              ← All the working code
    └── formatter.py      ← Main interactive formatter
```

## What Each File Does

### SKILL.md
- Claude reads this when you ask to format a brief
- Contains all the formatting rules
- Explains the interactive workflow
- Shows example XML for Word styles

### LICENSE.txt
- MIT License (Tyler's copyright)
- Allows free use, modification, distribution

### scripts/formatter.py
- Interactive Python script
- Phase 1: You classify sections (Heading1, Body, etc.)
- Phase 2: Claude suggests edits
- Outputs 2 Word files (formatted + with tracked changes)

## Usage Examples

### With Claude
```
User: "Format my Ninth Circuit brief using the formatter skill"
Claude: [Reads SKILL.md, runs scripts/formatter.py interactively]
```

### Standalone
```bash
python scripts/formatter.py my_brief.docx
```

## Testing

Try it on a sample section first:

```bash
# Create a test brief (just a few paragraphs)
# Run the formatter
python scripts/formatter.py test_brief.docx

# You'll be asked to classify each section
# Then optionally review for suggestions
# Output: test_brief_FORMATTED.docx + test_brief_WITH_EDITS.docx
```

---

**Ready to use!** The skill is complete and self-contained.
