---
name: ninth-circuit-brief-formatter
description: "Interactive Ninth Circuit appellate brief formatter. Use when Tyler needs to format legal briefs for the Ninth Circuit Court of Appeals with proper styles, spacing, and optional content review with tracked change suggestions."
license: MIT. See LICENSE.txt for details
---

# Ninth Circuit Brief Formatter

## When to Use This Skill

Use this skill when Tyler asks to:
- Format a Ninth Circuit appellate brief
- Apply Ninth Circuit court formatting rules
- Fix formatting on an existing legal brief  
- Review and suggest edits to brief content

## How This Skill Works

This is an **interactive Python script** (`scripts/formatter.py`) that runs in two phases.

### Phase 1: Classification
Run the script and it will show Tyler each section of his brief. Tyler decides what each section is:
- **H1**: Main heading (all caps, centered, bold) - e.g., "STATEMENT OF THE CASE"
- **H2**: Subheading (all caps, left-aligned, bold, Roman numerals) - e.g., "I. THE ARREST"
- **B**: Body text (normal case, double-spaced)
- **N**: Numbered paragraph (starts with 1., 2., 3., double-spaced)
- **S**: Skip (blank line or irrelevant section)

The script stores Tyler's classification for each section.

### Phase 2: Content Review (Optional)
After classification, the script asks Tyler if he wants content review. If yes:
- You (Claude) review each section Tyler classified
- Suggest improvements: grammar, clarity, legal terminology, citation format
- Tyler accepts or rejects each suggestion
- Accepted suggestions are inserted as Word tracked changes (deletions shown as red strikethrough, insertions shown as blue underline)

### Outputs
The script creates two Word files:
1. **{filename}_FORMATTED.docx** - Tyler's classifications applied with proper Ninth Circuit formatting
2. **{filename}_WITH_EDITS.docx** - Includes your suggestions as tracked changes (only if Tyler accepted any)

## Ninth Circuit Formatting Standards

### Font and Spacing
- Font: Century Schoolbook 14pt
- Body text: Double-spaced (line spacing = 2.0 or 480 twips)
- Headings: Single-spaced (line spacing = 1.0 or 240 twips)
- Margins: 1 inch on all sides

### Custom Styles Created
The script adds these Word XML styles:

**AppHeading1** (Main section headings)
- All caps, centered, bold
- 14pt Century Schoolbook
- Single-spaced
- No numbers

**AppHeading2** (Subsection headings)
- All caps, left-aligned, bold
- 14pt Century Schoolbook
- Single-spaced
- Roman numerals (I., II., III.)

**AppBody** (Body paragraphs)
- Normal case, left-aligned
- 14pt Century Schoolbook
- Double-spaced

**AppNumbered** (Numbered paragraphs)
- Normal case, left-aligned
- 14pt Century Schoolbook
- Double-spaced
- Starts with Arabic numbers (1., 2., 3.)

## Running the Script

```bash
cd /path/to/ninth-circuit-brief-formatter
python scripts/formatter.py /path/to/TYLERS_BRIEF.docx
```

The script will:
1. Unpack Tyler's .docx file to XML
2. Show each paragraph and prompt for classification
3. Save classifications to JSON
4. Ask if Tyler wants content review
5. If yes, prompt Tyler for each suggestion
6. Apply formatting based on classifications
7. Insert tracked changes for accepted suggestions
8. Pack XML back to .docx
9. Save both output files

## Content Review Guidelines

When reviewing Tyler's sections during Phase 2:

### What to Look For
- **Factual accuracy**: Don't suggest changes to facts Tyler has stated
- **Clarity**: Suggest rewording if something is confusing
- **Legal precision**: Improve legal terminology if needed
- **Citation format**: Flag missing or malformed citations (e.g., ECF references)
- **Conciseness**: Flag unnecessarily verbose passages
- **Grammar**: Fix grammatical errors

### What NOT to Do
- Don't add facts or details Tyler didn't include
- Don't add commentary or editorial opinions
- Don't suggest changes that alter Tyler's argument
- Don't rewrite entire paragraphs - suggest minimal targeted edits

### Suggestion Format
When suggesting edits in the script:
```python
{
    'original': 'the exact text to be replaced',
    'suggested': 'the new text to insert',
    'reason': 'brief explanation why'
}
```

Tyler will see: `Change "the exact text" → "the new text" (reason)`

## Technical Details

### Dependencies
- Python 3.x
- DOCX skill (OOXML manipulation library at `/mnt/skills/public/docx`)
- Access to `/mnt/skills/public/docx/ooxml/scripts/` for pack/unpack

### File Structure
```
scripts/formatter.py main functions:
- classify_sections(): Interactive classification phase
- review_and_suggest(): Content review phase  
- apply_formatting(): Apply styles to XML
- apply_tracked_changes(): Insert Word track changes for edits
- add_custom_styles(): Add AppHeading1, AppHeading2, AppBody styles to styles.xml
```

### Word XML Notes
- Tracked changes use `<w:del>` for deletions and `<w:ins>` for insertions
- Each tracked change includes `w:author="Claude"` and timestamp
- Styles are added to `word/styles.xml` before packing
- Paragraph properties (`<w:pPr>`) must follow element ordering rules per OOXML spec

## Important Reminders

1. **This is Tyler's brief**: You're helping format and polish, not rewriting
2. **Tyler makes all decisions**: Classification choices and suggestion acceptance are his calls
3. **Tracked changes are visible**: Tyler reviews all suggestions in Word before accepting
4. **Keep suggestions minimal**: Only mark text that actually changes, preserve unchanged text
5. **No mock suggestions**: If there's nothing to improve, say so - don't invent issues
