---
name: ninth-circuit-cover-generator
description: "Generates Ninth Circuit Court of Appeals cover pages using a perfect template. Use when Tyler needs to create a cover page for an appellate brief, motion, or other filing."
license: MIT. See LICENSE.txt for details
---

# Ninth Circuit Cover Page Generator

## When to Use This Skill

Use this skill when Tyler asks to:
- Generate a Ninth Circuit cover page
- Create a caption page for an appellate brief
- Make a cover for a motion or other filing

## What This Does

Generates a perfectly formatted Ninth Circuit cover page by:
1. Using `CAPTION_NINTH.docx` as a read-only template (never modifies the template)
2. Prompting for: Case Number, Filing Name, Judge Name
3. Performing string replacement in the Word XML
4. Outputting a timestamped .docx file

## Running the Script

### Interactive Mode (recommended)
```bash
cd ninth-circuit-cover-generator
python scripts/generate_cover.py
```

You'll be prompted for:
- **Case Number**: e.g., `24-1234` or `3:24-cv-00839-SB`
- **Filing Name**: e.g., `APPELLANT'S OPENING BRIEF` (will be converted to all caps)
- **Judge Name**: e.g., `Hon. Susan Brnovich`

### Command Line Mode
```bash
python scripts/generate_cover.py "24-1234" "APPELLANT'S OPENING BRIEF" "Hon. Susan Brnovich"
```

## Output

Creates: `COVER_PAGE_YYYYMMDD_HHMMSS.docx`

The output file has:
- Perfect Ninth Circuit formatting (already in template)
- Your case number, filing name, and judge name inserted
- Ready to use immediately

## Template Requirements

The script looks for `CAPTION_NINTH.docx` in the same directory. This template must contain these placeholder strings:
- `[CASE_NUMBER]` - Replaced with case number
- `[FILING_NAME]` - Replaced with filing name  
- `[JUDGE_NAME]` - Replaced with judge name

**IMPORTANT**: The template file is NEVER modified. It's copied first, then the copy is modified.

## Technical Details

### How It Works
1. Copies template to output file with timestamp
2. Unzips .docx (it's a ZIP archive)
3. Opens `word/document.xml`
4. Performs string replacement on placeholders
5. Rezips to create final .docx

### Why This Approach
- **No python-docx dependency** - uses native ZIP handling
- **Preserves perfect formatting** - template stays pristine
- **Fast and reliable** - simple string replacement
- **No corruption risk** - template is read-only

## Files in This Skill

```
scripts/
├── generate_cover.py    - Cover page generator
└── formatter.py         - (Future) Full brief formatter
```

## Usage Tips

1. **Keep template safe**: Never edit CAPTION_NINTH.docx directly
2. **Reuse output**: Generated covers can be copied/modified
3. **Batch generation**: Run script multiple times for different filings
4. **Verify output**: Always open generated file to confirm before filing
