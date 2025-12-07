---
name: ninth-circuit-cover
description: "Generate Ninth Circuit Court of Appeals cover pages. This skill should be used when creating cover pages for appellate briefs, motions, or other filings in the Ninth Circuit. Requires case number, filing type, and judge name."
---

# Ninth Circuit Cover Page Generator

## Overview

Generate properly formatted cover pages for Ninth Circuit filings. The cover page is created from a master template with placeholders replaced by case-specific information.

## When to Use

- Creating a cover page for an appellate brief
- Creating a cover page for a motion
- Any Ninth Circuit filing that requires a caption page

## Required Information

1. **Case Number** - Ninth Circuit case number (e.g., `25-6461`)
2. **Filing Name** - Document title (e.g., `APPELLANT'S OPENING BRIEF`, `MOTION FOR STAY PENDING APPEAL`)
3. **Judge Name** - District court judge name (e.g., `Stacy Beckerman`)

## Workflow

To generate a cover page:

```bash
python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\COVER_GENERATOR_COMPLETE\generate_cover.py" --case "CASE_NUMBER" --filing "FILING_NAME" --judge "JUDGE_NAME"
```

### Example

```bash
python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\COVER_GENERATOR_COMPLETE\generate_cover.py" --case "25-6461" --filing "APPELLANT'S OPENING BRIEF" --judge "Stacy Beckerman"
```

### Output

- File is saved to: `COVER_GENERATOR_COMPLETE/output/`
- Naming convention: `Case_[number]_[filing]_[date].docx`
- If file exists, adds `_1`, `_2`, etc. suffix

### Optional Arguments

- `--output "filename.docx"` - Custom output filename
- `--template "path/to/template.docx"` - Use different template

## Common Filing Names

- `APPELLANT'S OPENING BRIEF`
- `APPELLANT'S REPLY BRIEF`
- `APPELLEE'S ANSWERING BRIEF`
- `MOTION FOR STAY PENDING APPEAL`
- `MOTION FOR EXTENSION OF TIME`
- `EMERGENCY MOTION`

## CRITICAL RULES

1. **DO NOT** modify the template file `TEMPLATE_CAPTION.docx`
2. **DO NOT** edit the generated output - regenerate if changes needed
3. **ALWAYS** use the exact case number format (XX-XXXXX)
4. **ALWAYS** use UPPERCASE for filing names
