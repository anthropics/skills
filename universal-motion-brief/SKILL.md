---
name: universal-motion-brief
description: Build motions and appellate briefs from user-supplied DOCX templates using JSON or XML data. Preserves user formatting; requires template with {{placeholders}}.
---

# Universal Motion & Brief Builder

## Purpose
Create motions or full briefs by merging structured data (JSON or XML converted to JSON) into a user-supplied `.docx` template. Footnotes and styling are preserved because the script only replaces placeholder text and does not regenerate the document layout.

## When to Use
- You already have a Word template (with styles/footers/footnotes) and want it filled from structured data.
- You want deterministic, non-generative assembly (no rewriting).
- You need separate runs for different documents (e.g., motion vs. brief) without mixing fields.

## Inputs Needed
1. `.docx` template with placeholder tokens like `{{CASE_NUMBER}}`, `{{FILING_TITLE}}`, `{{INTRO}}`, etc. (Do **not** place placeholders inside footnotes if you need to preserve them.)
2. JSON data file matching your placeholders. XML is fine if you convert to JSON first.
3. Optional: a mapping file if you want to reuse the same template with different field names.

## References
- `references/motion_schema.json`: Suggested keys for common motions.
- `references/brief_schema.json`: Suggested keys for appellate briefs (FRAP 28 ordering).
- `references/examples/` (add your own): Keep a good and a blank example to avoid drift.

## Script
Use `scripts/render_docx.py` to merge data into a DOCX template. It does plain placeholder replacement in paragraphs/runs and table cells; it leaves other content (headers/footers/footnotes) untouched.

### Usage
```bash
python scripts/render_docx.py \
  --template "path/to/your_template.docx" \
  --data "path/to/data.json" \
  --output "output.docx"
```

Options:
- `--mapping path/to/mapping.json` to remap data keys to template tokens (e.g., map `case_no` -> `CASE_NUMBER`).
- `--strict` to fail if any placeholder in the template is not resolved.

### Notes
- Placeholders must match `{{TOKEN}}` exactly (case-sensitive). Tokens in headers/footers may not be replaced; keep tokens in body where possible.
- Footnotes are preserved if you do not put placeholders inside them.
- Runs can split placeholders. The script reassembles run text to replace tokens, but keep tokens on one line to reduce surprises.
- If you need a fresh template, generate it from Word using styles; do **not** rely on this script to style content.

## Workflow
1. Copy your existing high-quality DOCX into your working directory (not tracked here to keep the skill ASCII-safe).
2. Add `{{placeholders}}` where text should be filled.
3. Prepare a JSON data file following `references/*_schema.json`.
4. Run the script (see above). Inspect the output in Word. If styles drift, adjust the template, not the script.
5. Keep two example data files per document type (one strong example, one minimal) to avoid degradation over time.

## Packaging
When ready to zip as a skill: `python ../skill-creator/scripts/package_skill.py .`

## Safety / Non-Goals
- No text generation or rewording—this is a copy/merge tool.
- Does not edit or remove footnotes; avoid placeholders in footnotes.
- Does not alter page setup, fonts, or numbering—your template controls all formatting.
