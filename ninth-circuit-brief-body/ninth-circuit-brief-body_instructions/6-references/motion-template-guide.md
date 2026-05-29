# Motion Template Automation Guide

This guide explains how to feed the FRAP 27 motion template (`legal_brief_system/templates/MOTION_SHELL.md`) with data so that a single LLM agent can generate ready-to-file motions without editing the template directly.

## 1. Data Sources

| File | Purpose | Key Fields |
| --- | --- | --- |
| `legal_brief_system/data/case_info.json` | Caption, party labels, signature block, contact info | `case_number`, `caption`, `signature`, `contact_block` |
| `legal_brief_system/data/argument_content.json` | Narrative paragraphs for each motion type | `motions[].arguments[]`, `motions[].legal_standard` |
| `legal_brief_system/data/evidence_pool.json` | Fact paragraphs with cites | Facts tagged `"used_in_sections": ["motion_facts", "motion_I"]` |
| `legal_brief_system/data/timeline.json` | Chronological events for urgency | Add `"used_in_sections": ["motion_timeline"]` when needed |
| `legal_brief_system/templates/motion_blocks/*.md` | Building-block markdown snippets | Inputs listed in `MOTION_SHELL.md` block table |
| `legal_brief_system/motions/<key>/inputs/config.json` | Motion-specific metadata + block sequence | `motion_key`, `block_sequence`, block inputs |
| Case-law banks (e.g., `templates/CaseLaw_1100pp.docx`, `templates/CaseLaw_1093pp.docx`) | Source text for authorities/excerpts | Export chosen text into `argument_content.json` prior to generation |

## 2. Generation Steps

1. **Select Motion Type** – define JSON payload (see `MOTION_SHELL.md`) with motion title, relief list, emergency basis, citations, attachments, and the `block_sequence` array describing the order of sections.
2. **Collect Facts** – query `evidence_pool.json` for entries tagged to the motion, preserving their `statement` + `record_cite` verbatim. Map them to `motion_facts[]` or more specific tags (e.g., `motion_I_A`).
3. **Assemble Block Inputs** – fill `legal_standard`, `jurisdiction_blocks`, `arguments[]`, and any other block-specific objects. Each argument item should include `heading`, `text`, optional `footnotes`.
4. **Render Blocks** – for every slug in `block_sequence`, load the matching file from `templates/motion_blocks/`, substitute the data, and append the result. Feed the concatenated markdown into the same renderer used for `BRIEF_SHELL.md` (Pandoc or python-docx). No ad-libbing.
5. **Attach Required Exhibits** – verify each file in `attachments[]` exists; zip PDFs with the motion if filing electronically.
6. **Copy Outputs** – save the DOCX/PDF into the motion's `outputs/` folder and duplicate into `OUTBOX/motions/` and `OUTBOX/chronological/` with timestamps.

## 3. Read-Only Enforcement

- Set `MOTION_SHELL.md` to read-only at the OS level (`attrib +R` on Windows) after inspection.
- Store edits only in the JSON data files to maintain provenance and simplify regeneration. When a new structure is needed, add a block file and reference it via `block_sequence` rather than rewriting existing blocks.

## 4. LLM Guardrails

- **No paraphrasing** – always cite text pulled from the evidence or case-law banks.
- **No mixed relief** – file separate motions when requesting both procedural and substantive relief.
- **Log actions** – append each generation run (motion type, timestamp, files produced) to `OUTBOX/chronological/motion-log.json` for auditing.

## 5. Future Automation Hooks

- Use `python legal_brief_system/generate_motion.py --motion-key <key>` to render a motion from `legal_brief_system/motions/<key>/inputs/config.json`. The script writes to the motion's `outputs/` folder and mirrors the file into `OUTBOX/motions/` and `OUTBOX/chronological/`, updating `motion-log.json` automatically.
- Implement cite-checks by cross-referencing `authorities.json`; warn when a cited case is missing.
- Sample large pleadings (1100/1093-page sets) by indexing them into a retrieval system; copy chosen paragraphs into `argument_content.json` for deterministic output.
