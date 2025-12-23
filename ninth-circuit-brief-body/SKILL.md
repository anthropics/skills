---
name: ninth-circuit-brief-body
description: "Generate Ninth Circuit appellate brief body sections. This skill should be used when assembling brief sections (jurisdictional statement, issues presented, statement of case, argument, etc.) from evidence and facts. Each section is built separately and assembled into a complete brief. NO REWORDING of source material."
---

# Ninth Circuit Brief Body Generator

## Overview

Assemble appellate brief sections from evidence pool data. Each section is generated separately, validated, then combined. **CRITICAL: All text comes from source files - NO AI rewording.**

## Brief Sections (FRAP 28 Order)

| #   | Section                   | Required | Source                                  |
| --- | ------------------------- | -------- | --------------------------------------- |
| 1   | Corporate Disclosure      | Yes*     | `case_info.json`                        |
| 2   | Table of Contents         | Yes      | Auto-generated                          |
| 3   | Table of Authorities      | Yes      | `authorities.json`                      |
| 4   | Jurisdictional Statement  | Yes      | `case_info.json`                        |
| 5   | Issues Presented          | Yes      | `issues_presented.json`                 |
| 6   | Statement of the Case     | Yes      | `evidence_pool.json`                    |
| 7   | Summary of Argument       | Yes      | `arguments.json`                        |
| 8   | Argument                  | Yes      | `evidence_pool.json` + `arguments.json` |
| 9   | Conclusion                | Yes      | Template                                |
| 10  | Certificate of Compliance | Yes      | Word count                              |
| 11  | Certificate of Service    | Yes      | Template                                |

*Pro se appellants exempt from corporate disclosure

# Ninth Circuit Brief Body Generator

Teach the model to load the master fact set, stitch every FRAP-required section, and emit a DOCX that already lives in the dual-copy OUTBOX workflow. All prose remains verbatim from the JSON sources—no paraphrasing, no “improvements.”

## When to Trigger This Skill


## Files and References to Load

1. `legal_brief_system/data/*.json` – case data, issues, authorities, argument content, evidence pool, timeline. See `references/data-map.md` for a full schema.
2. `legal_brief_system/assemble_brief.py` – use when you need section-specific plain text output or to confirm which facts are mapped.
3. `legal_brief_system/templates/BRIEF_SHELL.md` – marker list for every section inside the DOCX.
4. `references/frap_rules.md` – FRAP 28/32 compliance checklist.
5. `legal_brief_system/NO_REWORDING_RULES.md` – guardrail: read before issuing any generation prompts.

## Workflow (Single Agent, Repeatable)

1. **Prep the data (no drafting here).**
    - Update `case_info.json`, `issues_presented.json`, `arguments.json`, `argument_content.json`, `authorities.json`, `timeline.json`, `evidence_pool.json`.
    - Tag each fact in `evidence_pool.json` with the correct `used_in_sections` keys (`statement_of_case`, `argument_I`, `argument_I_A`, etc.).
2. **Validate before touching output.**
    ```powershell
    python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\legal_brief_system\validate_brief.py"
    ```
    Resolve any missing fields or malformed JSON before continuing.
3. **Preview the evidence flow.**
    ```powershell
    python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\legal_brief_system\build_from_evidence.py"
    ```
    Inspect the generated TXT in `legal_brief_system/output/BRIEF_REVIEW_*.txt` to confirm each fact + footnote chain is correct.
4. **Generate the DOCX (with dual OUTBOX copies).**
    ```powershell
    python "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\legal_brief_system\generate_brief.py" ^
      --outbox-dir "d:\Nineth Circuit\CLAUDE_COPILOT HLP\NINTH CIR5\OUTBOX"
    ```
    - Reads every JSON file, injects the exact text into the DOCX, and writes the first copy to `legal_brief_system/output/`.
    - Automatically writes `{Case}-{Filing}-{timestamp}.docx` to `OUTBOX/briefs/` and a read-only chronological copy to `OUTBOX/chronological/`.
    - Use `--skip-outbox` only when explicitly sandboxing; production runs must keep the dual-copy rule.
5. **Post-generation checklist.**
    - Open the DOCX and verify each section matches the JSON source (no paraphrasing drift).
    - Update TOC page numbers after final pagination.
    - Insert the precise word count in the Certificate of Compliance.
    - Export to PDF and combine with the cover page if filing immediately.

## Section-to-Source Mapping

| Section | Source | Notes |
| --- | --- | --- |
| Disclosure | `case_info.json` | Uses pro se exemption text unless a custom block exists. |
| Table of Contents | Auto-generated | Pulls headings + subheadings from `arguments.json`. |
| Table of Authorities | `authorities.json` | Alphabetized; relies on `pages_cited`. |
| Introduction | `argument_content.json > content_sections.introduction` | Draft text must already be present; the script will not invent prose. |
| Jurisdiction | `case_info.json > jurisdiction` | Includes statutes, judgment date, NOA date. |
| Issues Presented | `issues_presented.json` | Each issue prints verbatim. |
| Statement of the Case | `evidence_pool.json` facts tagged with `statement_of_case` (falls back to `timeline.json` only if none are tagged). |
| Summary of Argument | `argument_content.json > content_sections.summary_of_argument` | Keep concise; mirrors argument structure. |
| Standard of Review | `issues_presented.json` | Groups issues by identical standards. |
| Argument I/II/III | Combination of `argument_content.json` and `evidence_pool.json` facts tagged with `argument_*` keys. |
| Conclusion | `case_info.json > conclusion.text` or default relief paragraph. |
| Statement of Related Cases | `case_info.json > related_cases[]` (optional list). |
| Certificates | Auto text + `case_info.json` signature block; fill in word count manually. |

## Guardrails: Exact Text Only

- Never summarize or “improve” facts. If a change is needed, edit the JSON source and regenerate.
- When adding a new fact:
  1. Insert it into `evidence_pool.json` with `statement`, `record_cite`, and `used_in_sections` keys.
  2. If the fact should appear in multiple arguments, list every relevant `argument_*` tag.
  3. Re-run validation and regeneration.
- When drafting substantive narrative (Intro, Summary, subarguments), always write directly into `argument_content.json`. The generator copies the text verbatim.
- Keep FRAP/9th Cir formatting rules handy via `references/frap_rules.md` and ensure fonts, spacing, and citations remain compliant.

## Troubleshooting

- **Missing section text?** Confirm the corresponding JSON field exists and is tagged. Example: If Argument II.B is blank, ensure facts include `"argument_II_B"` and that `argument_content.json` has `content_sections.arguments["II"].B.content` filled.
- **No OUTBOX copy?** You likely passed `--skip-outbox` or the OUTBOX path is wrong. Re-run with the correct `--outbox-dir`.
- **Table of Authorities gaps?** Add the new authority to `authorities.json` with `bluebook` and `pages_cited`. Re-run the generator.

## References

- `references/data-map.md` – exhaustive list of required data files and `used_in_sections` keys.
- `legal_brief_system/templates/MOTION_SHELL.md` – FRAP 27 motion template with program-fill placeholders.
- `references/motion-template-guide.md` – automation steps for populating the motion shell.
- `legal_brief_system/generate_motion.py` – CLI to render motions via the block library.
- `references/frap_rules.md` – FRAP 28/32 requirements and Ninth Circuit nuances.
- `legal_brief_system/templates/BRIEF_SHELL.md` – Word marker definitions for every section.
- `references/frap_rules.md` - FRAP formatting requirements
