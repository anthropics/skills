---
name: pimp-formatting-skills
description: Legal Document Formatter for Pro Se Litigants. Uses taxonomy + jurisdiction profiles to format legal documents (structure + styling) without rewriting content.
license: Apache-2.0 (see LICENSE.txt)
allowed-tools: []
metadata:
  version: 2.1.0
  author: Tyler A. Lofall
  suite: pimp-formatting-skills
---

# pimp-formatting-skills — Legal Document Formatter

## READ FIRST (required)
Open these files **in this exact order**:

1. `pimp-formatting-skills_instructions/MODEL_INSTRUCTIONS.md`
2. `pimp-formatting-skills_instructions/taxonomy/build_manifest.json`
3. `pimp-formatting-skills_instructions/taxonomy/heading1_definitions.json`
4. `pimp-formatting-skills_instructions/jurisdictions/courts.json`

---

## What this skill does
This is a **FORMATTER** — not a drafter.

It:
- Enforces document **structure** (sections, ordering) by filing type.
- Applies **jurisdiction-specific formatting** (fonts, margins, spacing) using court profiles.
- Produces a deterministic build plan + XML + validation report.

It does **not**:
- Write arguments, add facts, or choose strategy.
- Provide legal advice.

---

## Package layout (fixed; compatible with skill loaders)
```
pimp-formatting-skills/
├── SKILL.md
├── LICENSE.txt
└── pimp-formatting-skills_instructions/
    ├── .readme
    ├── MODEL_INSTRUCTIONS.md
    ├── master_config.json
    ├── taxonomy/
    │   ├── build_manifest.json
    │   ├── filing_types.json
    │   └── heading1_definitions.json
    ├── jurisdictions/
    │   ├── courts.json
    │   ├── local_rules_override.json
    │   └── local_rules_override.schema.json
    ├── scripts/
    │   ├── extract_docx_blocks.py
    │   ├── render_docx_from_legalxml.py
    │   └── validate_docx.py
    ├── examples/
    │   └── LEGALDOC_example.xml
    └── references/
        ├── master_instructions_plan.md
        ├── skill_creator_example_SKILL.md
        └── XProc_3.1_An_XML_Pipeline_Language.mhtml
```

---

## Quick reference
### Filing types (14)
`MOTION`, `BRIEF`, `APPELLATE_BRIEF`, `COMPLAINT`, `ANSWER`, `DECLARATION`, `NOTICE`, `ORDER`, `STIPULATION`, `DISCOVERY`, `EXHIBIT`, `JUDGMENT`, `LETTER`, `SUBPOENA`

### XML style tokens (semantic)
- `LEGAL_CAPTION`
- `LEGAL_TITLE`
- `LEGAL_H1`, `LEGAL_H2`, `LEGAL_H3`
- `LEGAL_BODY`

---

## Notes
- **Local rules and judge-specific standing orders control** in most district courts; the included profiles are defaults.
- Appellate formatting relies on **FRAP 32** baselines plus any circuit local rules reflected in `courts.json`.
