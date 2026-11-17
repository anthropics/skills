---
name: pro-se-formatter-taxonomy
description: Filing-type taxonomy used by the pro-se formatter suite (framework-only baseline + separate sourced-rules workspace).
license: Apache-2.0 (see LICENSE)
allowed-tools: []
metadata:
  suite: pro-se-formatter-suite
  role: taxonomy
---

# Pro Se Formatter Suite — Taxonomy

WE.[READ FIRST]
- Read `pro-se-formatter-taxonomy_instructions/.readme` first.
- Treat this taxonomy as **framework-only** until jurisdiction sources are attached.

WE.[FILES]
- Baseline filing types (+ default H1 headings per type): `pro-se-formatter-taxonomy_instructions/filing_types_federal_baseline.json`
- Rules workspace template (populate from cited sources; keep baseline unchanged): `pro-se-formatter-taxonomy_instructions/rules_workspace_federal_template.json`
- Optional reference (legacy glossary/back-compat): `pro-se-formatter-taxonomy_instructions/heading1_groups_baseline.json`

WE.[NON-NEGOTIABLES]
- Local rules/certs: use cited sources.
- Evidence UID system: preserve UIDs exactly as provided.

This skill provides a baseline filing taxonomy (framework-only) plus a separate workspace file where extracted jurisdiction requirements can be recorded with citations.

Primary files live in `pro-se-formatter-taxonomy_instructions/`.
