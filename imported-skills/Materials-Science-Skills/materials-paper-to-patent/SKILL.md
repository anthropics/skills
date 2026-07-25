---
name: materials-paper-to-patent
description: Convert materials science papers, theses, technical reports, figures, or research manuscripts into evidence-grounded Chinese invention patent drafts. Use when an AI agent must extract patentable technical contributions, map every claimed feature to source evidence, preserve core formulas as editable Office Math, generate claim-aligned flowcharts, validate claims against a civil patent knowledge base (patent_kb.yaml), compare a paper with an existing patent, audit support and consistency, or deliver separate Chinese DOCX files for claims, specification, abstract, and abstract figure. Default invention type is process-material.
---

# Materials Paper to Chinese Patent

Read `manifest.yaml` and every `always_load` file. Apply profile-first routing,
detect the `source_format`, `task_mode`, and `invention_type` axes, state the
detected values in one line, and load only the selected fragments and keyed
on-demand references.

## Evidence Boundary

Inspect the complete substantive source; stop if it cannot be inspected.
Create stable P/E/F/C source IDs. Use only `explicit`, `inherent`,
`needs-confirmation`, and `unsupported` support states. Unsupported features
never enter formal claims. Turn needs-confirmation features into specific
inventor questions outside claims, and do not invent legal or inventor facts.
Across disclosure analysis and formal drafting, unresolved needs-confirmation
items or inventor questions force overall status `incomplete-draft`; do not
use `review-draft` or completed package status.

## Route

- `disclosure-analysis`: build the source map, inventories, and evidence
  ledger without claims or specification; do not load `patent-kb` or
  `output-contract`.
- Before any formal claim or claim audit, load `patent-kb`, `stage-gates`, and
  `claim-checklist`; load `cn-drafting-guide` for Chinese drafting.
- `claim-set`: follow the detailed gates through claims and preserve every
  claim-to-source mapping.
- `full-draft`: also load `output-contract` and `draft-schema`, then complete
  every detailed gate. Consume `reader-package` and `figure-handoff` when
  supplied.
- `paper-patent-audit`: load `corpus-pair-audit`; load the formal-claim
  references above whenever claims are audited.

Formal claims, specification, abstract, figure labels, and descriptions are
Chinese. Preserve source-supported formulas as editable Office Math, disclosed
ranges and units, claim-aligned figures, and the output semantics declared by
the selected fragments and references.

## Validate and Hand Off

Run `validate_patent_draft.py`, `validate_patent_claims.py` with the detected
invention type, and `build_patent_package.py`. Resolve every `ERROR`, review
warnings against the source, and label blocking gaps `incomplete-draft`.
Emit the named `patent-draft-handoff` route to `materials-research` with the
validated artifact paths and status; formal shared schema wiring is external
to this router. The package is a drafting aid, not a legal opinion or filing
guarantee.
