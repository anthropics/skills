# Materials Science Reader Standard Output Package

This contract turns a reader task into a reusable handoff folder. The package is
source-grounded first: no claim, figure idea, citation role, or review sentence
is promoted without a source anchor or an explicit missing-evidence flag.

## Package Layout

Required files for every package:

| Path | Status | Contract |
|---|---|---|
| `package_manifest.json` | required | Package metadata, source type, paper title, DOI or URL, generated time, required file list, handoff targets, and evidence boundary. |
| `source_map.json` | required | Stable source IDs such as `S001`, `C001`, `F001`, and `T001`, each tied to page, section, figure, table, excerpt, confidence, and missing evidence state. |
| `paper.md` | required | Reader-facing paper note with bibliographic metadata, source summary, claim-evidence-boundary rows, and source anchors. |
| `translation_notes.md` | required | Chinese interpretation notes when translation is requested; otherwise records that translation was not requested. |
| `source_anchor_checklist.md` | required | Checklist proving every core claim, figure/table card, citation row, and review handoff has an anchor or missing-evidence flag. |
| `figure_table_cards.md` | required | Figure and table cards with visual object ID, location, measured evidence, interpretation boundary, and reuse risk. |
| `mechanism_evidence_table.csv` | required | Claim-to-evidence mechanism table using stable source anchors and bounded inference language. |
| `dosage_window_table.csv` | required | Dosage, formulation, performance, and boundary rows. Empty packages keep headers only. |
| `citation_handoff.csv` | required | Citation matrix handoff rows for `materials-citation`. |
| `figure_handoff.csv` | required | Figure planning handoff rows for `materials-figure`. |
| `review_handoff.md` | required | Review-writing handoff with claim roles, evidence strength, missing evidence, and reviewer-risk notes. |
| `obsidian_note.md` | required | Obsidian-ready note with stable sections and source-grounded links. |
| `qa_report.md` | required | Audit report covering source coverage, figure/table coverage, citation handoff, figure handoff, missing evidence, overclaim risk, path leakage, and final status. |
| `assets/asset_manifest.md` | required | Asset inventory and local asset policy. |
| `assets/visual_asset_report.json` | required | Visual extraction/audit metadata. Empty packages use an empty `assets` list. |
| `assets/contact_sheet.png` | optional | Required only when visual crops or rendered pages are generated. |
| `assets/rendered_pages/` | optional | Required only for PDF/page-rendered workflows. |
| `reader.html` | optional | HTML reader view when generated. |
| `assets/crops/` | optional | Figure/table crops when extracted. |
| `assets/tables/` | optional | Table exports when extracted. |

## Required Fields

### `package_manifest.json`

Required fields: `package_type`, `skill_version`, `source_type`,
`paper_title`, `doi_or_url`, `generated_at`, `required_files`,
`handoff_targets`, and `evidence_boundary`.

Optional fields: `package_id`, `source_count`, `asset_count`, `warnings`,
`builder`, and `notes`.

### `source_map.json`

Required fields: `schema_version`, `source_type`, `paper_title`,
`doi_or_url`, and `sources`.

Each source row requires `source_id`, `source_kind`, `source_location`,
`source_anchor`, `original_excerpt`, `evidence_layer`, `evidence_type`,
`certainty_tier`, `confidence_label`, and `missing_evidence_flag`.

Optional fields: `section`, `page`, `figure_id`, `table_id`,
`chinese_interpretation`, `claim_id`, `reviewer_risk`, `caption_boundary`,
and `notes`.

### Markdown Files

`paper.md` requires sections for metadata, source summary, claim evidence
boundary, figure/table notes, and missing evidence. `translation_notes.md`
requires translation status and notes. `source_anchor_checklist.md` requires
claim, citation, figure, review, and missing-evidence checks.
`figure_table_cards.md` requires figure cards, table cards, and visual risk
boundaries. `review_handoff.md` requires review claim roles, mechanism
boundaries, missing evidence, and reviewer risk. `obsidian_note.md` requires
`## Source Anchors`, `## Evidence Chain`, `## Figure And Table Cards`,
`## Citation Handoff`, `## Figure Handoff`, `## Review Handoff`, and
`## QA Flags`.

### CSV Files

`mechanism_evidence_table.csv` requires `claim_id`, `source_anchor`,
`source_location`, `original_excerpt`, `evidence_layer`, `evidence_type`,
`mechanism_interpretation`, `boundary_note`, `certainty_tier`,
`confidence_label`, and `missing_evidence_flag`.

`dosage_window_table.csv` requires `claim_id`, `source_anchor`,
`material_system`, `dosage_or_ratio`, `performance_metric`, `measured_value`,
`test_condition`, `workability_or_stability`, `boundary_note`, and
`missing_evidence_flag`.

`citation_handoff.csv` requires `claim_id`, `source_anchor`,
`source_location`, `original_excerpt`, `evidence_layer`, `evidence_type`,
`source_role`, `source_quality`, `certainty_tier`, `citation_role`,
`reviewer_risk`, `missing_evidence_flag`, and `handoff_target`.

`figure_handoff.csv` requires `claim_id`, `source_anchor`,
`source_location`, `original_excerpt`, `evidence_layer`, `evidence_type`,
`figure_archetype`, `asset_id`, `caption_boundary`, `reviewer_risk`,
`certainty_tier`, `missing_evidence_flag`, and `handoff_target`.

## Source-Type Requirements

| Source type | Mandatory package files | Additional expectation |
|---|---|---|
| `pasted-text` | All required files above | Page anchors may be section anchors if pages are unknown. |
| `doi` or `html` | All required files above | DOI/URL must be recorded in manifest and source map. |
| `full-pdf` | All required files above | Figure/table cards should use page or figure/table anchors; rendered pages are optional until extraction is requested. |
| `wer-ea-mini-review` | All required files above | Citation, figure, and review handoff files must preserve mechanism evidence boundaries and missing-evidence flags. |

## QA Report Contract

`qa_report.md` must include these sections:

- `## Source Coverage`
- `## Figure/Table Coverage`
- `## Citation Handoff`
- `## Figure Handoff`
- `## Missing Evidence`
- `## Overclaim Risk`
- `## Absolute Path Leakage`
- `## Final Status`

## Asset Contract

`assets/asset_manifest.md` is required even when no assets have been extracted.
`assets/visual_asset_report.json` is required and must contain
`schema_version`, `package_type`, `assets`, `warnings`, and `qa_status`.
Visual asset specs and reports must keep caption boundaries separate from
measured evidence.
