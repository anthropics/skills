# Evidence-To-Review Handoff

Use this reference when a paper reading package must feed a mini-review, citation matrix, or review figure without losing source traceability.

## Source-map-first workflow

Start every handoff from a source map, even when the source is incomplete.

- PDF: anchor to page, section, figure/table label, excerpt, and visual asset status. If the PDF can be rendered, connect the row to the matching figure/table card and asset file.
- DOI/HTML: anchor to DOI or URL, section heading, paragraph or figure/table label, access date if needed, and copied excerpt.
- pasted text: anchor to user-provided source label, section heading or pasted-text block, excerpt, and a note that page/figure verification is missing.

Every borrowable claim must have a `source_anchor`, `source_location`, `original_excerpt`, `confidence_label`, and `missing_evidence_flag`. Do not create citation or figure rows from memory-only impressions.

## Output contract

When the user requests WER-EA mini-review extraction, source-map-first reading, citation handoff, figure handoff, evidence-to-review handoff, or reviewer-safe review assets, produce these files when the evidence exists:

- `source_map.json`
- `source_anchor_checklist.md`
- `citation_handoff.csv`
- `figure_handoff.csv`
- `review_handoff.md`
- `figure_table_cards.md`

If a file cannot be completed, keep the file name in the package and mark why with `[source missing]`, `[page not verified]`, `[figure not inspected]`, `[mechanism inferred]`, or `[not review-figure safe]`.

## Shared required fields

The citation and figure handoff tables must use these shared fields:

| Field | Required meaning |
|---|---|
| `claim_id` | Stable row ID linked to paper notes, source map, and downstream tables. |
| `source_anchor` | Stable source ID such as `EX-001`, `F001-01`, `T001-01`, `M001-01`, or `D001-01`. |
| `source_location` | Page, section, figure/table label, DOI/HTML section, or pasted-text block. |
| `original_excerpt` | Short exact excerpt or caption/table text that supports the row. |
| `measured_evidence` | What was directly measured or reported. |
| `inferred_mechanism` | Mechanism interpretation, or `[none]` when the source does not support one. |
| `boundary_or_missing_test` | Limitation, missing test, unsupported generalization, or condition boundary. |
| `citation_role` | central WER-EA evidence, adjacent modifier evidence, method evidence, durability gap, background, or caution. |
| `evidence_type` | primary experimental, review, method, standard/specification, field/service, or weak background. |
| `figure_archetype` | mechanism map, evidence heatmap, dosage window, test-method comparison, performance-mechanism boundary, screening flow, or none. |
| `reviewer_risk` | Main reviewer concern if the row is overused. |
| `handoff_target` | `materials-citation`, `materials-figure`, `review_handoff`, or `table_system`. |

Also include:

- `confidence_label`: high / medium / low, based on source completeness and directness.
- `missing_evidence_flag`: none, source missing, page not verified, figure not inspected, mechanism inferred, durability missing, field missing, or statistics missing.

## WER-EA mini-review extraction route

For WER-EA, waterborne epoxy resin modified emulsified asphalt, waterproof-bonding, tack-coat, or adjacent pavement-bonding sources, extract rows in these groups:

- mechanism rows: epoxy-amine curing, demulsification, phase morphology, FTIR/SEM/FM/AFM/DSC/TG/rheology, interface adhesion, and compatibility.
- dosage rows: WER dosage, curing-agent ratio, emulsifier, asphalt/emulsion type, SBR or other modifier, optimum window, overdose risk, and construction window.
- durability rows: moisture, aging, freeze-thaw, UV, fatigue, traffic/service simulation, field evidence, and missing service tests.
- citation-role rows: central evidence, adjacent evidence, method evidence, background, caution, or gap.
- figure-handoff rows: mechanism map, evidence heatmap, dosage window, test-method comparison, performance-mechanism boundary, or literature-screening flow.

Performance improvement alone is not a mechanism row. It can support a performance-comparison or dosage-window row and may become a mechanism row only when direct chemistry, morphology, rheology, or interface evidence is anchored.

## Visual-asset linkage protocol

Each figure/table card used for downstream review work must record:

- source page and figure/table label,
- rendered page or DOI/HTML source status,
- crop status,
- asset file or failure reason,
- interpretation boundary,
- whether it can support a review figure,
- figure archetype,
- reviewer-risk boundary.

Use `review_figure_support: yes` only when the asset has been visually inspected, the source anchor is clear, and the card distinguishes measured evidence from interpretation. Use `conditional` when the asset can guide a schematic but needs redraw, permission, additional sources, or missing-test disclosure. Use `no` when the asset is text-only, unverified, or would invite overclaiming.

## Handoff to citation

Before handing rows to `materials-citation`, make sure every borrowable claim has:

- `claim_id`,
- `source_anchor`,
- `citation_role`,
- `evidence_type`,
- `confidence_label`,
- `boundary_or_missing_test`,
- `reviewer_risk`.

Rows without direct evidence may still be useful as background or gap rows, but they must not be labeled as primary experimental support.

## Handoff to figure

Before handing rows to `materials-figure`, make sure every figure-worthy row has:

- `claim_id`,
- `source_anchor`,
- `measured_evidence`,
- `inferred_mechanism`,
- `figure_archetype`,
- `boundary_or_missing_test`,
- `reviewer_risk`,
- visual-asset status from the matching figure/table card.

If the figure is schematic-only, state which parts are measured, inferred, or missing. The caption boundary should be ready before the figure workflow begins.
