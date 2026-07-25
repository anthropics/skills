# Literature Pipeline Contract

`materials-literature-pipeline` produces candidate-stage discovery outputs. It
does not replace source reading, source-anchored extraction, or citation
verification.

## Inputs

- Topic, material system, keywords, and time window.
- Optional `citation-handoff` from `materials-citation`.
- User-provided databases, journals, or inclusion/exclusion rules.

## Outputs

- Required: `literature_candidate_table.csv`, `literature_digest.md`.
- Optional `search_strategy.md`
- Optional `gap_report.md`
- Optional `review_compilation_plan.md`

## Handoff Fields

The candidate table keeps these public fields in order:

`candidate_id`, `title`, `year`, `venue`, `doi`, `dedup_key`,
`material_system_match`, `evidence_layer`, `source_depth`, `topic_fit`,
`evidence_layer_score`, `method_relevance`, `material_system_proximity`,
`source_quality`, `actionability`, `score_total`, `next_action`,
`evidence_boundary`.

The six numeric score fields are the score breakdown; do not add a separate
JSON `score_breakdown` CSV column.

## Evidence Boundary

Every literature-pipeline candidate row remains candidate evidence at every
`source_depth` and for every score, including `full-text-read` and
`data-extracted`. The row is never manuscript evidence and is never promoted
into it. Manuscript support must be a separate source-anchored
`materials-reader` or extraction artifact. The candidate row may link or route
to that artifact while preserving its own candidate status.

When scoring is active, recalculate `score_total` from the six dimensions. Do
not compensate for degradation by inflating scores. `topic_fit < 10` blocks the
top tier; every top-tier row requires `source_depth`, `evidence_boundary`, and
`next_action`. Record reasons for `exclude` and `archive`.

## Handoff And State

The `literature-pipeline-handoff` carries each candidate's boundary and next
action. Route `read` to `materials-reader` and `cite-gap-audit` to
`materials-citation`. Formal consumer wiring remains outside this skill.

In persistent multi-skill workflows, store rows only in
`research-state.source_map.candidates`. Do not create a new database,
downloader, or external scheduling service. Automated schedules remain local
until listing and a manual run verify them; report partial-source, delivery, or
archive degradation explicitly.
