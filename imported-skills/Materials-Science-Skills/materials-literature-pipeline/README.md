# materials-literature-pipeline

Version: 1.1.0

`materials-literature-pipeline` adapts recurring literature discovery to materials research. It creates candidate tables, scoring notes, source-depth labels, and digest outputs that can be handed to `materials-research`, `materials-citation`, and `materials-reader`.

## When to use

Use this skill when the user wants to:

- monitor a materials topic repeatedly;
- screen many candidate papers before deep reading;
- score papers for relevance to a material system or method;
- prepare a daily/weekly digest;
- set up or audit a local recurring literature push;
- format digests for Feishu, Telegram, email, or Markdown inbox delivery;
- run a four-step literature gap analysis;
- compile pipeline outputs into a review-paper workflow;
- identify which papers need `materials-reader` or citation-gap auditing.

## Core outputs

| Output | Purpose |
|---|---|
| `literature_candidate_table.csv` | Candidate records, dedup keys, scores, source depth, and next action |
| `literature_digest.md` | Ranked digest with evidence caveats |
| `search_strategy.md` | Optional query and database record |
| `gap_report.md` | Optional four-step gap analysis report |
| `review_compilation_plan.md` | Optional review synthesis handoff |

## Scoring contract

Candidate tables use six numeric score fields: `topic_fit`,
`evidence_layer_score`, `method_relevance`, `material_system_proximity`,
`source_quality`, and `actionability`. `score_total` must be recalculated from
those six fields on every run.

Scores are discovery triage, not evidence promotion. Metadata-only and
abstract-screened records can guide reading priority, but manuscript claims
still require `materials-reader` source excerpts or extracted data. If a source,
delivery, archive, or schedule step degrades, record the degradation rather than
inflating scores.

## Boundaries

This skill does not bypass publisher access, download restricted PDFs, or treat search metadata as verified evidence. It organizes discovery and routes deep reading to other skills.

## Operational references

| Reference | Use |
|---|---|
| `references/cron-operations.md` | Local recurring run setup, verification, missed-run backfill |
| `references/push-format.md` | Daily/weekly digest message fields and delivery rules |
| `references/degradation-strategy.md` | Source, scheduler, delivery, and archive fallback |
| `references/gap-analysis.md` | Four-step gap analysis for unexplored topics |
| `references/review-compilation-workflow.md` | Turning pipeline outputs into a review synthesis plan |
