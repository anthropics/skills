---
name: materials-literature-pipeline
version: "1.1.0"
description: Use when setting up, running, or auditing a recurring materials literature discovery workflow with candidate scoring, evidence-layer labels, deduplication, digest notes, and next-reading actions.
---

# Materials Literature Pipeline

Build recurring materials-literature watches and candidate-stage handoffs without
confusing discovery priority with manuscript evidence.

## Routing

1. Read `manifest.yaml` and its `always_load` core.
2. Apply profile-first routing, then detect the `pipeline_mode`,
   `material_family`, and `output` axes.
3. In configure mode, define scope and operation without loading scoring unless
   the user also asks to score, rank, calibrate, or audit candidates.
4. In run or audit mode, load only the selected axis paths and matching
   `references.on_demand` entries.
5. Assign stable candidate IDs and deduplicate by DOI or normalized title plus
   year before any scoring.
6. Emit the candidate table, digest, and `literature-pipeline-handoff` required
   by the request.

## Gates

- Every candidate row remains candidate evidence at every `source_depth` and
  score. Manuscript support requires a separate source-anchored reader or
  extraction artifact; the row may link or route to it but is never promoted.
- When scoring applies, recalculate totals from dimensions. A candidate with
  `topic_fit < 10` cannot rank top tier, and every top-tier row requires
  `source_depth`, `evidence_boundary`, and `next_action`.
- Candidates flagged as `exclude` or `archive` must have a documented reason.
- `next_action=read` routes through the handoff to `materials-reader`;
  `next_action=cite-gap-audit` routes to `materials-citation`.
- Automated schedules remain local/profile-bound until listed and manually
  verified. Report degradation without hiding partial coverage or inflating
  scores.
- Persistent multi-skill candidates live only in
  `research-state.source_map.candidates`.
