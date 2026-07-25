# Literature Pipeline Workflow

1. Read the manifest and default core.
2. Apply profile-first routing and detect pipeline mode, family, and output.
3. Define topic, time window, sources, inclusion rules, and exclusion rules.
4. Assign stable candidate IDs and deduplicate by DOI or normalized title plus
   year before scoring.
5. Load the scoring rubric only when scoring, ranking, or auditing candidates.
6. Preserve source depth, evidence boundary, and next action on every retained
   candidate.
7. Route `read` to materials-reader and `cite-gap-audit` to
   materials-citation.
8. Load research-state guidance only for persistent multi-skill workflows.
9. Load cron, push, degradation, gap, or review-compilation references only
   when their conditions apply.
10. Emit the candidate table, digest, and literature pipeline handoff.
