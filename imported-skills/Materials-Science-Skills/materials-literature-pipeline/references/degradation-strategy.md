# Degradation Strategy

Use this reference when any source, scheduler, delivery channel, or archive step
fails. The goal is to preserve a useful digest without fabricating coverage.

## Source Degradation

Search sources are attempted in priority order selected for the task. If a
source fails:

1. Record the source name, failure type, and time.
2. Continue with remaining sources.
3. Label the run as `partial-source`.
4. In the digest, state which source was unavailable.
5. Do not compensate by inflating scores from weaker sources.

Recommended fallback ladder:

| Failed source type | Fallback |
|---|---|
| Subscription index unavailable | Crossref/OpenAlex metadata plus user-provided records |
| Publisher API unavailable | DOI/title search plus abstracts when available |
| Semantic/citation graph unavailable | Keyword search plus reference chasing from known papers |
| Full text unavailable | `abstract-screened` only; route to `materials-reader` or library access |

## Scheduler Degradation

If cron or automation is absent, invisible, or missed:

1. Manually run a reduced candidate search.
2. Deliver the digest or save it locally.
3. Recreate the schedule only after the user has the backfill.
4. Add `manual_backfill: true` to the run record.

## Delivery Degradation

If push delivery fails:

1. Save `literature_digest.md`.
2. Save `literature_candidate_table.csv`.
3. Report the local paths and the failed target.
4. Do not block archive or research-state updates.

## Archive Degradation

If archive write fails:

1. Keep the digest and candidate table in the current output folder.
2. Mark `archive_status: failed`.
3. Do not rewrite knowledge-base pages automatically.
4. Ask for the archive path only when the user wants the notes persisted.
