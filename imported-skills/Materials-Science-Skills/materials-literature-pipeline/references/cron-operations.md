# Cron Operations

Use this reference when the literature pipeline should run on a recurring local
schedule. The schedule is an operational wrapper around the existing materials
scoring system and `literature-pipeline-handoff`; it does not change the scoring
rubric or evidence contract.

## Setup Protocol

1. Capture the schedule: timezone, cadence, run window, candidate count, top-N
   delivery count, archive path, and delivery target.
2. Confirm local scheduler scope. Treat cron or app automations as local/profile
   state, not a cloud guarantee.
3. Create the scheduled run only after the search scope, source list, and digest
   template are stable.
4. Immediately list scheduled jobs and record the visible job identifier.
5. Run one manual dry run with a small candidate count before relying on the
   schedule.

## Verification Checklist

- [ ] The job appears in the current scheduler/profile after creation.
- [ ] Manual run completes search, deduplication, scoring, and digest rendering.
- [ ] Delivery target is reachable, or the digest is saved locally for manual
      posting.
- [ ] Archive path accepts writes to a raw or inbox location.
- [ ] The user knows the computer/profile must be running at the scheduled time.

## Failure Triage

If the scheduled push does not arrive:

1. Send a manual backfill digest first; do not spend the morning debugging before
   the user receives papers.
2. List scheduled jobs. If the job is absent, recreate it and record that the
   previous profile did not retain the task.
3. Check source availability and apply `degradation-strategy.md`.
4. Check delivery availability. If delivery fails, save the digest and provide
   the local path for manual posting.
5. Check archive write status. Archive failure must not block the digest.

## Run Record

Every scheduled run should leave a short run record:

```yaml
run_id: ""
scheduled_for: ""
started_at: ""
candidate_target: 30
delivered_top_n: 5
sources_attempted: []
sources_degraded: []
delivery_status: ""
archive_status: ""
manual_backfill: false
notes: []
```
