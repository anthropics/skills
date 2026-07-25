# TC Lifecycle and State Machine

A TC moves through six implementation states. Transitions are validated on every write — invalid moves are rejected with a clear error.

## State Diagram

```
                +-----------+
                |  planned  |
                +-----------+
                  |       ^
                  v       |
                +-------------+
        +-----> | in_progress | <-----+
        |       +-------------+       |
        |         |       |           |
        v         |       v           |
   +---------+    |  +-------------+  |
   | blocked |<---+  | implemented |  |
   +---------+       +-------------+  |
        |                  |          |
        v                  v          |
   +---------+         +--------+     |
   | planned |         | tested |-----+
   +---------+         +--------+
                            |
                            v
                       +----------+
                       | deployed |
                       +----------+
                            |
                            v
                       in_progress (rework / hotfix)
```

## Transition Table

| From | Allowed Transitions |
|------|---------------------|
| `planned` | `in_progress`, `blocked` |
| `in_progress` | `blocked`, `implemented` |
| `blocked` | `in_progress`, `planned` |
| `implemented` | `tested`, `in_progress` |
| `tested` | `deployed`, `in_progress` |
| `deployed` | `in_progress` |

Same-status transitions are no-ops and always allowed. Anything else is an error.

## State Definitions

| State | Meaning | Required Before Moving Forward |
|-------|---------|--------------------------------|
| `planned` | TC has been created with description and motivation | Decide implementation approach |
| `in_progress` | Active development | Code changes captured in `files_affected` |
| `blocked` | Cannot proceed (dependency, decision needed) | At least one entry in `handoff.blockers` |
| `implemented` | Code complete, awaiting tests | All target files in `files_affected` |
| `tested` | Test cases executed, results recorded | At least one `test_case` with status `pass` (or explicit `skip` with rationale) |
| `deployed` | Approved and shipped | `approval.approved=true` with `approved_by` and `approved_date` |

## Recovery Flows

### "I committed before testing"
1. Status is `implemented`.
2. Write tests, run them, set `test_cases[*].status = pass`.
3. Transition `implemented -> tested`.

### "Production bug in a deployed TC"
1. Open the deployed TC.
2. Transition `deployed -> in_progress`.
3. Add a new revision summarizing the rework.
4. Walk forward through `implemented -> tested -> deployed` again.

### "Blocked, then unblocked"
1. From `in_progress`, transition to `blocked`. Add blockers to `handoff.blockers`.
2. When unblocked, transition `blocked -> in_progress` and clear/move blockers to `notes`.

### "Cancelled work"
There is no `cancelled` state. If a TC is abandoned:
1. Add a final revision: "Cancelled — reason: ...".
2. Move to `blocked`.
3. Add a `[CANCELLED]` tag.
4. Leave the record in place — never delete it (history is append-only).

## Status Field Discipline

- Update `status` ONLY through `tc_update.py --set-status`. Never edit JSON by hand.
- Every status change creates a new revision entry with `field` = `status`, `action` = `changed`, and `reason` populated.
- The registry's `statistics.by_status` is recomputed on every write.

## Anti-patterns

| Anti-pattern | Why it's wrong |
|--------------|----------------|
| Skipping `tested` and going straight to `deployed` | Bypasses validation; misleads downstream consumers |
| Deleting a record to "cancel" a TC | History is append-only; deletion breaks the audit trail |
| Re-using a TC ID after deletion | Sequential numbering must be preserved |
| Changing status without a `--reason` | Future maintainers cannot reconstruct intent |
| Long-lived `in_progress` TCs (weeks+) | Either too big — split into sub-TCs — or stalled and should be marked `blocked` |
