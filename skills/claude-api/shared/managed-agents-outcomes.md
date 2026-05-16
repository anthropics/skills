# Managed Agents — Outcomes

An **outcome** elevates a session from *conversation* to *work*: you state what "done" looks like, and the harness runs an iterate → grade → revise loop until the artifact meets the rubric, hits `max_iterations`, or is interrupted. A separate **grader** (independent context window) scores each iteration against your rubric and feeds per-criterion gaps back to the agent.

The SDK sets the `managed-agents-2026-04-01` beta header automatically on all `client.beta.sessions.*` calls; no additional header is required for outcomes.

---

## The `user.define_outcome` event

Outcomes are not a field on `sessions.create()`. You create a normal session, then send a `user.define_outcome` event. The agent starts working on receipt — **do not also send a `user.message`** to kick it off.

```python
session = client.beta.sessions.create(
    agent=AGENT_ID,
    environment_id=ENVIRONMENT_ID,
    title="Financial analysis on Costco",
)

client.beta.sessions.events.send(
    session_id=session.id,
    events=[
        {
            "type": "user.define_outcome",
            "description": "Build a DCF model for Costco in .xlsx",
            "rubric": {"type": "text", "content": RUBRIC_MD},
            # or: "rubric": {"type": "file", "file_id": rubric.id}
            "max_iterations": 5,  # optional; default 3, max 20
        }
    ],
)
```

| Field | Type | Notes |
|---|---|---|
| `type` | `"user.define_outcome"` | |
| `description` | string | The task. This is what the agent works toward — no separate `user.message` needed. |
| `rubric` | `{type: "text", content}` \| `{type: "file", file_id}` | **Required.** Markdown with explicit, independently gradeable criteria. Upload once via `client.beta.files.upload(...)` (beta `files-api-2025-04-14`) to reuse across sessions. |
| `max_iterations` | int | Optional. Default **3**, max **20**. |

The event is echoed back on the stream with a server-assigned `outcome_id` and `processed_at`.

> **Writing rubrics.** Use explicit, gradeable criteria ("CSV has a numeric `price` column"), not vibes ("data looks good") — the grader scores each criterion independently, so vague criteria produce noisy loops. If you don't have a rubric, have Claude analyze a known-good artifact and turn that analysis into one.

---

## Outcome-specific events

These appear on the standard event stream (`sessions.events.stream` / `.list`) alongside the usual `agent.*` / `session.*` events.

| Event | Payload highlights | Meaning |
|---|---|---|
| `span.outcome_evaluation_start` | `outcome_id`, `iteration` (0-indexed) | Grader began scoring iteration *N*. |
| `span.outcome_evaluation_ongoing` | `outcome_id` | Heartbeat while the grader runs. Grader reasoning is opaque — you see *that* it's working, not *what* it's thinking. |
| `span.outcome_evaluation_end` | `outcome_evaluation_start_id`, `outcome_id`, `iteration`, `result`, `explanation`, `usage` | Grader finished one iteration. `result` drives what happens next (table below). |

### `span.outcome_evaluation_end.result`

| `result` | Next |
|---|---|
| `satisfied` | Session → `idle`. Terminal for this outcome. |
| `needs_revision` | Agent starts another iteration. |
| `max_iterations_reached` | No further grader cycles. Agent may run one final revision, then session → `idle`. |
| `failed` | Session → `idle`. Rubric fundamentally doesn't match the task (e.g. description and rubric contradict). |
| `interrupted` | Only emitted if `_start` had already fired before a `user.interrupt` arrived. |

```json
{
  "type": "span.outcome_evaluation_end",
  "id": "sevt_01jkl...",
  "outcome_evaluation_start_id": "sevt_01def...",
  "outcome_id": "outc_01a...",
  "result": "satisfied",
  "explanation": "All 12 criteria met: revenue projections use 5 years of historical data, ...",
  "iteration": 0,
  "usage": { "input_tokens": 2400, "output_tokens": 350, "cache_creation_input_tokens": 0, "cache_read_input_tokens": 1800 },
  "processed_at": "2026-03-25T14:03:00Z"
}
```

---

## Checking status & retrieving deliverables

**Status** — either watch the stream for `span.outcome_evaluation_end`, or poll the session and read `outcome_evaluations`:

```python
session = client.beta.sessions.retrieve(session.id)
for ev in session.outcome_evaluations:
    print(f"{ev.outcome_id}: {ev.result}")  # outc_01a...: satisfied
```

**Deliverables** — the agent writes to `/mnt/session/outputs/`. Once idle, fetch via the Files API with `scope_id=session.id`. This is the same session-outputs mechanism documented in `shared/managed-agents-environments.md` → Session outputs (including the dual-beta-header requirement on `files.list`).

---

## Interaction rules & pitfalls

- **One outcome at a time.** Chain by sending the next `user.define_outcome` only after the previous one's terminal `span.outcome_evaluation_end` (`satisfied` / `max_iterations_reached` / `failed` / `interrupted`). The session retains history across chained outcomes.
- **Steering is allowed but optional.** You *may* send `user.message` events mid-outcome to nudge direction, but the agent already knows to keep working until terminal — don't send "keep going" prompts.
- **`user.interrupt` pauses the current outcome** — it marks `result: "interrupted"` and leaves the session `idle`, ready for a new outcome or conversational turn.
- **After terminal, the session is reusable** — continue conversationally or define a new outcome.
- **Outcome ≠ session-create field.** Don't put `outcome`, `rubric`, or `description` on `sessions.create()` — outcomes are always sent as a `user.define_outcome` event.
- **Idle-break gate is unchanged.** In your drain loop, keep using `event.type === 'session.status_idle' && event.stop_reason?.type !== 'requires_action'` — do **not** gate on `span.outcome_evaluation_end` alone (on `needs_revision` the session keeps running). See `shared/managed-agents-client-patterns.md` Pattern 5.

For the raw HTTP shapes and per-language SDK bindings beyond Python, WebFetch `https://platform.claude.com/docs/en/managed-agents/define-outcomes.md` (see `shared/live-sources.md`).
