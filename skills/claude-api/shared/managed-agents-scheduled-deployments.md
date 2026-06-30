# Managed Agents — Scheduled Deployments

A **scheduled deployment** runs an agent on a recurring cron schedule — each firing creates a session autonomously. Use it for predictable-cadence work: nightly triage, weekly compliance scans, hourly monitors.

Requires the `managed-agents-2026-04-01` beta header (the SDK sets it automatically for `client.beta.deployments.*` / `client.beta.deployment_runs.*` calls).

## Create a deployment

A deployment bundles everything a session needs (agent, environment, optional files / GitHub / memory stores / vaults) plus a `schedule` and the `initial_events` that kick off each run:

- `agent` and `environment_id` are required — same shapes as `sessions.create` (see `shared/managed-agents-core.md`).
- `initial_events` must contain the starting `user.message`.
- `schedule` takes a cron `expression` and an IANA `timezone`. Minute-level granularity is the maximum.

```bash
curl -fsSL https://api.anthropic.com/v1/deployments \
  -H "x-api-key: $ANTHROPIC_API_KEY" \
  -H "anthropic-version: 2023-06-01" \
  -H "anthropic-beta: managed-agents-2026-04-01" \
  -H "content-type: application/json" \
  -d @- <<EOF
{
  "name": "Weekly compliance scan",
  "agent": "$AGENT_ID",
  "environment_id": "$ENVIRONMENT_ID",
  "initial_events": [
    {"type": "user.message", "content": [{"type": "text", "text": "Run the weekly compliance scan."}]}
  ],
  "schedule": {
    "type": "cron",
    "expression": "0 20 * * 5",
    "timezone": "America/New_York"
  }
}
EOF
```

```python
deployment = client.beta.deployments.create(
    name="Weekly compliance scan",
    agent=agent.id,
    environment_id=environment.id,
    initial_events=[
        {
            "type": "user.message",
            "content": [{"type": "text", "text": "Run the weekly compliance scan."}],
        },
    ],
    schedule={
        "type": "cron",
        "expression": "0 20 * * 5",
        "timezone": "America/New_York",
    },
)
```

The response is a deployment object (`depl_` ID prefix). Check `schedule.upcoming_runs_at` — the next fire times — to confirm the schedule parses the way you intended:

```json
{
  "id": "depl_01xyz",
  "status": "active",
  "paused_reason": null,
  "schedule": {
    "type": "cron",
    "expression": "0 20 * * 5",
    "timezone": "America/New_York",
    "last_run_at": null,
    "upcoming_runs_at": ["2026-05-09T00:00:00Z", "2026-05-16T00:00:00Z", "2026-05-23T00:00:00Z"]
  }
}
```

Deployments may apply up to **10 seconds of jitter** to distribute load. Maximum **1000 scheduled deployments per organization** (contact Anthropic support for more).

### Cron and timezone semantics

- **Expression:** standard POSIX cron (`minute hour day-of-month month day-of-week`).
- **Timezone:** IANA identifier (e.g. `"America/Los_Angeles"`).
- **DST:** literal wall-clock matching — `"0 20 * * *"` in `America/New_York` fires at 8:00 PM local regardless of EST/EDT.

> ⚠️ **DST edge:** wall-clock times that don't exist on a spring-forward day (e.g. 2AM) are **skipped**; times that occur twice on a fall-back day **fire twice**. Schedule outside the 1–3AM local window, or use UTC, when missed or duplicate executions are unacceptable.

## Deployment runs

Every trigger attempt — successful or not — writes a **deployment run** record (`drun_` prefix), so you can audit failures independent of the session lifecycle. A successful run carries the created `session_id`; follow that session via the event stream (`shared/managed-agents-events.md`) or webhooks (`shared/managed-agents-webhooks.md`) as usual. A failed run carries an `error` whose `type` explains why session creation was rejected.

```python
# All runs for a deployment
for run in client.beta.deployment_runs.list(deployment_id=deployment.id):
    print(run.created_at, run.session_id or run.error.type)

# Failures only
for run in client.beta.deployment_runs.list(deployment_id=deployment.id, has_error=True):
    print(run.created_at, run.error.type, run.error.message)
```

```typescript
for await (const run of client.beta.deploymentRuns.list({
  deployment_id: deployment.id,
  has_error: true,
})) {
  console.log(run.created_at, run.error?.type, run.error?.message);
}
```

Raw HTTP: `GET /v1/deployment_runs?deployment_id=...&has_error=true`. To retrieve a single run by ID, `GET /v1/deployment_runs/{deployment_run_id}` (SDK: `client.beta.deployment_runs.retrieve(run_id)`) — a `deployment_run.*` webhook event carries the run ID as its `data.id`.

A failed run looks like:

```json
{
  "type": "deployment_run",
  "id": "drun_01abc124",
  "deployment_id": "depl_01xyz",
  "trigger_context": { "type": "schedule", "scheduled_at": "2026-05-09T00:00:00Z" },
  "session_id": null,
  "error": { "type": "environment_archived", "message": "environment `env_01abc` is archived" },
  "agent": { "type": "agent", "id": "agent_01ghi789", "version": 3 },
  "created_at": "2026-05-09T00:00:01Z"
}
```

Error types include `environment_archived`, `agent_archived`, `vault_not_found`, `session_rate_limited`, and `service_unavailable`.

The outcome of each **scheduled** run (started/succeeded/failed) and each deployment lifecycle change (created/updated/paused/unpaused/archived/deleted) is also delivered as a webhook event — see `shared/managed-agents-webhooks.md` for the `deployment.*` and `deployment_run.*` event types — so you can react without polling. Manual runs do **not** emit `deployment_run.*` webhook events.

## Lifecycle: pause / unpause / archive

| Operation | SDK | Effect |
|---|---|---|
| Pause | `client.beta.deployments.pause(id)` | Suppresses scheduled triggers go-forward. Sessions already running continue. **Manual runs are still permitted while paused.** Sets `paused_reason: {"type": "manual"}`. |
| Unpause | `client.beta.deployments.unpause(id)` | Resumes from the next scheduled occurrence. **Missed triggers are not backfilled.** Clears `paused_reason`. |
| Archive | `client.beta.deployments.archive(id)` | **Terminal** — the schedule stops and the deployment can no longer be modified. Use pause for anything reversible. |

Raw HTTP: `POST /v1/deployments/{deployment_id}/pause` (likewise `/unpause`, `/archive`).

### Failure behavior

- **Rate-limited:** recorded immediately as a `session_rate_limited` run, **no retry** — the schedule simply tries again at the next occurrence. (Rate limits on API calls *inside* a session are handled by the session itself.)
- **Other failed runs** (e.g. `environment_archived`, `vault_not_found`, `service_unavailable`): the run records the `error.type` — monitor runs and fix the referenced resource, or pause the deployment.
- **Agent archived or deleted:** the deployment is automatically **archived** (terminal) and no further sessions are created.

## Manual runs

`POST /v1/deployments/{deployment_id}/run` (SDK: `client.beta.deployments.run(id)`) creates a session immediately and writes a run with `trigger_context.type: "manual"`. Use it to **test a deployment before committing to the schedule** — and remember it works even while the deployment is paused.
