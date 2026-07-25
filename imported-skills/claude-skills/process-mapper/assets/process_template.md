# Process Template

Use this template to document a business process before running it through
the process-mapper tools. Fill in the stage table first, then translate it
into the JSON skeleton at the bottom of this file. Feed that JSON into the
three CLI tools:

```
python3 scripts/process_documenter.py    --input my-process.json
python3 scripts/bottleneck_detector.py   --input my-process.json --profile saas
python3 scripts/cycle_time_analyzer.py   --input my-process.json --profile saas
```

---

## Process metadata

- **Process name:** _(e.g., Procurement Intake, Employee Onboarding, Incident Handoff)_
- **Owner role:** _(who is accountable for the end-to-end process)_
- **Frequency:** _(how often this process runs — daily, weekly, on-demand)_
- **Trigger event:** _(what starts the process)_
- **End state:** _(what marks the process complete)_
- **WIP at any time:** _(how many items are typically in process at once; needed for Little's-Law throughput)_

---

## Stage table

Six rows to start. Add or remove as needed. **Honesty about stage `type` is
the single most important data-quality choice.** If a stage is queue / wait,
mark it `wait`. If it changes the work product from the customer's
perspective, mark it `value-add`. If it exists to fix an upstream defect,
mark it `rework`.

| # | Stage name | Owner (role) | Type | P50 (min) | P90 (min) | Notes |
|---|------------|--------------|------|-----------|-----------|-------|
| 1 | _e.g., Submit request_ | Requestor | value-add | 15 | 30 | |
| 2 | _e.g., Wait for manager approval queue_ | Manager | wait | 480 | 1440 | Typically batched |
| 3 | _e.g., Manager approves_ | Manager | value-add | 10 | 25 | |
| 4 | _e.g., Wait for finance review_ | Finance | wait | 720 | 2880 | |
| 5 | _e.g., Finance validates budget code_ | Finance | value-add | 20 | 60 | |
| 6 | _e.g., Rework — missing vendor W-9_ | Requestor | rework | 120 | 360 | Frequent escape |

**Type definitions (Lean canon):**

- `value-add` — the stage changes the work product in a way the end customer
  would willingly pay for. Most stages are NOT value-add.
- `wait` — work is queued, idle, or waiting for someone. Wait stages are the
  largest source of cycle-time bloat in most office processes.
- `rework` — the stage exists to fix a defect introduced upstream. Six-Sigma
  canon: rework is always an upstream-quality problem.

---

## JSON skeleton

Copy this into `my-process.json`, edit the values to match your stage table,
and pass it to the CLI tools.

```json
{
  "process_name": "Replace with your process name",
  "wip": 12,
  "stages": [
    {
      "name": "Stage 1 name",
      "owner": "Owning role",
      "type": "value-add",
      "duration_minutes_p50": 15,
      "duration_minutes_p90": 30
    },
    {
      "name": "Stage 2 name",
      "owner": "Owning role",
      "type": "wait",
      "duration_minutes_p50": 480,
      "duration_minutes_p90": 1440
    },
    {
      "name": "Stage 3 name",
      "owner": "Owning role",
      "type": "value-add",
      "duration_minutes_p50": 10,
      "duration_minutes_p90": 25
    },
    {
      "name": "Stage 4 name",
      "owner": "Owning role",
      "type": "wait",
      "duration_minutes_p50": 720,
      "duration_minutes_p90": 2880
    },
    {
      "name": "Stage 5 name",
      "owner": "Owning role",
      "type": "value-add",
      "duration_minutes_p50": 20,
      "duration_minutes_p90": 60
    },
    {
      "name": "Stage 6 name",
      "owner": "Owning role",
      "type": "rework",
      "duration_minutes_p50": 120,
      "duration_minutes_p90": 360
    }
  ]
}
```

---

## Tips

- **Use real data when you can.** Pull stage durations from your ticket system
  (Jira, ServiceNow, Zendesk). Estimated durations are fine for a first pass
  but should be replaced before any change decision is made.
- **One process at a time.** Goldratt: every system has exactly one binding
  constraint. Mapping ten processes simultaneously dilutes attention away
  from the one that's actually limiting throughput.
- **Profile choice matters.** Pass `--profile manufacturing` for physical-goods
  flows, `--profile services` for human-delivered services with longer
  acceptable wait times, `--profile healthcare` for clinical or regulated
  human-in-the-loop flows, `--profile saas` for everything else.
