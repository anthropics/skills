---
name: "loop"
description: "Start an autonomous experiment loop with user-selected interval (10min, 1h, daily, weekly, monthly). Uses CronCreate for scheduling. Use when the user runs /ar:loop or asks to run an autoresearch experiment continuously on a schedule."
command: /ar:loop
---

# /ar:loop — Autonomous Experiment Loop

Start a recurring experiment loop that runs at a user-selected interval.

## Usage

```
/ar:loop engineering/api-speed             # Start loop (prompts for interval)
/ar:loop engineering/api-speed 10m         # Every 10 minutes
/ar:loop engineering/api-speed 1h          # Every hour
/ar:loop engineering/api-speed daily       # Daily at ~9am
/ar:loop engineering/api-speed weekly      # Weekly on Monday ~9am
/ar:loop engineering/api-speed monthly     # Monthly on 1st ~9am
/ar:loop stop engineering/api-speed        # Stop an active loop
```

## What It Does

### Step 1: Resolve experiment

If no experiment specified, list experiments and let user pick.

### Step 2: Select interval

If interval not provided as argument, present options:

```
Select loop interval:
  1. Every 10 minutes  (rapid — stay and watch)
  2. Every hour         (background — check back later)
  3. Daily at ~9am      (overnight experiments)
  4. Weekly on Monday   (long-running experiments)
  5. Monthly on 1st     (slow experiments)
```

Map to cron expressions:

| Interval | Cron Expression | Shorthand |
|----------|----------------|-----------|
| 10 minutes | `*/10 * * * *` | `10m` |
| 1 hour | `7 * * * *` | `1h` |
| Daily | `57 8 * * *` | `daily` |
| Weekly | `57 8 * * 1` | `weekly` |
| Monthly | `57 8 1 * *` | `monthly` |

### Step 3: Create the recurring job

Use `CronCreate` with this prompt (fill in the experiment details):

```
You are running autoresearch experiment "{domain}/{name}".

1. Read .autoresearch/{domain}/{name}/config.cfg for: target, evaluate_cmd, metric, metric_direction
2. Read .autoresearch/{domain}/{name}/program.md for strategy and constraints
3. Read .autoresearch/{domain}/{name}/results.tsv for experiment history
4. Run: git checkout autoresearch/{domain}/{name}

Then do exactly ONE iteration:
- Review results.tsv: what worked, what failed, what hasn't been tried
- Edit the target file with ONE change (strategy escalation based on run count)
- Commit: git add {target} && git commit -m "experiment: {description}"
- Evaluate: python {skill_path}/scripts/run_experiment.py --experiment {domain}/{name} --single
- Read the output (KEEP/DISCARD/CRASH)

Rules:
- ONE change per experiment
- NEVER modify the evaluator
- If 5 consecutive crashes in results.tsv, delete this cron job (CronDelete) and alert
- After every 10 experiments, update Strategy section of program.md

Current best metric: {read from results.tsv or "no baseline yet"}
Total experiments so far: {count from results.tsv}
```

### Step 4: Store loop metadata

Write to `.autoresearch/{domain}/{name}/loop.json`:

```json
{
  "cron_id": "{id from CronCreate}",
  "interval": "{user selection}",
  "started": "{ISO timestamp}",
  "experiment": "{domain}/{name}"
}
```

### Step 5: Confirm to user

```
Loop started for {domain}/{name}
  Interval: {interval description}
  Cron ID: {id}
  Auto-expires: 3 days (CronCreate limit)

  To check progress: /ar:status
  To stop the loop:  /ar:loop stop {domain}/{name}

  Note: Recurring jobs auto-expire after 3 days.
  Run /ar:loop again to restart after expiry.
```

## Stopping a Loop

When user runs `/ar:loop stop {experiment}`:

1. Read `.autoresearch/{domain}/{name}/loop.json` to get the cron ID
2. Call `CronDelete` with that ID
3. Delete `loop.json`
4. Confirm: "Loop stopped for {experiment}. {n} experiments completed."

## Important Limitations

- **3-day auto-expiry**: CronCreate jobs expire after 3 days. For longer experiments, the user must re-run `/ar:loop` to restart. Results persist — the new loop picks up where the old one left off.
- **One loop per experiment**: Don't start multiple loops for the same experiment.
- **Concurrent experiments**: Multiple experiments can loop simultaneously ONLY if they're on different git branches (which they are by default — each experiment gets `autoresearch/{domain}/{name}`).
