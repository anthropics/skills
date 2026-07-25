---
name: "status"
description: "Show experiment dashboard with results, active loops, and progress. Use when the user runs /ar:status or asks how an autoresearch experiment is going."
command: /ar:status
---

# /ar:status — Experiment Dashboard

Show experiment results, active loops, and progress across all experiments.

## Usage

```
/ar:status                                  # Full dashboard
/ar:status engineering/api-speed            # Single experiment detail
/ar:status --domain engineering             # All experiments in a domain
/ar:status --format markdown                # Export as markdown
/ar:status --format csv --output results.csv  # Export as CSV
```

## What It Does

### Single experiment

```bash
python {skill_path}/scripts/log_results.py --experiment {domain}/{name}
```

Also check for active loop:
```bash
cat .autoresearch/{domain}/{name}/loop.json 2>/dev/null
```

If loop.json exists, show:
```
Active loop: every {interval} (cron ID: {id}, started: {date})
```

### Domain view

```bash
python {skill_path}/scripts/log_results.py --domain {domain}
```

### Full dashboard

```bash
python {skill_path}/scripts/log_results.py --dashboard
```

For each experiment, also check for loop.json and show loop status.

### Export

```bash
# CSV
python {skill_path}/scripts/log_results.py --dashboard --format csv --output {file}

# Markdown
python {skill_path}/scripts/log_results.py --dashboard --format markdown --output {file}
```

## Output Example

```
DOMAIN          EXPERIMENT          RUNS  KEPT  BEST         CHANGE    STATUS   LOOP
engineering     api-speed            47    14   185ms        -76.9%    active   every 1h
engineering     bundle-size          23     8   412KB        -58.3%    paused   —
marketing       medium-ctr           31    11   8.4/10       +68.0%    active   daily
prompts         support-tone         15     6   82/100       +46.4%    done     —
```
