---
name: "autoresearch-agent"
description: "Autonomous experiment loop that optimizes any file by a measurable metric. Inspired by Karpathy's autoresearch. The agent edits a target file, runs a fixed evaluation, keeps improvements (git commit), discards failures (git reset), and loops indefinitely. Use when: user wants to optimize code speed, reduce bundle/image size, improve test pass rate, optimize prompts, improve content quality (headlines, copy, CTR), or run any measurable improvement loop. Requires: a target file, an evaluation command that outputs a metric, and a git repo."
license: MIT
metadata:
  version: 2.0.0
  author: Alireza Rezvani
  category: engineering
  updated: 2026-03-13
---

# Autoresearch Agent

> You sleep. The agent experiments. You wake up to results.

Autonomous experiment loop inspired by [Karpathy's autoresearch](https://github.com/karpathy/autoresearch). The agent edits one file, runs a fixed evaluation, keeps improvements, discards failures, and loops indefinitely.

Not one guess — fifty measured attempts, compounding.

---

## Slash Commands

| Command | What it does |
|---------|-------------|
| `/ar:setup` | Set up a new experiment interactively |
| `/ar:run` | Run a single experiment iteration |
| `/ar:loop` | Start autonomous loop with configurable interval (10m, 1h, daily, weekly, monthly) |
| `/ar:status` | Show dashboard and results |
| `/ar:resume` | Resume a paused experiment |

---

## When This Skill Activates

Recognize these patterns from the user:

- "Make this faster / smaller / better"
- "Optimize [file] for [metric]"
- "Improve my [headlines / copy / prompts]"
- "Run experiments overnight"
- "I want to get [metric] from X to Y"
- Any request involving: optimize, benchmark, improve, experiment loop, autoresearch

If the user describes a target file + a way to measure success → this skill applies.

---

## Setup

### First Time — Create the Experiment

Run the setup script. The user decides where experiments live:

**Project-level** (inside repo, git-tracked, shareable with team):
```bash
python scripts/setup_experiment.py \
  --domain engineering \
  --name api-speed \
  --target src/api/search.py \
  --eval "pytest bench.py --tb=no -q" \
  --metric p50_ms \
  --direction lower \
  --scope project
```

**User-level** (personal, in `~/.autoresearch/`):
```bash
python scripts/setup_experiment.py \
  --domain marketing \
  --name medium-ctr \
  --target content/titles.md \
  --eval "python evaluate.py" \
  --metric ctr_score \
  --direction higher \
  --evaluator llm_judge_content \
  --scope user
```

The `--scope` flag determines where `.autoresearch/` lives:
- `project` (default) → `.autoresearch/` in the repo root. Experiment definitions are git-tracked. Results are gitignored.
- `user` → `~/.autoresearch/` in the home directory. Everything is personal.

### What Setup Creates

```
.autoresearch/
├── config.yaml                        ← Global settings
├── .gitignore                         ← Ignores results.tsv, *.log
└── {domain}/{experiment-name}/
    ├── program.md                     ← Objectives, constraints, strategy
    ├── config.cfg                     ← Target, eval cmd, metric, direction
    ├── results.tsv                    ← Experiment log (gitignored)
    └── evaluate.py                    ← Evaluation script (if --evaluator used)
```

**results.tsv columns:** `commit | metric | status | description`
- `commit` — short git hash
- `metric` — float value or "N/A" for crashes
- `status` — keep | discard | crash
- `description` — what changed or why it crashed

### Domains

| Domain | Use Cases |
|--------|-----------|
| `engineering` | Code speed, memory, bundle size, test pass rate, build time |
| `marketing` | Headlines, social copy, email subjects, ad copy, engagement |
| `content` | Article structure, SEO descriptions, readability, CTR |
| `prompts` | System prompts, chatbot tone, agent instructions |
| `custom` | Anything else with a measurable metric |

### If `program.md` Already Exists

The user may have written their own `program.md`. If found in the experiment directory, read it. It overrides the template. Only ask for what's missing.

---

## Agent Protocol

You are the loop. The scripts handle setup and evaluation — you handle the creative work.

### Before Starting
1. Read `.autoresearch/{domain}/{name}/config.cfg` to get:
   - `target` — the file you edit
   - `evaluate_cmd` — the command that measures your changes
   - `metric` — the metric name to look for in eval output
   - `metric_direction` — "lower" or "higher" is better
   - `time_budget_minutes` — max time per evaluation
2. Read `program.md` for strategy, constraints, and what you can/cannot change
3. Read `results.tsv` for experiment history (columns: commit, metric, status, description)
4. Checkout the experiment branch: `git checkout autoresearch/{domain}/{name}`

### Each Iteration
1. Review results.tsv — what worked? What failed? What hasn't been tried?
2. Decide ONE change to the target file. One variable per experiment.
3. Edit the target file
4. Commit: `git add {target} && git commit -m "experiment: {description}"`
5. Evaluate: `python scripts/run_experiment.py --experiment {domain}/{name} --single`
6. Read the output — it prints KEEP, DISCARD, or CRASH with the metric value
7. Go to step 1

### What the Script Handles (you don't)
- Running the eval command with timeout
- Parsing the metric from eval output
- Comparing to previous best
- Reverting the commit on failure (`git reset --hard HEAD~1`)
- Logging the result to results.tsv

### Starting an Experiment

```bash
# Single iteration (the agent calls this repeatedly)
python scripts/run_experiment.py --experiment engineering/api-speed --single

# Dry run (test setup before starting)
python scripts/run_experiment.py --experiment engineering/api-speed --dry-run
```

### Strategy Escalation
- Runs 1-5: Low-hanging fruit (obvious improvements, simple optimizations)
- Runs 6-15: Systematic exploration (vary one parameter at a time)
- Runs 16-30: Structural changes (algorithm swaps, architecture shifts)
- Runs 30+: Radical experiments (completely different approaches)
- If no improvement in 20+ runs: update program.md Strategy section

### Self-Improvement
After every 10 experiments, review results.tsv for patterns. Update the
Strategy section of program.md with what you learned (e.g., "caching changes
consistently improve by 5-10%", "refactoring attempts never improve the metric").
Future iterations benefit from this accumulated knowledge.

### Stopping
- Run until interrupted by the user, context limit reached, or goal in program.md is met
- Before stopping: ensure results.tsv is up to date
- On context limit: the next session can resume — results.tsv and git log persist

### Rules

- **One change per experiment.** Don't change 5 things at once. You won't know what worked.
- **Simplicity criterion.** A small improvement that adds ugly complexity is not worth it. Equal performance with simpler code is a win. Removing code that gets same results is the best outcome.
- **Never modify the evaluator.** `evaluate.py` is the ground truth. Modifying it invalidates all comparisons. Hard stop if you catch yourself doing this.
- **Timeout.** If a run exceeds 2.5× the time budget, kill it and treat as crash.
- **Crash handling.** If it's a typo or missing import, fix and re-run. If the idea is fundamentally broken, revert, log "crash", move on. 5 consecutive crashes → pause and alert.
- **No new dependencies.** Only use what's already available in the project.

---

## Evaluators

Ready-to-use evaluation scripts. Copied into the experiment directory during setup with `--evaluator`.

### Free Evaluators (no API cost)

| Evaluator | Metric | Use Case |
|-----------|--------|----------|
| `benchmark_speed` | `p50_ms` (lower) | Function/API execution time |
| `benchmark_size` | `size_bytes` (lower) | File, bundle, Docker image size |
| `test_pass_rate` | `pass_rate` (higher) | Test suite pass percentage |
| `build_speed` | `build_seconds` (lower) | Build/compile/Docker build time |
| `memory_usage` | `peak_mb` (lower) | Peak memory during execution |

### LLM Judge Evaluators (uses your subscription)

| Evaluator | Metric | Use Case |
|-----------|--------|----------|
| `llm_judge_content` | `ctr_score` 0-10 (higher) | Headlines, titles, descriptions |
| `llm_judge_prompt` | `quality_score` 0-100 (higher) | System prompts, agent instructions |
| `llm_judge_copy` | `engagement_score` 0-10 (higher) | Social posts, ad copy, emails |

LLM judges call the CLI tool the user is already running (Claude, Codex, Gemini). The evaluation prompt is locked inside `evaluate.py` — the agent cannot modify it. This prevents the agent from gaming its own evaluator.

The user's existing subscription covers the cost:
- Claude Code Max → unlimited Claude calls for evaluation
- Codex CLI (ChatGPT Pro) → unlimited Codex calls
- Gemini CLI (free tier) → free evaluation calls

### Custom Evaluators

If no built-in evaluator fits, the user writes their own `evaluate.py`. Only requirement: it must print `metric_name: value` to stdout.

```python
#!/usr/bin/env python3
# My custom evaluator — DO NOT MODIFY after experiment starts
import subprocess
result = subprocess.run(["my-benchmark", "--json"], capture_output=True, text=True)
# Parse and output
print(f"my_metric: {parse_score(result.stdout)}")
```

---

## Viewing Results

```bash
# Single experiment
python scripts/log_results.py --experiment engineering/api-speed

# All experiments in a domain
python scripts/log_results.py --domain engineering

# Cross-experiment dashboard
python scripts/log_results.py --dashboard

# Export formats
python scripts/log_results.py --experiment engineering/api-speed --format csv --output results.csv
python scripts/log_results.py --experiment engineering/api-speed --format markdown --output results.md
python scripts/log_results.py --dashboard --format markdown --output dashboard.md
```

### Dashboard Output

```
DOMAIN          EXPERIMENT          RUNS  KEPT  BEST         Δ FROM START  STATUS
engineering     api-speed            47    14   185ms        -76.9%        active
engineering     bundle-size          23     8   412KB        -58.3%        paused
marketing       medium-ctr           31    11   8.4/10       +68.0%        active
prompts         support-tone         15     6   82/100       +46.4%        done
```

### Export Formats

- **TSV** — default, tab-separated (compatible with spreadsheets)
- **CSV** — comma-separated, with proper quoting
- **Markdown** — formatted table, readable in GitHub/docs

---

## Proactive Triggers

Flag these without being asked:

- **No evaluation command works** → Test it before starting the loop. Run once, verify output.
- **Target file not in git** → `git init && git add . && git commit -m 'initial'` first.
- **Metric direction unclear** → Ask: is lower or higher better? Must know before starting.
- **Time budget too short** → If eval takes longer than budget, every run crashes.
- **Agent modifying evaluate.py** → Hard stop. This invalidates all comparisons.
- **5 consecutive crashes** → Pause the loop. Alert the user. Don't keep burning cycles.
- **No improvement in 20+ runs** → Suggest changing strategy in program.md or trying a different approach.

---

## Installation

### One-liner (any tool)
```bash
git clone https://github.com/alirezarezvani/claude-skills.git
cp -r claude-skills/engineering/autoresearch-agent ~/.claude/skills/
```

### Multi-tool install
```bash
./scripts/convert.sh --skill autoresearch-agent --tool codex|gemini|cursor|windsurf|openclaw
```

### OpenClaw
```bash
clawhub install cs-autoresearch-agent
```

---

## Related Skills

- **self-improving-agent** — improves an agent's own memory/rules over time. NOT for structured experiment loops.
- **senior-ml-engineer** — ML architecture decisions. Complementary — use for initial design, then autoresearch for optimization.
- **tdd-guide** — test-driven development. Complementary — tests can be the evaluation function.
- **skill-security-auditor** — audit skills before publishing. NOT for optimization loops.
