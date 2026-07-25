---
name: "init"
description: "Create a new AgentHub collaboration session with task, agent count, and evaluation criteria. Use when the user runs /hub:init or asks to start a multi-agent competition on a task."
command: /hub:init
---

# /hub:init — Create New Session

Initialize an AgentHub collaboration session. Creates the `.agenthub/` directory structure, generates a session ID, and configures evaluation criteria.

## Usage

```
/hub:init                                                    # Interactive mode
/hub:init --task "Optimize API" --agents 3 --eval "pytest bench.py" --metric p50_ms --direction lower
/hub:init --task "Refactor auth" --agents 2                  # No eval (LLM judge mode)
```

## What It Does

### If arguments provided

Pass them to the init script:

```bash
python {skill_path}/scripts/hub_init.py \
  --task "{task}" --agents {N} \
  [--eval "{eval_cmd}"] [--metric {metric}] [--direction {direction}] \
  [--base-branch {branch}]
```

### If no arguments (interactive mode)

Collect each parameter:

1. **Task** — What should the agents do? (required)
2. **Agent count** — How many parallel agents? (default: 3)
3. **Eval command** — Command to measure results (optional — skip for LLM judge mode)
4. **Metric name** — What metric to extract from eval output (required if eval command given)
5. **Direction** — Is lower or higher better? (required if metric given)
6. **Base branch** — Branch to fork from (default: current branch)

### Output

```
AgentHub session initialized
  Session ID: 20260317-143022
  Task: Optimize API response time below 100ms
  Agents: 3
  Eval: pytest bench.py --json
  Metric: p50_ms (lower is better)
  Base branch: dev
  State: init

Next step: Run /hub:spawn to launch 3 agents
```

For content or research tasks (no eval command → LLM judge mode):

```
AgentHub session initialized
  Session ID: 20260317-151200
  Task: Draft 3 competing taglines for product launch
  Agents: 3
  Eval: LLM judge (no eval command)
  Base branch: dev
  State: init

Next step: Run /hub:spawn to launch 3 agents
```

## Baseline Capture

If `--eval` was provided, capture a baseline measurement after session creation:

1. Run the eval command in the current working directory
2. Extract the metric value from stdout
3. Append `baseline: {value}` to `.agenthub/sessions/{session-id}/config.yaml`
4. Display: `Baseline captured: {metric} = {value}`

This baseline is used by `result_ranker.py --baseline` during evaluation to show deltas. If the eval command fails at this stage, warn the user but continue — baseline is optional.

## After Init

Tell the user:
- Session created with ID `{session-id}`
- Baseline metric (if captured)
- Next step: `/hub:spawn` to launch agents
- Or `/hub:spawn {session-id}` if multiple sessions exist
