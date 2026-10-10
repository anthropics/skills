# skill_eval_mcp

MCP server exposing skill-creator's Phase 3 trigger evaluation pipeline as
LLM-callable tools. Lets any agent (Claude Code, Cursor, Cline, raw API)
run a real-world trigger evaluation against an installed skill, kick off
an optimization loop, and apply the winning description back to `SKILL.md`.

## Stack

- **Language:** Python 3.10+
- **SDK:** `mcp[cli]` (FastMCP) + Pydantic v2
- **Transport:** stdio (local Claude Code integration)
- **Auth:** none — inherits parent CC's OAuth via the `claude -p`
  subprocesses spawned by `run_eval.run_single_query`

## Tools (8)

All service-prefixed `skill_eval_*` to avoid collisions:

| Tool                                  | Purpose                                              | Sync? |
|---------------------------------------|------------------------------------------------------|-------|
| `skill_eval_list_skills`              | enumerate ~/.claude/skills/*                         | sync  |
| `skill_eval_get_skill`                | description + auto-discovered candidate eval sets    | sync  |
| `skill_eval_run_trigger_eval`         | one-shot eval, returns precision/recall/accuracy     | sync  |
| `skill_eval_start_optimization`       | full eval+improve loop in background, returns run_id | async |
| `skill_eval_get_run_status`           | poll run by id                                       | sync  |
| `skill_eval_list_runs`                | list active + recent runs                            | sync  |
| `skill_eval_apply_best_description`   | write best description to SKILL.md                   | sync  |
| `skill_eval_stop_run`                 | cooperative stop                                     | sync  |

All inputs validated by Pydantic models with `extra="forbid"` to reject
LLM hallucinated parameters. Tool descriptions are mini-manuals
(Args/Returns/Use-when/Notes) for unambiguous LLM use.

## Install

Bootstrap deps first:

```bash
cd skills/skill-creator/mcp
./start.sh   # creates .venv, installs mcp[cli] + pydantic, then runs server
# stdio server runs on stdin/stdout — no port to open. Ctrl+C to stop.
```

Register with Claude Code (user scope so it's available everywhere):

```bash
claude mcp add skill-eval --scope user --transport stdio -- \
  /home/johnzealanddoyle/skills/skills/skill-creator/mcp/start.sh
```

Or project-scoped (commit to `.mcp.json`):

```bash
claude mcp add skill-eval --scope project --transport stdio -- \
  ./skills/skill-creator/mcp/start.sh
```

Verify:

```bash
claude mcp list | grep skill-eval
```

## Use from Claude Code

Once installed, any agent in any session can call:

```
skill_eval_list_skills()
skill_eval_get_skill(name="medusa-pro")
skill_eval_run_trigger_eval(
    skill_path="/home/.../medusa-pro",
    eval_set_path="/home/.../medusa-pro-workspace/trigger-eval.json",
    description="Use this skill when ...",  # optional
    model="claude-sonnet-4-6",
    runs_per_query=2
)
# Returns: {precision, recall, accuracy, results, elapsed_s}
```

For a long optimization:

```
{run_id} = skill_eval_start_optimization(
    skill_path=...,
    eval_set_path=...,
    max_iterations=3,
    holdout=0.4
)
# Poll periodically:
status = skill_eval_get_run_status(run_id=run_id)
# When status.status == "complete":
skill_eval_apply_best_description(run_id=run_id)
```

## Why this exists

`skill-creator` ships a CLI (`python -m scripts.run_loop`) but it's
awkward for agents to drive — they'd need to spawn a subprocess, parse
stdout JSON, manage backpressure, etc. The MCP server packages the same
logic as first-class LLM tools.

The `eval-server` SSE dashboard (`../eval-server/`) is the human-facing
counterpart — same primitives, web UI instead of MCP.

## Files

```
mcp/
├── README.md           this file
├── server.py           FastMCP server + 8 tool definitions
├── start.sh            venv bootstrap + stdio launcher
└── requirements.txt    mcp[cli] + pydantic
```

## Compliance

Designed against `mcp-server-best-practices` skill v0.5.1:

- Service-prefixed tool names (`skill_eval_*`)
- Pydantic v2 with `extra="forbid"` on all inputs
- Tool annotations (`readOnlyHint`, `destructiveHint`, `idempotentHint`, `openWorldHint`)
- Mini-manual docstrings (Args / Returns / Use-when / Notes)
- Error bifurcation
- stdout reserved for JSON-RPC; logs to stderr
- stdio transport (recommended for local CC integration)
