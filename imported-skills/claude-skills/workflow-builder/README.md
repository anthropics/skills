# workflow-builder (skill)

Intake-first authoring of deterministic multi-agent **workflow `.js` files** for Claude Code's Workflow tool (`CLAUDE_CODE_WORKFLOWS=1`, `/workflows`). See the plugin root [README](../../README.md) for the full overview and attribution.

## Tools (`scripts/`)

| Tool | Purpose |
|---|---|
| `workflow_intake.py` | Classify a (vague) task → recommended topology + runner-up + per-stage model plan + budget guard + rationale. |
| `validate_workflow.py` | Lint a workflow `.js`: pure-literal `meta`, no non-determinism, no Node/FS APIs, `parallel()` thunks, guarded loops, `filter(Boolean)`, size cap. PASS / WARN / FAIL with line numbers. |
| `scaffold_workflow.py` | Emit a runnable starter for any of 5 topologies (fan-out, pipeline, barrier, loop, judge-panel). |

All three run with `--sample` (no args) and `--help`.

## Quick start

```bash
python scripts/workflow_intake.py --task "review my open PRs for bugs"
python scripts/scaffold_workflow.py --topology pipeline --name pr-triage \
  --description "Triage open PRs" > /tmp/pr-triage.js
python scripts/validate_workflow.py /tmp/pr-triage.js
```

## Layout

- `references/` — API surface, orchestration patterns, decision + intake guide.
- `assets/templates/` — fan-out / pipeline / loop-until-budget starters.
- `assets/examples/` — a complete PR-triage workflow.
- `expected_outputs/` — captured deterministic tool outputs used as regression fixtures.

## License

MIT.
