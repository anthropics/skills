---
name: ars-experiment-team
runtime: codex-agent-team
enabled_when: "ARS_CODEX_FULL_RUNTIME=1 and ARS_CODEX_AGENT_TEAM=1"
source_workflow: "ars/experiment-agent/WORKFLOW.md"
---

# ARS Experiment Team for Codex

Use for experiment planning, study protocol support, reproducibility planning,
and statistical interpretation when the user explicitly opts into full-runtime
agent-team mode.

## Source Prompts

- `ars/experiment-agent/agents/study_manager_agent.md`
- `ars/experiment-agent/agents/code_runner_agent.md`

## Output Contract

Separate design assumptions, runnable analysis plans, ethics/IRB constraints,
and reproducibility checks. Do not execute risky code or human-subject workflows
without explicit user approval and local safety review.
