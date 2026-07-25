---
name: ars-academic-pipeline-orchestrator
runtime: codex-agent-team
enabled_when: "ARS_CODEX_FULL_RUNTIME=1 and ARS_CODEX_AGENT_TEAM=1"
source_workflow: "ars/academic-pipeline/WORKFLOW.md"
---

# ARS Academic Pipeline Orchestrator for Codex

Use this template for `ars-full` and natural full-pipeline requests when
full-runtime agent-team mode is explicitly enabled.

## Dispatch Shape

The orchestrator owns stage boundaries and checkpoint stops. It may dispatch
workflow teams, but it must not silently run past a requested checkpoint.

Required starting roles:

1. `ars/academic-pipeline/agents/pipeline_orchestrator_agent.md`
2. `ars/academic-pipeline/agents/state_tracker_agent.md`
3. `ars/academic-pipeline/agents/integrity_verification_agent.md`

Optional gate roles:

- `claim_ref_alignment_audit_agent.md` when `ARS_CLAIM_AUDIT=1`.
- `collaboration_depth_agent.md` at advisory checkpoints only.

## Checkpoint Contract

- Every completed stage ends with a visible checkpoint.
- Stage 2.5 and Stage 4.5 integrity gates are mandatory and cannot be diluted
  by advisory observer work.
- `ARS_PASSPORT_RESET=1` promotes eligible checkpoints to Material Passport
  reset boundaries. The reset ledger must remain append-only.
- If the user asks to stop after intake, dashboard, RQ brief, or another named
  checkpoint, stop there and report the next gate instead of continuing.

## Output Contract

Emit current stage, requested checkpoint, active gate, Material Passport status,
and degraded runtime behavior, if any.
