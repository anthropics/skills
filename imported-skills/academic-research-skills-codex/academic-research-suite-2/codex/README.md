# ARS Codex Full-Runtime Adapter

This directory is the Codex-only runtime adapter for
`academic-research-suite`. Vendored upstream content remains under `ars/`; do
not hand-edit it except through an explicit upstream sync or documented path
patch.

## Runtime Profiles

Default behavior remains inline:

```text
Use $academic-research-suite: ars-plan ...
```

The root router reads the relevant `ars/*/WORKFLOW.md` and agent prompt files,
then performs the phase in the current Codex conversation.

Full-runtime behavior is opt-in:

```bash
export ARS_CODEX_FULL_RUNTIME=1
export ARS_CODEX_AGENT_TEAM=1
export ARS_CODEX_HOOKS=1
```

- `ARS_CODEX_FULL_RUNTIME=1` enables structured command routing and gate
  planning through `codex/scripts/ars_codex_full_runtime.py`.
- `ARS_CODEX_AGENT_TEAM=1` permits planner-driven Codex agent-team dispatch
  using templates under `codex/agents/`.
- `ARS_CODEX_HOOKS=1` permits manual installation of the disabled-by-default
  hook pack in `codex/hooks/`.

If a flag is absent, the adapter degrades to inline role-prompt execution and
must report that degraded behavior.

## Main Files

- `full-runtime-manifest.json` is the adapter contract: command aliases,
  workflow mapping, agent-team rules, quality gates, hook pack, and known
  degradations.
- `scripts/ars_codex_full_runtime.py` turns a request into a deterministic JSON
  plan. It is read-only and safe to run in tests.
- `scripts/ars_codex_quality_gates.py` validates adapter packaging, hook safety,
  reviewer independence fixtures, and upstream lock provenance.
- `agents/*.md` are Codex subagent templates. They point back to vendored ARS
  source prompts rather than duplicating upstream prompt bodies.
- `compatibility-matrix.md` records Claude Code parity, remaining gaps, and
  verification methods.

## Agent-Team Semantics

The adapter cannot promise byte-for-byte Claude Code Agent Team behavior.
Instead it provides an explicit Codex orchestration contract:

- reviewer panels produce independent reviewer sections before synthesis;
- synthesis preserves minority and dissenting findings unless resolved by
  evidence and severity;
- pipeline orchestration stops at requested checkpoints;
- Codex model routing uses the active model while preserving upstream
  `opus`/`sonnet` hints as metadata;
- ARS v3.16 model tiering is surfaced as advisory metadata; it is applied only
  when a Codex runtime provides explicit per-dispatch model selection;
- inline mode remains available and is the default.

## Verification

Run the adapter smoke/parity checks from the repository root:

```bash
python3 skills/academic-research-suite/codex/scripts/ars_codex_quality_gates.py all
python3 -m pytest skills/academic-research-suite/codex/tests
```

Run upstream validators from the vendored ARS root as needed:

```bash
cd skills/academic-research-suite/ars
python3 -m pytest scripts/test_codex_router_policy.py
python3 scripts/check_passport_reset_contract.py
python3 scripts/check_v3_9_2_phase_boundary.py
```
