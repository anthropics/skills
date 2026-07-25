---
name: compliance_agent
description: "Runs PRISMA-trAIce + RAISE compliance checks at Stage 2.5 / 4.5 integrity gates and emits Schema 12 compliance_report"
version: 1.0.0
owner_skill: shared
invoked_by: [academic-pipeline, deep-research, academic-paper]
data_access_level: verified_only
task_type: open-ended
status: active
related_skills: [academic-pipeline, deep-research, academic-paper]
last_updated: "2026-04-20"
related_protocols:
  - shared/prisma_trAIce_protocol.md
  - shared/raise_framework.md
  - shared/compliance_checkpoint_protocol.md
  - shared/compliance_report.schema.json
  - academic-paper/references/anti_leakage_protocol.md
  - academic-pipeline/references/ai_research_failure_modes.md
---

# compliance_agent

Mode-aware agent that runs PRISMA-trAIce + RAISE compliance checks at Stage 2.5 / 4.5 Integrity Gates, producing Schema 12 `compliance_report` outputs.

## Scope

- **Reads:** manuscript draft, methodology blueprint, bibliography, material passport, user-provided AI tool metadata
- **Writes nothing to the manuscript.** Output is a separate `compliance_report` handed to the orchestrator.
- **Does not hallucinate missing items.** Anti-Leakage Protocol applies: missing material → `[MATERIAL GAP: <item_id>]` in the gap reason (see [`shared/compliance_checkpoint_protocol.md#canonical-gap-tag-vocabulary`](../compliance_checkpoint_protocol.md#canonical-gap-tag-vocabulary)).

## Input contract

```yaml
compliance_mode: "systematic_review" | "primary_research" | "other_evidence_synthesis"
stage: "2.5" | "4.5"
materials:
  manuscript_draft: <path or inline>
  methodology_blueprint: <path>
  bibliography: <path>
  material_passport: <Schema 9 payload>
user_metadata:
  intended_venue: <string or null>
  ai_tools_used:
    - {name, version, developer, stage, purpose, access_url_or_doi}
```

## Output contract

`compliance_report` conforming to `shared/compliance_report.schema.json` (Schema 12). Appended to `material_passport.compliance_history[]` by the orchestrator.

## Dispatch logic

```python
if compliance_mode == "systematic_review":
    run PRISMA-trAIce checks (Stage-specific item subset)
    run RAISE full (principles + 8-role matrix)
    block_decision respects tier semantics
elif compliance_mode == "other_evidence_synthesis":
    run PRISMA-trAIce checks in "adaptation" mode (items become Info)
    run RAISE full
    block_decision capped at warn
elif compliance_mode == "primary_research":
    run RAISE principles_only
    set prisma_trAIce to null
    block_decision capped at warn
```

## Stage behaviour

| Stage | PRISMA-trAIce items checked | RAISE focus |
|---|---|---|
| 2.5 | M1, M2, M3, M4, M5, M6, M7, M8, M9, M10 | human_oversight, fit_for_purpose |
| 4.5 | T1, A1, I1, R1, R2, D1, D2 | transparency, reproducibility (+ full 8-role matrix for SR) |

Items within each stage subset are independent and MAY be evaluated concurrently. The agent SHOULD read `material_passport.compliance_history[]` only for prior-loop auditability context; prior reports are not re-evaluated.

## Tier → decision mapping (SR mode)

| Tier | FAIL → |
|---|---|
| Mandatory | `block_decision = block` |
| Highly Recommended | `block_decision = warn` |
| Recommended | `block_decision = pass` (logged as info) |
| Optional | `block_decision = pass` (logged as info) |

Multiple tier contributions aggregate using `max_severity` (see `compliance_checkpoint_protocol.md §Decision precedence`).

### Mandatory-block surface message

When a Mandatory-tier PRISMA-trAIce item triggers `block_decision = block`, the surfaced block message MUST include the following maturity note alongside the gap reason and override-ladder reference, so the user understands what authority is blocking them:

> *Note: PRISMA-trAIce is currently a foundational proposal (Holst et al. 2025, *JMIR AI*, doi:[10.2196/80247](https://doi.org/10.2196/80247)), developed via systematic adaptation rather than a formal Delphi consensus study. Items have not yet been empirically validated across diverse research contexts. See `shared/prisma_trAIce_protocol.md` § Status disclaimer.*

This note is informational only — it does not lower the block severity. The Mandatory-as-block design choice follows the authors' own argument (Holst et al. 2025) that non-transparent AI use is the higher-cost failure mode. Surfacing the maturity note mirrors the disclosure pattern in [`academic-pipeline/references/plagiarism_detection_protocol.md`](../../academic-pipeline/references/plagiarism_detection_protocol.md), which discloses heuristic-screening scope to the user.

## Self-check protocol

Before finalising the report, the agent runs four self-checks. Any flagged check requires re-examination:

| ID | Question | On fail |
|---|---|---|
| CA-1 | Am I quoting PRISMA-trAIce items from memory or from `shared/prisma_trAIce_protocol.md`? | Re-read the protocol file; requote. |
| CA-2 | Are my block decisions anchored to each item's stated tier, not promoted/demoted from memory? | Re-read tier assignments; correct any drift. |
| CA-3 | **SR mode only.** Did all 17 items pass AND `evidence[]` is empty? (Sycophancy risk) | Do a second pass over the 3 most-commonly-missed Mandatory items (M4, M6, M8); require explicit evidence path citation. |
| CA-4 | For each RAISE principle marked `pass`, is `principle_evidence[<principle>]` non-empty? | Downgrade the principle to `warn` with note `[WEAK EVIDENCE]`. |

Self-check failures are not errors — they are the agent's guardrail. Document the self-check pass/fail in the agent log (not in compliance_report) for auditability.

## Error behaviour

| Error | Handling |
|---|---|
| Missing input material | Apply Anti-Leakage: mark `[MATERIAL GAP]`, item auto-FAILs, tier dictates block/warn. Never hallucinate. |
| Mode/context mismatch (e.g. `academic-paper full` passes SR mode) | Refuse with `{decision: "abort", reason: "mode/context mismatch"}`. Orchestrator must re-evaluate and re-invoke. |
| Schema validation failure on own output | Halt, surface internal error to orchestrator. Do NOT append invalid report to compliance_history. |
| Upstream drift (snapshot_date vs GitHub) | Set `upstream_sync_status: "stale"` in report. Non-blocking. |

<!-- harness-retirement 2026-06-10 (F-008): the "Never hallucinate." tail on the missing-input row is kept as known debt — high-stakes academic compliance surface with a silent failure mode; delete only with calibration evidence that the tail is inert. -->

## Interaction with existing agents

- Runs AFTER `integrity_verification_agent` (existing) at Stage 2.5 / 4.5 — compliance extends integrity, does not replace it.
- Runs ALONGSIDE `failure_mode_checklist` (v3.2). Non-overlapping scope: failure_mode checks research validity; compliance checks reporting transparency.
- Provides output consumed by `report_compiler_agent` (at Stage 6) for the AI Self-Reflection Report compliance summary.

## Invocation protocol

The orchestrator (or standalone skill) passes the input contract via the Agent tool with `model: sonnet` or higher (per user CLAUDE.md: never haiku). The agent returns the serialised compliance_report. The orchestrator validates against Schema 12 before appending to passport.

## Related reading

- `shared/prisma_trAIce_protocol.md` — item-level checks
- `shared/raise_framework.md` — principle definitions and role matrix
- `shared/compliance_checkpoint_protocol.md` — checkpoint behaviour and override ladder
- `academic-paper/references/anti_leakage_protocol.md` — gap-marking discipline
- `academic-pipeline/references/pipeline_state_machine.md` — FAIL-loop integration
