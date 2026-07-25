# Design — #111 slr_lineage emission on systematic-review → academic-paper full handoff

**Date**: 2026-05-15
**Issue**: #111 (parented to #108 PR #110 commit 70c8678)
**Status**: implemented (commit 7a2f789 on feat/111-slr-lineage-emission; pending PR)
**Scope**: pipeline plumbing only. NO change to #108 referee, anchor table, protocol doc, or v3.2 venue track.

---

## 1. Problem

`disclosure` mode with `--policy-anchor=prisma-trAIce` reads `slr_lineage: bool` at renderer time per the G2 invariant track gate (`policy_anchor_disclosure_protocol.md` §3.1). When the user runs the documented `deep-research systematic-review → academic-paper full → disclosure --policy-anchor=prisma-trAIce` pipeline path, the renderer currently sees `slr_lineage=false` because no upstream component sets it. The user must manually supply `mode=systematic-review` to dispatch — defeating the intended automatic SLR dispatch.

`disclosure` is a finishing step invoked standalone after pipeline completion (academic-paper SKILL.md line 278); the renderer cannot read live `state_tracker` state. The only cross-session, cross-skill carrier is the Material Passport (Schema 9).

## 2. Decision Doc anchors (frozen, do not re-litigate)

- §4.3 G2 invariant — SLR mode dispatches to PRISMA-trAIce track; non-SLR modes dispatch to general track
- §4.4 #1 — track-selection lookup resolved as **(b) explicit `slr_lineage` input** (impl-spec §3 row #1, user-chosen)
- §4.4 #11 + impl-spec §3 row #11 — G1 invariant scoped to *corpus entry schema* (`literature_corpus_entry.schema.json`); non-renderer code changes for pipeline plumbing **permitted**

## 3. Boundary distinction (load-bearing)

| Schema | G1 status |
|---|---|
| `literature_corpus_entry.schema.json` (corpus entry, per-source row) | **FROZEN** — no fields added |
| Schema 9 Material Passport (run-level provenance) | **PERMITTED** — extended in v3.6.3 (`reset_boundary[]`), v3.6.4 (`literature_corpus[]`), v3.6.7 (`audit_artifact[]`) per the same pattern |

Adding `slr_lineage` to Schema 9 Material Passport top-level is **not** a corpus entry schema mutation and is **not** a G1 invariant violation. The lint and audit trail must treat the distinction explicitly so future audit rounds don't false-flag.

## 4. Design — three pieces

### 4.1 Schema 9 extension

Add one top-level optional field to Material Passport (Schema 9):

| Field | Type | Description |
|---|---|---|
| `slr_lineage` | boolean | `true` iff any pipeline stage in this run history was deep-research `systematic-review` mode. Set by `pipeline_orchestrator_agent` at the documented handoff point. Omittable; absence is semantically equivalent to `false` (renderer treats unset as cold-start). |

Backward compat: passports written by pre-#111 runs lack the field; renderer defaults to cold-start path (requires explicit `mode=` per §3.1 G2 invariant fallback rule, identical to current behavior).

### 4.2 Emission point

`pipeline_orchestrator_agent.md` emits `slr_lineage` at the Stage 1 → Stage 2 handoff (the only transition where new deep-research lineage can enter the run). After Stage 1/2/3 schema validation, the orchestrator computes:

```
slr_lineage_out = bool(incoming_passport.slr_lineage) or any(
    stage.skill == "deep-research" and stage.mode in {"systematic-review", "slr"}
    for stage in state_tracker.stages.values()
)
```

The OR with `incoming_passport.slr_lineage` is **load-bearing** (codex round-1 [P2] closure): a `resume_from_passport=<hash>` session has an empty `state_tracker.stages` (reconstructed from ledger only); recomputing from stages alone would overwrite a persisted `true` and defeat #111's auto-dispatch goal. A monotonic flag never flips back to `false`. Reference helper: `scripts/slr_lineage.py` `emit(stages, incoming_slr_lineage)`.

**Reset-boundary path (codex round-2 [P2] closure, refined round-3 [P2] closure):** under `ARS_PASSPORT_RESET=1` + `systematic-review` mode, the v3.6.3 reset protocol (`academic-pipeline/references/passport_as_reset_boundary.md`) freezes a passport at the FULL checkpoint **and halts before the Stage 1 → Stage 2 handoff**. Handoff-only emission would therefore miss the only write opportunity, and the resuming fresh session would see an empty `state_tracker.stages` + flag-less incoming passport → OR resolves false → PRISMA-trAIce blocks. Fix: the orchestrator prose at §"Run-level lineage emission" specifies that `emit()` runs **before any passport write** (handoff + reset-boundary). Honest accounting (round-3 closure): `slr_lineage` lives at passport top-level — NOT inside the `reset_boundary[]` ledger entry — so the v3.6.3 boundary hash (JCS over ledger entries only, see `passport_as_reset_boundary.md` §"The reset boundary protocol") does **not** cover this field. Same trust model as the other Schema 9 top-level fields. The need is correctness-at-write, not integrity-after-write.

**Import ergonomics (codex round-2 [P2] closure):** `scripts/slr_lineage.py` uses a `try: from scripts.policy_anchor_disclosure_referee import SLR_MODES; except ImportError: from policy_anchor_disclosure_referee import SLR_MODES` dual-path import. The repo has both namespace-style callers (`from scripts.<module>` per `test_check_sprint_contract.py`) and sibling-style callers (sys.path-prepending per `test_slr_lineage_emission.py`). Both paths resolve to the same module — single source of truth for `SLR_MODES` preserved.

`origin_mode` on each artifact's passport remains as today (records the *directly-producing* skill's mode). `slr_lineage` is run-level provenance, not artifact-level, so it sits at passport top-level alongside `origin_skill` / `version_label`.

Pattern precedent: this mirrors the v3.7.1 Cite-Time Provenance Finalizer (line 605 of `pipeline_orchestrator_agent.md`) — orchestrator computes a derived signal at a stage transition and persists it for downstream consumers.

### 4.3 Handoff contract documentation

`shared/handoff_schemas.md` Schema 9 gains an optional-fields row + a short subsection describing:
- semantics (run-level, derived from any-SLR-stage scan)
- producer (`pipeline_orchestrator_agent` at handoff transitions)
- consumer (`disclosure` mode renderer via `policy_anchor_disclosure_referee.RendererInputs.slr_lineage`)
- backward compat (absence = cold-start, identical to pre-#111 behavior)
- G1 boundary note (passport-level vs corpus-entry-level distinction)

### 4.4 e2e fixture

One conformance test under `scripts/` (mirroring `test_policy_anchor_disclosure.py` shape) exercising:

1. Build a synthetic passport with `stages["1"].mode = "systematic-review"`, `stages["2"].mode = "full"`
2. Run orchestrator handoff logic (or its computational equivalent — see §6 implementation note)
3. Assert outgoing passport carries `slr_lineage: true`
4. Pass that passport to `policy_anchor_disclosure_referee` with `--policy-anchor=prisma-trAIce`
5. Assert no `G2 TrackGateError`, no manual `mode=` supplied

Plus three negative cases:
- Stage 1 mode = `full` (non-SLR) → passport `slr_lineage: false` → `prisma-trAIce` selector errors with G2 (existing behavior preserved)
- Pre-#111 passport (no field) → renderer cold-start path (existing behavior preserved)
- Pipeline with no Stage 1 (mid-entry from Stage 2) → no `systematic-review` evidence → `slr_lineage: false`

## 5. Files touched

| File | Change kind |
|---|---|
| `shared/handoff_schemas.md` | additive — optional field row + subsection |
| `academic-pipeline/agents/pipeline_orchestrator_agent.md` | additive — emission step in §4 Transition Management |
| `scripts/test_slr_lineage_emission.py` (new) | e2e conformance fixture |
| `CHANGELOG.md` | append release note under v3.7.x |

### Files explicitly NOT touched (matches #111 §Scope out-of-scope)

| File | Reason |
|---|---|
| `scripts/policy_anchor_disclosure_referee.py` | #108 referee — contract already correct |
| `academic-paper/references/policy_anchor_disclosure_protocol.md` | #108 protocol — contract already correct |
| `academic-paper/references/policy_anchor_table.md` | #108 anchor table |
| `academic-paper/references/disclosure_mode_protocol.md` | v3.2 venue track + #108 anchor track dispatch — already references `slr_lineage` as pipeline-supplied |
| `shared/contracts/passport/literature_corpus_entry.schema.json` | G1 frozen (corpus entry schema, not passport schema) |
| Any test under `scripts/test_policy_anchor_*.py` | #108 conformance baseline (1053 tests must stay green) |

## 6. Implementation note — orchestrator is LLM prose, not Python

`pipeline_orchestrator_agent.md` is an LLM-orchestrated agent prompt, not Python. The "emission logic" lives in prose instruction to the LLM at the handoff step.

The e2e fixture under §4.4 cannot dispatch the actual agent; instead it tests:

- (a) the *resolution function* (whether `slr_lineage` would be true given a `state_tracker.stages` snapshot) as a small pure Python helper under `scripts/`, callable by both the conformance test and (optionally) future Python tooling
- (b) the *renderer integration* — passport with `slr_lineage: true` → referee accepts `--policy-anchor=prisma-trAIce` without `mode=`

Discipline: keep the helper minimal. No new orchestration framework, no Python wrapper around the LLM agent. Resolution is one any() over a dict.

## 7. Regression budget

- 1053 baseline tests must stay green (no #108 contract drift)
- +4 new tests minimum (1 positive + 3 negative per §4.4)
- No new lint
- No frontmatter change to existing skills

## 8. Open questions

None at design time. All §4.4 Decision Doc concerns are frozen by impl-spec; the only branch is §4 / B1 above (Schema 9 top-level field), and it is selected.

## 9. Out of scope (defer to future issues)

- v3.7.x other lineage signals beyond SLR (no demonstrated need)
- Replacing v3.7.1 finalizer pattern with a generic "derived signal" framework (premature abstraction)
- Cold-start manual `mode=` UX improvements (#111 is auto-dispatch path; cold-start is correct as-is)

---

## Related

- Parent: #108 (closed) + PR #110 merged 70c8678
- Decision Doc: `docs/design/2026-05-14-ai-disclosure-schema-decision.md` §4.3 G2 + §4.4 #1 + #11
- Impl spec: `docs/design/2026-05-14-ai-disclosure-impl-spec.md` §3 row #1 + #11
- Protocol: `academic-paper/references/policy_anchor_disclosure_protocol.md` §3.1
- Referee: `scripts/policy_anchor_disclosure_referee.py` `RendererInputs.slr_lineage`
- v3.7.1 pattern precedent: `academic-pipeline/agents/pipeline_orchestrator_agent.md` §"Cite-Time Provenance Finalizer (v3.7.1)" line 603
