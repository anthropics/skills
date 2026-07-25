# ARS Shared Contracts

Schema files for cross-skill contracts: reviewer sprint contracts, Material Passport
ports, and (v3.6.7+) cross-model audit artifact pipelines.

## Sprint contracts (v3.6.2+)

Sprint contract templates for reviewer hard-gate orchestration.

Schema: `shared/sprint_contract.schema.json` (Schema 13).
Validator: `scripts/check_sprint_contract.py`.
Spec: `docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md`.
Protocol: `academic-paper-reviewer/references/sprint_contract_protocol.md`.

### Shipped templates

**v3.6.2 (reviewer family)**:

- `reviewer/full.json` — panel 5, 5 dimensions, 4 failure conditions
- `reviewer/methodology_focus.json` — panel 2, 2 dimensions, 3 failure conditions

**v3.6.6 / suite v3.6.8 (generator-evaluator family)**:

- `writer/full.json` — single-agent writer, 7 dimensions (D1 section_completeness / D2 citation_density / D3 argument_blueprint_fidelity / D4 total_word_count / D5 per_section_word_count / D6 acknowledged_limitations / D7 register_consistency), 5 failure conditions (F1 / F4 / F2 / F3 / F0). No `scoring_plan` field.
- `evaluator/full.json` — single-agent evaluator, 5 dimensions (D1 originality / D2 methodological_rigor / D3 evidence_sufficiency / D4 argument_coherence / D5 writing_quality), 7 failure conditions (F1 / F2 / F3 / F6 / F4 / F5 / F0). Carries full `scoring_plan` + `disagreement_handling`.

Both writer + evaluator templates ship under Schema 13.1 (allOf branches 11/12 require `pre_commitment_artifacts` for `writer_full` and `disagreement_handling` for `evaluator_full`; branches 5/6 pin `failure_conditions[].action` to mode-specific enums; branches 8/9 pin F0 contains to the mode's accept variant). Orchestration block lives in `academic-paper/SKILL.md` § "v3.6.6 Generator-Evaluator Contract Protocol" + the writer/evaluator agent files.

### Reserved reviewer modes without shipped templates

`reviewer_re_review`, `reviewer_calibration`, `reviewer_guided` are in the schema enum
but ship without templates in v3.6.2. Those modes continue to operate in their existing
form (no contract, no hard-gate) until a follow-up patch release adds their templates.

### How to add a new template

1. Add the file under `shared/contracts/<domain>/<mode>.json`.
2. Run `python scripts/check_sprint_contract.py <path> --ars-version vX.Y.Z`; expect
   zero errors and zero soft warnings.
3. If `expression` strings use new phrasing, update `sprint_contract_protocol.md`
   and the synthesizer prompt's recognised-pattern list in the same PR.

## Passport contracts (v3.6.4+)

Schemas for Material Passport input ports.

- `passport/literature_corpus_entry.schema.json` (v3.6.4) — Schema 9 `literature_corpus[]`
  entries produced by user-written adapters.
- `passport/rejection_log.schema.json` (v3.6.4) — adapter output companion logging
  entries that could not be included in the corpus.
- `passport/reset_ledger_entry.schema.json` (v3.6.3) — `reset_boundary[]` ledger entries
  for the opt-in passport reset boundary protocol.
- `passport/audit_artifact_entry.schema.json` (v3.6.7 Step 6) — `audit_artifact[]` entries
  recording one cross-model audit run per downstream-agent deliverable. Two lifecycle
  states (proposal / persisted) share the schema via `oneOf`. Cross-artifact invariants
  are enforced by `scripts/check_audit_artifact_consistency.py`. Spec:
  `docs/design/2026-04-30-ars-v3.6.7-step-6-orchestrator-hooks-spec.md` §3.1-§3.2.
- `passport/version_records.schema.json` (Kong #258) — optional
  `phase2_investigation/version_records.yaml` sidecar for academic citation version
  families (preprint -> proceedings -> journal extension). This is deliberately a
  sidecar: `literature_corpus_entry.schema.json` stays adapter-owned and unmodified.

## Audit artifact contracts (v3.6.7 Step 6)

The `audit/` directory carries the three wrapper-emitted artifact schemas that pair
with the passport-side `audit_artifact_entry.schema.json` above. Together they form
the four-schema contract that `scripts/run_codex_audit.sh` (Phase 6.1) writes and the
orchestrator agent reads at every per-agent audit gate.

- `audit/audit_jsonl.schema.json` — Layer 2 evidence: per-row schema for the codex CLI
  0.125+ `--json` event stream (`thread.started` / `turn.started` / `item.completed` /
  `turn.completed` / `error`). One JSONL line per event row.
- `audit/audit_sidecar.schema.json` — Layer 3 evidence: runner / timing / process /
  stream / prompt metadata. Cross-file rules linking sidecar fields to JSONL events,
  on-disk files, and passport entries (B1-B7 in spec §3.7 family B) are enforced by
  `scripts/check_audit_artifact_consistency.py` (Phase 6.3), not by this schema alone.
- `audit/audit_verdict.schema.json` — verdict file shape (PASS / MINOR / MATERIAL /
  AUDIT_FAILED). The artifact orchestrator parses for ship/block decisions; cross-field
  consistency with `finding_counts` and `failure_reason` is lint-enforced per
  spec §3.7 A1 / A2 / A5 / A6.

Spec: `docs/design/2026-04-30-ars-v3.6.7-step-6-orchestrator-hooks-spec.md` §3.
