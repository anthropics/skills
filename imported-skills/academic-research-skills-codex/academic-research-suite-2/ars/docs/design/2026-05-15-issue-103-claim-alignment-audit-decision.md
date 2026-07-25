# ARS v3.8 — Issue #103 `claim_ref_alignment_audit_agent` Decision Doc

**Date:** 2026-05-15
**Issue:** [#103](https://github.com/Imbad0202/academic-research-skills/issues/103)
**Target release:** v3.8
**Scope:** L3 claim-faithfulness audit channel (LLM-as-judge against retrieved reference text), running on top of v3.7.3 anchor infrastructure.

This is the decision layer. The implementation surface lives in the companion spec `2026-05-15-issue-103-claim-alignment-audit-spec.md`.

---

## 1. Why a decision doc precedes the spec

#103 issue body already contains a frozen-looking design — 6 implementation surfaces, RubricEM borrow scope boundaries, an 8-stage defect_stage matrix, acceptance criteria. But the body also surfaces **7 open questions** marked as deferred-to-decision, and pipeline inventory turned up an **8th boundary question** (`claim_audit_results[]` vs `audit_artifact[]` lifecycle) that the body does not address.

Without resolving these eight, the implementation spec cannot pin down:
- whether the audit agent runs at all on `anchor=none` inputs,
- which severity tier paywall-failures get,
- whether `claim_intent_manifest` can gate-refuse output,
- where `claim_audit_results[]` plugs into the orchestrator dispatch graph.

Each of those answers shapes the schema, the agent prompt, and the finalizer integration. So they land here first, then the spec lands on top of them. This mirrors the #106 → #108 → #110 three-stage pattern but compressed: discovery is collapsed into the decision doc (the issue body already did most of it), and the spec then walks straight into TDD.

## 2. Provenance — what is NOT being re-invented

The decisions below were filtered against five existing artifacts to avoid breaking established invariants:

- **v3.7.3 spec** (`docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`) — defines anchor schema (§3.1), the 5-cell finalizer matrix, R-L3-1-A/B/C firm rules, and the explicit boundary that **v3.7.3 does NOT do audit, v3.8 does**. Specifically R-L3-1-A makes `<kind>` ≠ `none` **production-mandatory**; any `none` is already gate-refused by `formatter_agent` / `cite_provenance_terminal_gate_agent` and cannot reach the audit agent in legitimate production prose.
- **v3.6.6 generator/evaluator contract** (`docs/design/2026-04-27-ars-v3.6.6-generator-evaluator-contract-design.md` §3.6 + D4) — `pre_commitment_artifacts` is the paper-blind contract baseline; runtime/paper-visible observations never enter the schema. `claim_intent_manifest` must respect this boundary.
- **v3.6.7 Step 6 Audit Artifact Gate** (`pipeline_orchestrator_agent.md` §3.5; `shared/contracts/passport/audit_artifact_entry.schema.json`) — `audit_artifact[]` is **cross-model deliverable audit**, agent enum locked to `{synthesis_agent, research_architect_agent, report_compiler_agent}`. The semantic is "did this stage-completion deliverable pass independent codex review". Claim-level alignment audit is a different semantic and gets its own lifecycle.
- **Material Passport entry-type schemas** (`shared/contracts/passport/*.schema.json`) — Material Passport is an aggregate concept; each entry type has its own schema (`audit_artifact_entry.schema.json`, `literature_corpus_entry.schema.json`, `rejection_log.schema.json`, `reset_ledger_entry.schema.json`). `claim_audit_result` adds a new entry-type schema (`claim_audit_result.schema.json`) and the orchestrator carries the aggregate `claim_audit_results[]` array. No root-level passport schema exists today; v3.8 does not introduce one.
- **Reviewer calibration protocol** (`shared/contracts/reviewer/`) — gold-set / FNR / FPR convention reused; not re-invented.

External sources informing the design:
- Zhao et al. arXiv:2605.07723 (2026-05) §1 — names "real citations deployed to support claims the cited references do not actually make" as the open challenge. §4 discusses LLM-as-judge as candidate detection.
- Li et al. arXiv:2605.10899 (2026) — RubricEM Stage-Structured GRPO; transferred as **prompt-time** decomposition (Borrows 1 & 2), not RL training.

## 3. Decisions

Eight decisions. Each names the question, the chosen path, the rejected path, the load-bearing reason, and the consequence on schema / agent / finalizer.

### D1 — Audit input requires anchor present (OQ1 closed)

**Question:** When the upstream emission carries `<!--anchor:none:-->`, should the audit agent retrieve the reference and ask the judge to find any support, or skip audit entirely?

**Decision:** **Skip audit. `anchor=none` is a v3.7.3 contract violation that has already been gate-refused upstream.**

The audit agent treats any received `anchor_kind=none` as a contract-violation signal: it emits a `claim_audit_result` with `judgment=RETRIEVAL_FAILED`, `defect_stage=not_applicable`, `audit_status=inconclusive`, and a rationale stating the violation. It does NOT invoke the LLM judge.

**Rejected:** Retrieve full reference and ask judge for any support. This contradicts v3.7.3 R-L3-1-A (production-mandatory locator) and would create a soft-bypass: a synthesis agent could emit `none` and rely on v3.8 audit to verify, defeating the precedence-zero gate that v3.7.3 just built. v3.7.3 spec §10 explicitly flags this rationalization ("Agents emit `<!--anchor:none:-->` reflexively to satisfy the contract, defeating the gate's purpose").

**Why:** Two reasons stack. (a) Production prose with `anchor=none` does not reach the audit input in legitimate runs — the v3.7.3 terminal gate refuses it. So the audit agent only sees `none` when the pipeline was already in a broken state; calling the judge there wastes inference cost on output that will be discarded. (b) Treating `none` as auditable would re-introduce the "free pass" pattern v3.7.3 explicitly engineered against (see v3.7.3 §10 trade-off table).

**Consequence:**
- Agent prompt: "STEP 1 — Anchor presence check. If anchor_kind=none, emit RETRIEVAL_FAILED + defect_stage=not_applicable + audit_status=inconclusive + rationale='v3.7.3 R-L3-1-A violation — upstream emission had no locator'. SKIP judge invocation."
- Backward compat: legacy v3.7.1 prose without anchors will surface `anchor_kind=none` to the audit agent (since audit dispatches at Stage 4→5 AFTER the v3.7.1/v3.7.3 cite finalizer pass but BEFORE the formatter hard gate, per spec §5 trigger boundary). When the audit agent sees `anchor_kind=none`, it does NOT call the judge — it emits the contract-violation claim_audit_result per Step 1 above. That result reaches the finalizer matrix, which routes it to the HIGH-WARN-CLAIM-AUDIT-ANCHORLESS row (defense-in-depth against v3.7.3 finalizer skip/stale paths — see spec §5 8-row matrix, the `(RETRIEVAL_FAILED, not_applicable, not_attempted)` row). The formatter hard gate then refuses output for that HIGH-WARN annotation. In practice, well-behaved v3.7.3+ prose never reaches this state because the v3.7.3 finalizer pass converts `anchor=none` markers into `[UNVERIFIED CITATION — NO QUOTE OR PAGE LOCATOR]` before audit dispatch — but the audit layer keeps the defense-in-depth row regardless.

### D2 — Paywall retrieval failures are LOW-WARN advisory (OQ2 closed)

**Question:** When the reference exists and is genuinely cited but no full-text API access exists (paywalled, restricted), severity tier?

**Decision:** **LOW-WARN-CLAIM-AUDIT-UNVERIFIED, advisory only, not gate-refused.**

Aligns with issue body's tentative answer. The audit agent emits `claim_audit_result` with `judgment=RETRIEVAL_FAILED`, `audit_status=inconclusive`, `ref_retrieval_method=failed`, `defect_stage=not_applicable`. Finalizer annotates `[CLAIM-AUDIT-UNVERIFIED — REFERENCE FULL-TEXT NOT RETRIEVABLE]` next to the citation. Terminal gate does NOT refuse output for UNVERIFIED markers.

**Rejected:** MED-WARN with gate-refuse. Would create huge noise on humanities/social-science papers whose references are >50% paywalled with no API. Signal-to-noise drops to zero; users get conditioned to ignore the gate.

**Why:** Retrieval failure ≠ claim unsupported. The audit is **measuring the system's ability to verify**, not the claim's truth-value. Conflating those collapses the signal. User remedy when they want hard verification: upload PDF manually, re-run audit. The advisory annotation is enough to surface "this one wasn't checked" without blocking output.

**Consequence:**
- New finalizer cell #7 (LOW-WARN tier alongside CLAIM-AUDIT-AMBIGUOUS).
- `claim_audit_result.ref_retrieval_method` enum includes `api`, `manual_pdf`, `failed`.
- `audit_status=inconclusive` MUST emit `defect_stage=not_applicable` (NOT `null`) — per #103 issue body acceptance criterion.

### D3 — Per-paper rate-limit + cache + shared calibration with negative-constraints (OQ3 + OQ5 closed)

**Question (OQ3):** Audit cost — 50-200 citations × API + judge inference per paper. Rate-limit / batching / caching?

**Question (OQ5):** Negative-constraint operationalization — bundle with main alignment calibration, or separate?

**Decision:** **Bundled. Single calibration mode protocol covering both. Cost controlled by per-paper claim cap + judge response cache.**

(a) Per-paper claim cap: default `MAX_AUDITED_CLAIMS_PER_PAPER=100`, configurable via passport input. When citation count exceeds cap, audit a stratified sample (every Nth claim) and annotate `[CLAIM-AUDIT-SAMPLED — k/N audited]` in finalizer report. No silent skipping.

(b) Judge response cache keyed by `(claim_text_hash, ref_slug, anchor_kind, anchor_value_hash, retrieved_excerpt_hash, active_constraints_hash, judge_model)` — a **seven-tuple**. The `active_constraints_hash` is SHA-256 over the canonical-form serialization of all manifest constraints that apply to this claim at audit time. The active-constraint set is built by joining on `(scoped_manifest_id, claim_id)`, NOT bare `claim_id` — when a passport contains multiple `claim_intent_manifests[]`, the same `C-001` may exist in different manifests with different `negative_constraints[]`, and selecting by bare claim_id would mix constraints from the wrong manifest (per M-INV-1, cross-manifest C-001 collision is permitted; the discriminator is the `(manifest_id, claim_id)` pair). The set is: top-level `manifest_negative_constraints[]` of the **specific manifest** whose `manifest_id == scoped_manifest_id` ∪ that manifest's `claims[].negative_constraints[]` entry whose `claim_id` matches the current claim, sorted by `constraint_id`, JCS-encoded. **Cache lookup runs AFTER retrieval, not before** — including the `retrieved_excerpt_hash` in the key means that if the user later uploads a manual PDF, corrects the corpus entry, or the slug resolves to a different excerpt for the same anchor, the cache miss forces fresh judging rather than reusing a stale verdict tied to the old source text. Including the `active_constraints_hash` means adding or modifying a negative constraint also forces fresh judging — otherwise a cached non-violation would silently bypass the new constraint's HIGH-WARN gate-refuse path. Cache lives at `${ARS_CACHE_DIR}/claim_audit_v1/` (env var, default `~/.cache/ars/claim_audit_v1/`). Cache eviction is user responsibility (`rm -rf`); no automatic TTL — judgments are deterministic given the same seven-tuple.

(c) Calibration: single gold-set covers both SUPPORTED/UNSUPPORTED/AMBIGUOUS/RETRIEVAL_FAILED judgments AND constraint VIOLATED/NOT_VIOLATED judgments. Gold tuple shape: `{tuple_kind, claim_text, ref_text_excerpt, anchor, expected_judgment, ...}` where `tuple_kind ∈ {alignment, constraint}` discriminates the two judgment lines. For `tuple_kind=alignment`, `expected_judgment ∈ {SUPPORTED, UNSUPPORTED, AMBIGUOUS, RETRIEVAL_FAILED}`. For `tuple_kind=constraint`, `expected_judgment ∈ {VIOLATED, NOT_VIOLATED}` AND `constraint_under_test_id` is **REQUIRED** (pattern `^(NC-C[0-9]{3,}-[0-9]+|MNC-[0-9]+)$`) AND `constraint_under_test_rule_text` is **REQUIRED** (the actual rule string used in the judge prompt; without it the negative-constraint judge prompt cannot evaluate). Alternative for `tuple_kind=constraint`: a per-tuple `manifest_fixture_path` field pointing to a manifest JSON whose `manifest_negative_constraints[]` or `claims[].negative_constraints[]` contains the constraint — calibration resolves rule text by id lookup. NOT_VIOLATED tuples are required to measure constraint **FPR** (false-positive rate — how often the judge wrongly flags a benign claim as violating); without them T-C1's `FPR < 0.10` threshold for the constraint line is uncomputable. FNR/FPR computed jointly per tuple_kind (alignment metrics + constraint metrics reported separately in T-C2, jointly thresholded in T-C1).

**Rejected:** Separate calibration protocols for alignment vs. negative-constraint. Would force user to curate two gold sets at typically N<20 each; v3.6.x calibration convention rejects N<10 hard guards (see `feedback_small_sample_hard_guard_caution.md`). Joint calibration trades resolution for statistical floor.

**Why:** Two pragmatic reasons + one principled. (1) Cache hit rate in practice will be high — same papers cite same references across repeated runs; users iterating drafts hit cache constantly. (2) Per-paper cap is the only way to bound worst-case cost without violating the "no silent skipping" rule the v3.6.x reviewer skill established. (3) Negative-constraint judgments and main alignment judgments share the same evaluator shape (claim + excerpt + verdict), so a shared gold-set is the lowest-overhead path to comparable FNR/FPR baselines.

**Consequence:**
- New file `academic-pipeline/references/claim_audit_calibration_protocol.md` (modeled on `shared/contracts/reviewer/` calibration).
- Passport input gains `claim_audit_config: {max_claims_per_paper, judge_model, gold_set_path, cache_dir}`.
- Cache schema: `${ARS_CACHE_DIR}/claim_audit_v1/<cache_key_sha256>.json` filesystem KV. File body stores only **judge-verdict + source-bound fields**: `judgment`, `audit_status`, `defect_stage`, `rationale`, `judge_model`, `judge_run_at`, `ref_retrieval_method`, `violated_constraint_id`. Run-local identifiers (`claim_id`, `audit_run_id`, `upstream_owner_agent`, `upstream_dispute`) are intentionally excluded — they are reconstructed from the current-run context on replay so the cached verdict for a given `(claim_text, ref, anchor, source-excerpt, constraints, judge_model)` can be reused across different drafts/manifest positions without misattribution. Replay rejoins cached block + current-run identifiers to produce a valid `claim_audit_result` entry. Cache-side metadata (mtime) lives on the filesystem, never inside the JSON body.
- Calibration acceptance: combined FNR < 0.15, FPR < 0.10. Same threshold for both judgment types because the joint gold-set is the unit of measurement.

### D4 — `claim_intent_manifest` is advisory non-blocking; stage-attribution disagreement is recorded not arbitrated; uncited threshold has 3 operational rules (OQ4 + OQ6 + OQ7 closed)

**Question (OQ4):** When emitted_claims diverge from intended_claims, which is authoritative?

**Question (OQ6):** If audit attributes defect to `synthesis_overclaim` but upstream agent disputes, resolution protocol?

**Question (OQ7):** What counts as "substantive claim requiring citation" for `uncited_assertion`?

**Decision:** Three sub-decisions, bundled because they share the same load-bearing principle: **v3.8 audit collects signal, does not adjudicate disputes or expand gate-refuse surface.**

**(a) OQ4 — Manifest authority: advisory, non-blocking.** When `emitted_claims` ∩ `intended_claims` = ∅ for some emitted claim → emit `CLAIM-DRIFT` advisory annotation, NOT a HIGH-WARN gate refuse. Negative-constraint violations remain HIGH-WARN per issue body (because those are explicit author-declared "MUST NOT" rules, qualitatively stronger than drift).

**(b) OQ6 — Stage-attribution disagreement: record, do not arbitrate.** Audit emits `defect_stage` from its own classification. If upstream agent (e.g., `synthesis_agent` review-loop) disputes, the dispute is logged in `claim_audit_result.upstream_dispute` (optional field, free-form rationale) but the original `defect_stage` is not overwritten. No voting, no v3.6.6 disagreement-handling reuse. Disagreement-rate analysis lives in #89 calibration scope.

**(c) OQ7 — `uncited_assertion` operational rule (3 conditions, AND):**
  1. Sentence contains at least one **quantifier or empirical claim** — quantifier tokens: numbers/percentages/{several, most, majority, significant, substantial, all, none}; empirical claim tokens: {found, showed, demonstrated, observed, measured, reported}.
  2. Sentence is NOT a **definition** (definition marker tokens: {refers to, is defined as, denotes, means}) AND NOT in a **methods boilerplate** section (section heading matches `/methods?/i` AND sentence is in a list/enumeration of standard procedures).
  3. Sentence has NO `<!--ref:slug-->` marker within its span.

Sentences satisfying all three are `uncited_assertion` candidates. **A claim that is in `claim_intent_manifest` but has no ref marker is still `uncited_assertion`** — manifest membership is independent of citation presence. This is a token-level rule, fast to implement, deliberately undertuned to favor false positives over false negatives (advisory tier, not gate-refusing).

**Rejected paths:**
- (a) Manifest as blocking → would gate-refuse on any paraphrase / claim-refinement during drafting, which is normal practice. v3.8 is detection layer, not contract layer.
- (b) Reuse v3.6.6 `disagreement_handling` → that pattern is writer↔evaluator pairwise dispute resolution with a tiebreaker (third reviewer). Stage attribution is measurement not adversarial; the pattern doesn't fit.
- (c) LLM-as-judge for "is this substantive?" → adds calibration surface (now THREE judgment types to calibrate: alignment, negative-constraint, substantive-ness) and high false-positive rate at small N. Token-based rule is deterministic, debuggable, and acceptable for an advisory annotation.

**Why:** v3.8's role is to surface signal that humans use to decide. Every additional gate-refuse expands the "things that block output" surface; v3.6.8/v3.7.x already established that gate-refuse should be reserved for **structural** contract violations (missing locator, fabricated reference, missing AI disclosure), not for **content judgment** ("this claim drifted from your manifest"). Recording disputes without arbitration mirrors the reviewer-calibration discipline: measure first, threshold later (in #89 calibration extension).

**Consequence:**
- `claim_audit_result.upstream_dispute` optional field added.
- Finalizer 6-cell matrix gains advisory cells (CLAIM-DRIFT, CLAIM-AUDIT-AMBIGUOUS, CLAIM-AUDIT-UNVERIFIED, UNCITED-ASSERTION) at LOW-WARN tier; HIGH-WARN reserved for UNSUPPORTED + NEGATIVE-CONSTRAINT-VIOLATION.
- `uncited_assertion` detector is a deterministic token-rule module, NOT an LLM-as-judge call.
- Manifest absence falls back to claim-extraction-from-draft with `MANIFEST-MISSING` advisory — all defect_stages still emit (per issue body acceptance criterion).

### D5 — `claim_audit_results[]` is a parallel lifecycle, not piggybacked on `audit_artifact[]` (OQ8 closed)

**Question:** v3.6.7 already has `audit_artifact[]` with `run_codex_audit.sh` wrapper and sidecar/jsonl/verdict.yaml triple. Should `claim_audit_results[]` reuse the lifecycle?

**Decision:** **Parallel new lifecycle. `claim_audit_results[]` is a new aggregate array in the orchestrator's passport-tracking, backed by a new per-entry schema `claim_audit_result.schema.json`. No change to `audit_artifact_entry.schema.json` or its agent enum.**

**Rejected:** Extend `audit_artifact_entry.schema.json`'s `agent` enum to include `claim_ref_alignment_audit_agent`, reuse the wrapper, write sidecar/jsonl/verdict.yaml triples per claim.

**Why:** Semantic mismatch.
- `audit_artifact[]` records "did this stage-completion deliverable pass independent codex review" — granularity is **per-stage-deliverable**, output is verdict (PASS/MINOR/MATERIAL/AUDIT_FAILED), invariants are enforced by `check_audit_artifact_consistency.py`.
- `claim_audit_results[]` records "did each individual claim's citation hold up under judge inspection" — granularity is **per-citation**, output is judgment (SUPPORTED/UNSUPPORTED/AMBIGUOUS/RETRIEVAL_FAILED), invariants are per-claim semantics (anchor required, defect_stage required when not SUPPORTED, etc.).

Bolting per-claim audit onto the per-deliverable schema would either (a) blow up the audit_artifact_entry size 50-200× per deliverable (one entry per claim) or (b) force claim-level results into nested arrays inside per-deliverable entries, fighting the schema's grain.

Independence is also valuable for migrations: #103 schema can evolve without coupling to v3.6.7 audit-artifact lint constraints, and #89 calibration can scope `claim_audit_results[]` analysis without touching `audit_artifact[]` semantics.

**Consequence:**
- New schema file: `shared/contracts/passport/claim_audit_result.schema.json`.
- New trigger boundary: claim_ref_alignment_audit_agent dispatches AFTER the v3.7.1 Cite-Time Provenance Finalizer pass and BEFORE `formatter_agent`'s hard gate, in the Stage 4 → Stage 5 transition slot. The formatter terminal hard gate runs DURING Stage 5, so any Stage 5→6 dispatch would produce results too late to block output. The Stage 4→5 slot is the only point where (a) draft prose with v3.7.3 anchors exists, (b) anchor presence is settled, and (c) the formatter hard gate has not yet run. Mirrors v3.6.7 Step 6 (audit between deliverable completion and downstream consumption) without sharing infrastructure.
- New orchestrator section in `pipeline_orchestrator_agent.md`: §3.6 "Claim-Faithfulness Audit Gate (v3.8)". Separate from §3.5.
- New lint: `scripts/check_claim_audit_consistency.py` covering per-claim invariants. Separate from `check_audit_artifact_consistency.py`.

### D6 — `claim_intent_manifest` is paper-visible runtime artifact, NOT part of `pre_commitment_artifacts`

This is restating the issue body's "critical scope boundary" for clarity in this decision doc, because it has downstream effects on schema 13.1 zero-touch verification.

**Decision:** `claim_intent_manifest` is emitted by `synthesis_agent` (deep-research) / `draft_writer_agent` (academic-paper) **after** paper-visible context loads, **before** prose generation. It is a separate downstream artifact persisted alongside the draft, NOT a field on the v3.6.6 `pre_commitment_artifacts` contract.

Schema 13.1 `pre_commitment_artifacts` field (on `sprint_contract` baseline) is **untouched**. `claim_intent_manifest` is a separate runtime artifact persisted as `claim_intent_manifests[]` in the orchestrator passport-tracking, backed by new per-entry schema `shared/contracts/passport/claim_intent_manifest.schema.json`.

**Consequence:**
- v3.6.6 zero-touch promise verifiable via lint: `pre_commitment_artifacts` schema diff vs. v3.7.3 baseline = empty.
- Manifest emission integrates into `synthesis_agent.md` / `draft_writer_agent.md` Three-Layer Citation Emission heading (added in v3.7.3) — new sibling heading "Claim Intent Manifest Emission (v3.8)".

## 4. Out-of-scope reminders (consolidated)

Issue body already lists these; restated here so the spec doesn't drift:

1. **Reflection meta-policy** — RubricEM per-run reflection buffer. Candidate for academic-pipeline revision-loop / systematic-review; deferred.
2. **Evolving rubric buffer** — RubricEM dynamic rubric pruning. Requires accumulated judged trajectories ARS lacks. Post-v3.8.
3. **Rubric discrimination-power audit** — Borrow 2 (analysis layer). Belongs to #89 calibration extension. #103 owns data emission only.
4. **`defect_stage` accuracy measurement** — Belongs to #89 / gold fixtures.
5. **L3-2 contamination_signals** — handled by #105 (closed) and v3.7.4 #102. Distinct from L3-1 claim alignment.

## 5. Acceptance criteria (decision-layer only)

Implementation-layer acceptance lives in the spec. The decision doc passes when:

- [ ] All 8 OQs have a written decision + rejected alternative + load-bearing reason
- [ ] All 6 invariants from §2 (v3.7.3 R-L3-1-A; v3.6.6 zero-touch; v3.6.7 audit_artifact semantic; passport 13.1 backward-compat; reviewer calibration; #103 out-of-scope list) traced to the relevant decision(s)
- [ ] Boundary between #103 and adjacent issues (#102 v3.7.4 triangulation; #89 calibration extension) named
- [ ] Codex review on this doc returns 0 P1/P2 boundary-leak findings

## 6. Companion documents

- **Spec:** `docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md` (implementation surface, schema, lint, TDD test cases — to be written after this doc passes codex round-1).
- **Calibration protocol:** `academic-pipeline/references/claim_audit_calibration_protocol.md` (post-spec implementation).
- **Memory anchor:** private maintainer memory (`project_ars_106_ai_disclosure_discovery`) — lesson #22 to be added recording 8-OQ resolution pattern (compresses #106's three-stage to two-stage when issue body already contains frozen design).
