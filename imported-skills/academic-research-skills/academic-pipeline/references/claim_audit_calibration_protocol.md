# Claim-Faithfulness Audit Calibration Protocol

**Status**: v3.8
**Parent agent**: `claim_ref_alignment_audit_agent`
**Mode name**: `calibration`
**Purpose**: Measure the audit agent's own false-negative rate (FNR) and false-positive rate (FPR) on alignment judgments (SUPPORTED / UNSUPPORTED / AMBIGUOUS / RETRIEVAL_FAILED) AND negative-constraint judgments (VIOLATED / NOT_VIOLATED) against a synthetic gold set, then gate CI on FNR < 0.15 AND FPR < 0.10.

This protocol is modeled on `academic-paper-reviewer/references/calibration_mode_protocol.md`. The reviewer mode measures editorial decision accuracy on whole papers; this mode measures claim-to-source alignment accuracy on per-citation tuples. Both share the same FNR / FPR / threshold-gate vocabulary; the difference is unit of analysis.

---

## Why this mode exists

The audit agent emits HIGH-WARN gate-refuse annotations on UNSUPPORTED rows and VIOLATED constraint matches. Those signals are only useful if the underlying judge is reliably distinguishing supported from unsupported claims. Without measurement, a judge that systematically over-flags AMBIGUOUS cases as UNSUPPORTED looks identical at the row level to a judge that nails the discrimination — but the former produces a flood of false HIGH-WARN refusals that erodes operator trust and eventually gets the agent ignored.

Calibration mode closes the measurability gap. It does NOT try to make the judge perfect; it makes the judge's error profile legible BEFORE the agent ships to a new operator's pipeline.

---

## Inputs

1. **Gold set**: 25 tuples (17 alignment incl. 5 #213 partial-support fixtures + 8 constraint per the canonical shipped fixture at `scripts/fixtures/claim_audit_calibration/gold_set.json`). Per-tuple shape and the four ingestion-gate rules (alignment-judgment coverage, ≥3 NOT_VIOLATED floor, required constraint fields, tuple_kind validity) are spelled out in **Gold tuple schema** below + spec §7.7 rules (a)-(d). The shipped fixture is the canonical example.

2. **Judge function**: a callable matching the v3.8 judge interface (`claim_text`, `retrieved_excerpt`, `anchor_kind`, `anchor_value`, `active_constraints`, `judge_model` kwargs). The shipped test fixture pairs the gold set with a perfect-judge stub so T-C1 / T-C2 / T-C3 exercise the calibration tooling end-to-end without requiring a live LLM call. Production deployment plugs a real judge_fn in place of the stub.

3. **Thresholds** (optional): `{"FNR": 0.15, "FPR": 0.10}` per spec §7.7 + §9 acceptance. Tightening these is a spec bump; loosening them is not permitted without a corresponding judge-quality-improvement justification recorded in the calibration report's `thresholds` block.

---

## Gold tuple schema

Two discriminated `tuple_kind` shapes, validated at ingestion by `validate_gold_set` (raises `GoldSetValidationError` on the first rule violation).

### Alignment tuple

```jsonc
{
  "tuple_kind": "alignment",
  "claim_text": "<the prose claim under test>",
  "ref_text_excerpt": "<source-passage excerpt the judge will evaluate against; null for RETRIEVAL_FAILED tuples>",
  "anchor": {"kind": "page" | "section" | "quote" | "paragraph" | "none", "value": "<...>"},
  "expected_judgment": "SUPPORTED" | "UNSUPPORTED" | "AMBIGUOUS" | "RETRIEVAL_FAILED"
}
```

Alignment tuples MUST NOT carry any of: `constraint_under_test_id`, `constraint_under_test_rule_text`, `manifest_fixture_path` (rule (b)). Mixing constraint fields onto an alignment tuple corrupts the per-class confusion matrix because the judge call shape differs between the two kinds.

### Constraint tuple

```jsonc
{
  "tuple_kind": "constraint",
  "claim_text": "<the prose claim under test>",
  "ref_text_excerpt": null,
  "anchor": {"kind": "page" | "section" | ..., "value": "<...>"},
  "expected_judgment": "VIOLATED" | "NOT_VIOLATED",
  "constraint_under_test_id": "MNC-N" | "NC-CN-M",
  "constraint_under_test_rule_text": "<inline rule text>",     // EITHER this
  "manifest_fixture_path": "scripts/fixtures/.../mnc.json"     // OR this
}
```

Both rule sources are accepted by `validate_gold_set` because manifest-bound constraints sometimes carry domain-specific rule text that authors want versioned alongside the manifest. **The v3.8.0 calibration runner supports only the inline `constraint_under_test_rule_text` form.** A manifest-only tuple validates clean per rule (c) but `run_calibration` raises `NotImplementedError` at run time rather than reach the judge with an empty rule (R2 codex P1 closure on the silent-skip risk that T-C3 is meant to prevent). The manifest-fixture resolver is a post-v3.8 deliverable; until it ships, author calibration fixtures with inline rule text.

---

## Process

### Phase 0: Intake

1. Call `validate_gold_set(tuples)`. Any of the four spec §7.7 rules (a)/(b)/(c)/(d) failing raises `GoldSetValidationError` with the offending tuple index and the rule name. Do NOT catch the exception — fix the gold set.

### Phase 1: Per-tuple judge invocation

For each tuple, the calibration runner calls `judge_fn(...)` with kwargs matching the v3.8 judge interface:
- Alignment tuples (all four `expected_judgment` values including `RETRIEVAL_FAILED`) → `retrieved_excerpt = tuple.ref_text_excerpt` (may be `null` for `RETRIEVAL_FAILED` tuples), `active_constraints=[]`. The runner does NOT pre-filter `RETRIEVAL_FAILED` tuples — the judge stub is responsible for returning the matching label.
- Constraint tuples → `retrieved_excerpt = tuple.ref_text_excerpt` (typically `null`), `active_constraints=[{"constraint_id": ..., "rule": ..., "scope": "MNC" | "NC"}]`. Scope is derived from `constraint_under_test_id`: `MNC-N` → `"MNC"`, `NC-CN-M` → `"NC"`. Malformed ids are rejected by `_derive_constraint_scope` with a diagnostic naming the expected shape.

No ensembling at this layer. Spec §7.7 does not require N-run majority voting (reviewer mode does, but reviewer-paper unit-of-analysis is heavier and benefits more from variance reduction; per-tuple alignment is a simpler call). Re-running the same tuple is the operator's responsibility if a high-variance judge_model warrants it.

### Phase 2: Confusion-matrix accumulation

The runner accumulates two confusion matrices:

- **Aggregate** (the rates that T-C1 gates against): a tuple contributes a FN when `expected_judgment ≠ actual judgment`. For alignment, every mismatched tuple counts as both FN (for the expected class) and FP (for the wrongly-picked class), so aggregate FNR and FPR are symmetric. For constraint tuples, VIOLATED is the positive class (gate-refuse signal); the matrix is the standard binary form.
- **Per-class one-vs-rest** (the report block that T-C2 checks): for each of `SUPPORTED`, `UNSUPPORTED`, `AMBIGUOUS`, `violated_constraint`, the runner computes FNR / FPR with that class as the positive label. `n_positive` / `n_negative` denominators are surfaced so a "0.0 FNR on n_positive=0" entry is distinguishable from "0.0 FNR on n_positive=8".

The fourth alignment class `RETRIEVAL_FAILED` is intentionally NOT surfaced in `per_class`: the pipeline sets it pre-judge at operational deployment, so judge-quality FNR/FPR against this label is uninformative for tooling validation. To keep the per-tuple call shape uniform, the runner still passes `RETRIEVAL_FAILED` tuples to `judge_fn` (no pre-filter) — the stub or real judge echoes the expected label, and the tuple contributes to aggregate FNR/FPR via the non-`per_class` aggregate path.

### Phase 3: Threshold check

If `report["FNR"] >= thresholds["FNR"]` OR `report["FPR"] >= thresholds["FPR"]`, the test (T-C1) fails. The report's `thresholds` block echoes the active gate values so CI failure messages can distinguish:

- A regression (judge quality degraded — same gold set, higher FNR/FPR than the previous run).
- A spec bump (tighter thresholds — same judge, but T-C1 now demands more).

Both surface as the same CI failure; the report block makes the diagnosis explicit.

### Phase 4: Report shape

```jsonc
{
  "FNR": 0.0,
  "FPR": 0.0,
  "per_class": {
    "SUPPORTED":           {"FNR": 0.0, "FPR": 0.0, "n_positive": 5, "n_negative": 12},
    "UNSUPPORTED":         {"FNR": 0.0, "FPR": 0.0, "n_positive": 8, "n_negative": 9},
    "AMBIGUOUS":           {"FNR": 0.0, "FPR": 0.0, "n_positive": 3, "n_negative": 14},
    "violated_constraint": {"FNR": 0.0, "FPR": 0.0, "n_positive": 5, "n_negative": 3}
  },
  "partial_support": {"miss_rate": 0.0, "n_partial": 5},
  "thresholds": {"FNR": 0.15, "FPR": 0.10},
  "n_total": 25,
  "n_alignment": 17,
  "n_constraint": 8
}
```

The shape is the canonical contract `scripts/test_claim_audit_calibration.py` (T-C1 / T-C2) pins against. Adding fields is non-breaking; removing or renaming is a spec bump.

**Partial-support subset (`partial_support`, #213).** Gold tuples tagged `expected_prompt_verdict=PARTIAL` carry `expected_judgment=UNSUPPORTED` (the B1 normalization), so a judge that **stops decomposing and emits a bare `UNSUPPORTED`** matches the aggregate gate and hides the exact regression #213 closes. The subset metric counts a partial fixture as passed ONLY when the judge emits `UNSUPPORTED` AND a well-formed true-partial `sub_claim_breakdown` (≥2 items, ≥1 SUPPORTED AND ≥1 non-SUPPORTED — the INV-19 definition). `miss_rate = misses / n_partial`; a bare-`UNSUPPORTED` judge registers `miss_rate=1.0` here while the aggregate FNR stays green. The block is additive — a gold set with no partial fixtures yields `{"miss_rate": 0.0, "n_partial": 0}`.

---

## Failure cases this mode does NOT fix

Calibration reports the judge's error profile on a **specific** gold set in a **specific** domain. It does not:

- Predict performance on tuples outside the gold-set distribution (the canonical fixture is mid-domain synthetic; ML / clinical / qualitative judges should run domain-specific gold sets).
- Detect rubric-discrimination-power problems on the LLM-as-judge side — that's the `#89 / gold fixtures` work tracked separately (per spec §2 out-of-scope).
- Replace the post-calibration ramp-on plan recorded in `academic-pipeline/SKILL.md` mode flags. v3.8.0 ships the audit agent dispatch as opt-in default-OFF; T-C1 passing on the canonical gold set is necessary but not sufficient evidence for default-ON.

If a deploying operator brings a gold set that is itself biased (all tuples from one venue, all post-2024, all heavily-redacted), calibration reports a biased profile. Emit a warning during intake if the gold set looks clustered — this protocol does not currently auto-detect clustering, but the operator's pre-deployment review should.

**Partial-evidence regression IS caught (#213).** One failure the aggregate gate alone would NOT catch: a judge that regresses to emitting bare `UNSUPPORTED` on compound claims instead of decomposing them. Because partial fixtures carry `expected_judgment=UNSUPPORTED`, the aggregate FNR stays green on that regression. The `partial_support` subset metric exists precisely to surface it — `miss_rate > 0` means the judge stopped producing inspectable `sub_claim_breakdown` decompositions even though it got the headline label right. Treat a non-zero `partial_support.miss_rate` as a judge-quality regression on the §F.3.2 partial-evidence trap, distinct from an aggregate FNR/FPR threshold breach.

---

## Integration with existing modes

| Mode | Interaction with calibration |
|---|---|
| Stage 4 → 5 audit dispatch | Calibration runs offline; results inform the `ARS_CLAIM_AUDIT` ramp-on decision. |
| Cite-Time Provenance Finalizer | No direct coupling — calibration evaluates the judge in isolation; the finalizer's matrix is downstream. |
| `/ars-mark-read` clearance | Calibration does not interact with mark-read state; HIGH-WARN-CLAIM-NOT-SUPPORTED stays non-clearable regardless of calibration outcome. |
| Reviewer `calibration` mode | Sibling, not coupled. Both compute FNR/FPR but on different units (papers vs claim-tuples); both can run in the same session. |

---

## Resolved design decisions (2026-05-15, per spec §10 OQs)

- **Activation**: opt-in. The audit agent ships with default thresholds and the canonical fixture; operators run `scripts/test_claim_audit_calibration` as a CI gate. Re-calibration with a domain-specific gold set is the operator's call, not auto-triggered.
- **Threshold values**: FNR < 0.15 + FPR < 0.10. Tightened from the reviewer-mode 0.17 / 0.50 Lu 2026 reference points because the audit unit (per-claim) is simpler than the reviewer unit (whole paper) — the gate should track the stricter end of plausible LLM-as-judge accuracy.
- **Ensembling**: not in v3.8.0. Per-tuple alignment calls are short and the judge's response shape is constrained; majority-vote ensembling adds cost without obvious accuracy gain for this unit of analysis. Re-evaluate if calibration evidence in v3.8.x shows high variance.
- **Cross-model verification**: out of scope for the calibration runner — `ARS_CROSS_MODEL` interacts with the audit agent dispatch path, not the calibration script. An operator wanting cross-model calibration runs the runner twice with different `judge_model` settings.

---

## Running locally

```bash
PYTHONPATH=. python3 -m unittest scripts.test_claim_audit_calibration -v
```

The CI-equivalent invocation lives in `.github/workflows/spec-consistency.yml` (the v3.8 `#103` unittest step). Both paths exercise T-C1 (threshold gates), T-C2 (per-class FNR/FPR reporting), and T-C3 (gold-set shape integrity).

---

## References

- Spec: `docs/design/2026-05-15-issue-103-claim-alignment-audit-spec.md` §7.7 (test contract) + §1 deliverable 7 (this doc) + §9 (acceptance criteria) + §13 step 10 (implementation order).
- Issue: [academic-research-skills #103](https://github.com/Imbad0202/academic-research-skills/issues/103) acceptance criterion (FNR < 0.15 + FPR < 0.10 gates).
- Parent agent: `academic-pipeline/agents/claim_ref_alignment_audit_agent.md` — dispatches calibration mode and consumes the report's thresholds block. The agent prompt and this doc form a two-way pair following the v3.6.5 protocol-doc convention (`literature_corpus_consumers.md` ↔ `bibliography_agent.md`).
- Reviewer calibration baseline: `academic-paper-reviewer/references/calibration_mode_protocol.md` (same vocabulary, different unit of analysis).
- Lu, C. et al. (2026). *Nature* 651, 914-919 — Table 1 reference rates for LLM-vs-human agreement on whole-paper decisions; this protocol uses tighter thresholds for the simpler per-claim unit.
