# #216 — Surface-Form Parity (reviewer-type asymmetry, §F.3.6)

**Status:** implemented
**Date:** 2026-06-09
**Paper:** Kim et al. 2026, *On the limits and opportunities of AI reviewers*, arXiv:2605.20668v1, §F.3.6 ("Reviewer-type asymmetry")
**Split from:** #215 (field-norm severity). A cross-model review confirmed the two need different gold sets; combining them would serve neither measurement cleanly.

## What the paper found

The AI meta-reviewer applies **two different standards** depending on the **prose style** of a review item (§F.3.6, "Asymmetry mechanism"):

- **Human-written** items (informal, vague, loosely scoped): it demands literal precision and penalises informal language, over-rejecting correct concerns. Of 41 correctness false negatives, 29 involved human reviewers.
- **AI-written** items (naming specific technical concepts, code elements, math frameworks): it credits technical specificity and accepts claims without checking them, over-accepting incorrect concerns. Of 13 false positives, 10 involved AI reviewers.

Root cause the paper names: a learned prior that **specificity correlates with correctness**, misfiring in both directions.

## The two design tensions (and how they were resolved)

A codex consult (xhigh) stress-tested the design before implementation. Both recommendations were accepted by the maintainer.

### Tension 1 — the visibility paradox → **Surface-Form Parity, not authorship parity**

The bias appears to require the judge to know "human vs AI", so the obvious mitigation is to blind authorship at judgment time. But the prior actually keys off **prose style** (vague vs precise), not the author label — so a blinded judge still over-penalises vague prose. Blinding authorship is **necessary but not sufficient**.

**Resolution:** the mitigation is a **Surface-Form Parity self-check** at verdict-assignment time (extract the checkable claim → judge it against the paper, not the polish → do not down-rate informal wording unless ambiguity changes truth conditions → do not credit technical specificity without checking → run the opposite-style counterfactual). Authorship is **not** a judgment input.

### Tension 1b — schema decision → **authorship stays OUT of the runtime schema**

The issue originally allowed authorship metadata if kept audit-only. The codex consult and maintainer went further: authorship does **not** enter the runtime reviewer-item schema at all. `source_type` / author label belongs only in gold-set metadata, hidden from the judge. The enforcement point is `render_judge_view()` in `scripts/check_surface_form_parity.py` — a **whitelist** projection (the judge sees only an opaque `handle` (derived internally from a position index) + `review_item_text`), so no field added later can leak. This includes the nested `provenance.reviewer_source` author label AND the fixture `id` itself: the IDs encode the answer (`-cf` = counterfactual, `-ambiguous` = expected boundary verdict, flagged by codex review P2), so the real id is kept internal and the judge gets an opaque handle instead. `scripts/test_check_surface_form_parity.py::TestSerializerStrip` proves it (no blind field, no nested author label, no semantic id, no answer-encoding suffix).

### Tension 2 — measure the real asymmetry, not a proxy → **mixed-provenance regression fixture**

There is no deterministic predictor for this bias, and the 29-FN-human / 10-FP-AI numbers are **directional** (§H), not a calibration target. A parity-check that measured a proxy ("which challenge dimension activated on human vs AI items") could pass green while the real asymmetry persists.

**Resolution:** `evals/gold/surface_form_parity/` is a **regression fixture**, validated for data integrity + provenance honesty + pair invariants — NOT FNR/FPR. Provenance is honestly mixed:

- `paper_verbatim` (4) — real §F.3.6 examples with quote anchors that appear in the paper.
- `counterfactual_rewrite` (2) — maintainer-authored minimal-difference variants (same claim, same verdict, opposite framing). NOT first-party; carry `derived_from` + `semantic_equivalence_rationale`.
- `maintainer_boundary` (1) — `sfp-005-ambiguous`, a maintainer-authored boundary case documenting the UNLESS clause (vagueness that genuinely makes a claim unevaluable).

The smallest honest claim: *we preserve provenance-pinned examples of the documented failure shape and enforce a verdict-time prompt instruction not to let framing style flip a correctness verdict.* No asymmetry-rate claim.

## Verdict surface scope — TWO surfaces

The §F.3.6 failure is a property of any surface that adjudicates the correctness or weight of a reviewer concern keyed off its prose style. A codex review (round 6) flagged that the Devil's Advocate is **not** the only such surface: the **editorial synthesizer** arbitrates reviewer sub-claims in Phase 2 and explicitly down-ranks a criticism that is "too vague or unspecific" — exactly where §F.3.6 fires. So the parity self-check lands on **both** verdict-time surfaces:

1. **`devils_advocate_reviewer_agent.md`** — a verdict-time self-check when the DA decides whether a concern or counter-argument holds.
2. **`editorial_synthesizer_agent.md`** — a Step 1c arbitration-time check (before sub-claim weighting) + the "reduce weight if too vague" rule (Special Situation 4) is reworded to fire *only* when vagueness makes the sub-claim unevaluable, never on a substantively correct but informally phrased concern.

The other reviewer surfaces (domain, methodology, perspective) score paper dimensions; they do not adjudicate the correctness of a reviewer concern keyed off its prose style, so they are out of scope. The lint (`check_216_surface_form.py`) enforces both surfaces; if a future change makes another agent adjudicate concern correctness, the #215 precedent ("harden every verdict-assignment surface") applies and the parity check should extend there too.

## Relationship to #273 — cross-reference only (NOT folded)

#273 (same-family / rubric-aware calibration note, `docs/design/2026-06-08-273-rubric-aware-calibration-note-design.md`) is a **different mechanism**: it is an interpretive caveat about a judge shading a verdict toward what the rubric seems to want, with **no detection or prevention claim**. #216 is surface-form verdict parity. Folding them would dilute both into generic "don't game the rubric" prompt noise and blur #273's deliberate no-mitigation-claim boundary.

**Scope guard:** #273 may be mentioned only in this design note and the PR body. There is **no** shared prompt block, gold set, lint, or runtime wiring between #216 and #273. The `manifest.yaml` `related_issues` entry records this relationship as `cross-reference-only`.

## Files

- `evals/gold/surface_form_parity/{gold_set.json, manifest.yaml, README.md}`
- `academic-paper-reviewer/agents/devils_advocate_reviewer_agent.md` (Surface-Form Parity Self-Check section + marker block)
- `academic-paper-reviewer/agents/editorial_synthesizer_agent.md` (Step 1c arbitration-time parity check + reworded Special Situation 4)
- `scripts/check_surface_form_parity.py` (gold integrity + `render_judge_view`) + `scripts/test_check_surface_form_parity.py`
- `scripts/check_216_surface_form.py` (prompt-marker coverage) + `scripts/test_check_216_surface_form.py`
- `scripts/test_run_evals.py::test_surface_form_parity_is_pending_not_silently_passing`
- CI: `scripts/_ci_pytest_manifest.toml` + `.github/workflows/spec-consistency.yml`

## Epistemic status

The DA self-check is a prompt-surface instruction. It makes the parity standard explicit at verdict time; it does not, and cannot, prove the model is free of the surface-form prior at runtime — that needs a separate non-deterministic behavioral eval. The lints check data integrity, provenance honesty, pair invariants, and prompt-marker presence — not detection accuracy. The §F.3.6 directional counts motivate the gate; they are not a target it claims to hit.
