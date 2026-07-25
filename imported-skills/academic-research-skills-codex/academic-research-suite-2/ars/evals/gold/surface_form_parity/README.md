# Surface-Form Parity Gold Set

Issue: #216

A **mixed-provenance regression fixture** for the §F.3.6 reviewer-type asymmetry documented in Kim et al. 2026 (arXiv:2605.20668v1, "On the limits and opportunities of AI reviewers"). It is anchored to first-party verbatim examples from the paper, with a small number of maintainer-authored variants that are labelled honestly as such.

## What the paper found

The AI meta-reviewer applies **two different standards** depending on the **prose style** of the review item (§F.3.6, "Asymmetry mechanism"):

- For **human-written** items (typically informal, vague, loosely scoped) it demands literal precision and penalises informal language — so it over-rejects correct human concerns. Of 41 correctness false negatives, 29 involved human reviewers.
- For **AI-written** items (typically naming specific technical concepts, code elements, math frameworks) it credits technical specificity and accepts claims without checking them against the paper — so it over-accepts incorrect AI concerns. Of 13 false positives, 10 involved AI reviewers.

The root cause the paper names is a learned prior that **specificity correlates with correctness**, which misfires in both directions.

## Why "surface-form", not "authorship"

The hook is the **prose style** (`framing_style`: `informal_vague` vs `technical_precise`), **not** the author label. Blinding the author does not remove the bias, because the prior keys off how the item is written, not a literal "human"/"AI" tag. So the mitigation (#216) is a **Surface-Form Parity** self-check at verdict time — judge the checkable claim against the paper, not against polish — and authorship is deliberately kept **out** of the runtime reviewer-item schema (see the design note).

## What this is (and is not)

This is a **regression fixture**, not a detector calibration set. There is no deterministic predictor for this bias, n is tiny, and the paper's 29-FN-human / 10-FP-AI numbers are **directional** (§H), not thresholds. The validator (`scripts/check_surface_form_parity.py`) checks **data integrity + provenance honesty + pair invariants** — it does **not** compute FNR/FPR or assert distributional asymmetry. A lint that claimed to measure detection accuracy on a prompt-based judge would be fluent wrongness: green while the real bias persists.

## Provenance honesty (mixed-provenance)

Because the set mixes real and maintainer-authored material, every item carries an explicit `provenance_type`:

- `paper_verbatim` (n=4) — a real §F.3.6 example with a `verbatim_anchor` quote that appears in the paper. Items: `sfp-001`, `sfp-002`, `sfp-003`, `sfp-004`.
- `counterfactual_rewrite` (n=2) — a **maintainer-authored** minimal-difference variant of a `paper_verbatim` case: same `canonical_claim`, same `expected_correctness`, rewritten in the **opposite** `framing_style`, truth conditions preserved. Carries `derived_from` + `semantic_equivalence_rationale`. **NOT first-party** — never cite it as paper-verbatim. Items: `sfp-001-cf`, `sfp-003-cf`.
- `maintainer_boundary` (n=1) — a **maintainer-authored** boundary case whose `review_item_text` is synthetic (the paper states the mechanism but gives no verbatim item for this boundary). Anchored to the paper's mechanism sentence via `mechanism_anchor`, not a verbatim review quote. Item: `sfp-005-ambiguous`.

Anchors are paper section/example IDs + verbatim quote snippets, **not** session-scoped pdftotext line numbers (those rot).

## Pairs

Two `pair_id` groups (`pair-01`, `pair-03`) hold a `paper_verbatim` + its `counterfactual_rewrite`. Pair invariant: members share `canonical_claim` and `expected_correctness` and differ only in `framing_style`. The discipline being fixtured: a correctness verdict that **flips** between paired members is keying off style, not substance — the §F.3.6 failure. `pair_id` is internal; it is in `judge_blind_fields` and must never reach the judge.

## Judge-blind fields

`metadata.judge_blind_fields` lists everything that must be stripped before an item is shown to a reviewing judge: `pair_id`, `framing_style`, `provenance_type`, `expected_correctness`, `expert_verdict`, `meta_reviewer_verdict`, `asymmetry_direction`. The judge sees only an opaque `handle` (derived internally from a position index) + `review_item_text` — **not** the fixture `id`, because the IDs encode the answer (`-cf` = counterfactual, `-ambiguous` = expected boundary verdict). A serializer-strip test enforces this (the #216 enforcement point for the "authorship/style invisible at judgment time" decision).

## Exception / boundary fixture

`sfp-005-ambiguous` (`exception: true`) documents the **UNLESS** clause of the parity rule: "do not down-rate informal/vague wording *unless* ambiguity changes truth conditions or makes the item unevaluable." It is a genuinely unevaluable vague item where a Not-Correct / ambiguous outcome is **correct**. Retained so the parity rule cannot be misread as "never penalise vagueness" — without it, a judge could over-correct into accepting empty concerns.

## Relationship to #273

#273 (same-family / rubric-aware calibration) is a **different mechanism** and is **not** folded in here. Cross-reference only — no shared prompt, gold, or runtime wiring. See the design note.

## Run

```bash
python -m scripts.check_surface_form_parity
```
