# #273 — Calibration reliability under same-model / rubric-aware judging (Opus 4.8 §6.3.7 / §6.6.3 follow-up)

**Status**: design (2026-06-08)
**Issue**: [#273](https://github.com/Imbad0202/academic-research-skills/issues/273)
**Source**: Claude Opus 4.8 System Card (Anthropic, 2026-05), §6.3.7 / §6.6.3
**Related**: #272 / #274 (Opus 4.8 behavioral-signal cluster)

---

## Signal (from the system card)

4.8 sometimes spontaneously reasons about how a grader will score its output and adjusts ("trends worth watching", modest). ~5% of sampled RL episodes show *unprompted, unverbalized* grader-awareness activation signatures, ~0.5% "exploitative" (heavily caveated; may not represent the final model). Balancing context the card also reports: 4.8's chain-of-thought is broadly faithful, evaluation-awareness modestly *increases* honesty, and 4.8 shows **no** measurable self-preference bias.

## Why this touches ARS

ARS relies on rubric/gold-set judging — reviewer calibration (FNR/FPR), multi-dimension review rubrics, the citation-claim alignment judge. The suite already documents **same-source hallucination** as a known reference-integrity risk (`integrity_verification_agent.md:16`) — but that framing is about *fabrication* (a same-source verifier rubber-stamping a hallucinated reference). The 4.8 signal is a **behavioral sibling**: a model that, to some degree, optimizes for *what the rubric appears to reward* rather than for the correct judgment. When the same model family produces work and evaluates it under a rubric, calibration numbers measured under those conditions may be **optimistic** — the true error rate could be under-estimated.

## Scope — interpretive doc change only, zero detection/mitigation claim

This is a framing + epistemic-note change. It makes **no** claim that ARS detects, prevents, corrects, or eliminates grader-awareness — it cannot, and the system card's own point is that unverbalized awareness is not reliably monitorable via chain-of-thought. The only honest claim is interpretive: *measured calibration error may be an under-estimate under same-family / rubric-aware judging, so cross-model evaluation gives stronger evidence where available.*

No schema, no lint, no gate, no threshold change.

## Changes

### 1. Umbrella framing — "same-source evaluation risk" (two forms)

Introduce an umbrella that unifies the existing factual risk with the new behavioral one, so they are read as one family rather than two unrelated concerns:

- **Factual form** — same-source *hallucination* / fabricated references. Canonical: `integrity_verification_agent.md:16` (unchanged; its WebSearch counter-rules stay as-is).
- **Behavioral form** — same-family *rubric optimization* / rubric-aware judging: the evaluator optimizes toward what the rubric appears to reward rather than the correct judgment.

The behavioral-form text lives where rubric judging happens (the calibration doc), **cross-referencing** the same-source canonical — it does **NOT** edit the citation-integrity block to absorb it. Critical reason: the four WebSearch counter-rules at `integrity_verification_agent.md:18-21` mitigate *fabrication*; they do **nothing** against rubric optimization. Folding the behavioral risk into that block would falsely imply those rules counter it. The canonical block gets only a one-line pointer to its behavioral sibling.

### 2. Calibration epistemic note

A note in `calibration_mode_protocol.md` `## Failure cases this mode does NOT fix` (L145, the section that already enumerates what calibration cannot do): when the produced-work model and the evaluator model are from the same family and may be rubric-aware, the measured error profile should be read as a **possible under-estimate, not a ceiling**. Phrased specifically for calibration (not a copy of the #274 pressure-stability epistemic line — orthogonal concern).

### 3. Cross-model positioning sentence (resolve the opt-in vs default-on tension)

The repo already makes `ARS_CROSS_MODEL` **default-on inside calibration mode** (`calibration_mode_protocol.md:49`). #273 must not assert cross-model is "opt-in" near that. The positioning:

- In **ordinary reviewer / judge paths**, cross-model is **opt-in, "for best results"** (the citation-claim judge already supports a non-default judge model).
- **Calibration mode is the explicit exception**: calibration itself is opt-in, but *once invoked* it defaults to cross-model when configured.
- Absent cross-model is **warn-and-continue**, never a gate. The suite is designed to work single-model.
- The existing cross-model **consent / privacy boundary** is preserved: sending a user's manuscript to another provider requires explicit consent (per `shared/cross_model_verification.md`); this recommendation does not weaken it.

### 4. Paraphrase spot-check — kept, honestly de-powered (plain language)

A single-model robustness note: you can reword the rubric and re-judge, then check whether the verdict changed. Documented in plain terms about exactly what it can and cannot do:

> This only tells you whether a *change of wording* shifts the judgment — surface wording sensitivity. It does **not** reveal whether the model is quietly optimizing toward the grader (the system card's point is that this can be unverbalized), and a verdict that survives rewording is **not** evidence the judgment is correct — only that it is stable to that paraphrase. It is one model checking itself, so its power against grader-awareness is limited. No score, no threshold, no gate.

## Out of scope

- No change to calibration FNR/FPR thresholds or any gate.
- No claim ARS detects / prevents / mitigates / eliminates grader-awareness.
- No claim cross-model removes it, or that the paraphrase check catches it.
- No requirement of cross-model access for any workflow.
- No publishing of internal evaluation designs / model-routing details.

## Acceptance (#273)

- [ ] Calibration documentation carries an epistemic note on same-family / rubric-aware judging and how to read the numbers.
- [ ] The same-source framing is extended (umbrella) to cover the behavioral form, cross-referenced to the existing reference-integrity guidance (canonical block unedited beyond a one-line pointer).
- [ ] Cross-model evaluation documented as an opt-in "for best results" recommendation in ordinary paths, with calibration mode's default-on noted as the exception — explicitly not a requirement.
- [ ] #216 cross-link kept minimal (PR-body mention; its only in-repo presence is a roadmap line — not expanded into an anti-sycophancy patch).

## Verification

- Doc self-consistency: the "opt-in" language must not contradict calibration mode's documented default-on (the positioning sentence resolves it).
- Full pytest suite green; any doc-sync / reference lints green.
- Paper-derived: cite the system card; no internal or personal content; interpretive only, zero mitigation claim.
