# Calibration Mode Protocol

**Status**: v3.2
**Parent skill**: `academic-paper-reviewer`
**Mode name**: `calibration`
**Purpose**: Measure this reviewer's own false-negative rate (FNR), false-positive rate (FPR), balanced accuracy, and **severity-miscalibration rate** (#215) against a user-supplied gold-standard set, then attach the resulting error profile as a confidence disclosure to subsequent reviews in the same session.

---

## Why this mode exists

A single LLM reviewer produces an absolute 0-100 rubric score, but that score is weakly interpretable without knowing the reviewer's error profile. Two reviewers could give the same paper a 65, yet one might systematically over-score weak methodology papers and the other might systematically under-score cross-disciplinary work. Absolute scores don't reveal this.

Lu et al. (2026, Nature 651:914-919) demonstrated in Table 1 that an LLM-based Automated Reviewer can approach human balanced accuracy (0.65 vs human 0.67-0.73 on 500 ICLR 2022 papers) while having a dramatically different error profile: FNR 0.17 vs human 0.52, at the cost of FPR 0.50 vs human 0.17-0.34. Human reviewers miss half of the papers that should be rejected; the Automated Reviewer misses very few but over-rejects more.

Translation for ARS: **our reviewer has an error profile too, and we do not currently measure it.** Calibration mode closes that gap. It does not try to make the reviewer perfect; it makes the reviewer's imperfections legible.

---

## Inputs

1. **Gold-standard set**: 5-20 papers the user has labelled with known outcomes. Minimum 5; recommended 10-15. Each entry:
   - Paper file path or text
   - Ground-truth label: `accept`, `reject`, or `borderline`
   - Venue context (journal/conference, tier)
   - Optional: human reviewer scores for comparison

2. **Domain specification**: the user's target field, used to seed `field_analyst_agent`. Calibration for "machine learning venues" is not valid for "qualitative education research" — error profiles are domain-specific.

3. **Session persistence**: the error profile is cached for the **current session only**. No cross-session caching, no `~/.ars_calibration_cache/` directory. Calibration is explicitly opt-in per the v3.2 design decision: the user decides when to spend tokens on calibration, and a new session starts fresh. If the user wants to reuse a profile across sessions, they re-run calibration or paste a prior Calibration Report as a session prompt.

---

## Process

### Phase 0: Intake

- Verify the set has at least one `accept` and one `reject` (otherwise FNR or FPR is undefined).
- If all labels are on one side, refuse to proceed and ask the user for at least one counter-example.
- Warn if n < 10: "Calibration with fewer than 10 papers produces wide confidence intervals. Results should be treated as directional, not conclusive."

### Phase 1: Run `full` mode on each gold paper, with ensembling

For each paper, run the standard `full` review pipeline **5 times** (ensembling, per Lu 2026 Methods A.1.1). Each run uses a fresh context window to avoid within-session bias. Aggregate:
- Median rubric score per dimension
- Variance across the 5 runs (reported as a stability indicator)
- Editorial decision (majority vote across 5)

**Cross-model verification**: In calibration mode, `ARS_CROSS_MODEL` is **default-on** rather than opt-in. At least one of the 5 runs should use a different model family if available, to avoid single-model blind spots. If no cross-model is configured, emit a warning and run all 5 on the primary model.

### Phase 2: Build the confusion matrix

Compare reviewer's majority-vote decision against the user's ground-truth label.

- `borderline` ground truth papers are excluded from the binary confusion matrix but reported separately (see Phase 3).
- Map `Accept` and `Minor Revision` reviewer decisions → positive. Map `Major Revision` and `Reject` → negative. This follows Lu 2026 Table 1's binarization.

Compute:

| Metric | Formula | Report with |
|---|---|---|
| Balanced accuracy | (TPR + TNR) / 2 | 95% CI via bootstrap (1000 resamples) |
| FNR (miss rate) | FN / (FN + TP) | Same |
| FPR (false alarm) | FP / (FP + TN) | Same |
| AUC | ROC over rubric-score threshold | Same |
| Calibration error | Mean &#124;rubric_score - ground_truth_severity&#124; | Per-dimension |

### Phase 3: Borderline handling

Borderline papers don't enter the binary matrix but are useful for rubric-score calibration. For each borderline paper, report:
- The reviewer's rubric score
- The reviewer's decision
- Whether the reviewer's decision respects the user's "this is borderline" signal (i.e., did it correctly land in Major Revision rather than confidently Accept or Reject?)

A reviewer that confidently Accepts or Rejects borderline papers has a "confidence miscalibration" problem even if its binary accuracy looks fine.

### Phase 3.5: Severity-miscalibration measurement (#215)

The binary confusion matrix (Phase 2) measures decision-level error (FNR/FPR). It does **not** capture the paper's largest documented AI-reviewer failure: a finding that is content-correct but **severity-miscalibrated** — either a field-norm boundary error (Kim et al. 2026, W1, n=54) or the "would addressing this change the core result?" significance-boundary error (Kim §F.3.4, 56 errors). A reviewer can have a clean FNR/FPR and still systematically over- or under-rate the severity of individual findings.

For each weakness the reviewer emitted across the gold runs, classify its **severity-miscalibration risk** as `low` / `med` / `high`:

- **`high`** — the finding's severity rests on a field norm or the "core result" formula, AND the reviewer asserted the severity **without** grounding the norm in an external checkable source (the W1 / §F.3.4 failure shape).
- **`med`** — severity depends on a field norm but the reviewer gave partial or weak grounding (named a standard but did not establish it applies to this subfield).
- **`low`** — severity does not depend on a field norm, OR the norm is grounded in an external checkable source per the domain-reviewer Field-Norm Severity Discipline (Step 5).

**Grounding discipline (do not repeat the failure you are measuring).** The classifier persona **MUST NOT** guess whether a norm is right from its own model knowledge — that is exactly the W1 behaviour under audit. It rates *whether the reviewer supplied external grounding*, not *whether the reviewer's norm is factually correct*. The reference shapes are anchored to the first-party regression fixture at `evals/gold/field_norm_severity/` (W1 + §F.3.4 cases extracted verbatim from Kim et al. 2026); a finding that matches a fixture shape but lacks grounding is `high`.

This produces a histogram of low/med/high counts reported alongside FNR/FPR in Phase 4 — a severity-calibration signal the binary matrix cannot show.

### Phase 4: Produce the Calibration Report

Output document structured as:

```
# Calibration Report for <Reviewer Instance>
Domain: <domain>
Gold set: n=<N> (accept=<a>, reject=<r>, borderline=<b>)
Runs per paper: 5 (ensembled)
Cross-model: <yes/no, model families used>

## Summary metrics
- Balanced accuracy: 0.XX [95% CI: 0.XX - 0.XX]
- FNR: 0.XX [95% CI ...]
- FPR: 0.XX [95% CI ...]
- AUC: 0.XX
- Ensemble stability: <mean std of rubric scores across runs>

## Comparison to Lu 2026 Table 1 baselines
| Metric | This reviewer | Lu 2026 Automated Reviewer | Lu 2026 Human |
|---|---|---|---|
| Balanced accuracy | X | 0.65 | 0.67-0.73 |
| FNR | X | 0.17 | 0.52 |
| FPR | X | 0.50 | 0.17-0.34 |

(Note: Lu 2026 numbers are for ML venues specifically. Compare with caution outside ML.)

## Per-dimension calibration error
<table of 7 review dimensions with mean absolute calibration error>

## Severity-miscalibration histogram (#215)
<low/med/high counts over all emitted weaknesses, e.g.>
| Risk | Count | Share |
|---|---|---|
| low | XX | XX% |
| med | XX | XX% |
| high | XX | XX% |
<A high `high`-share means the reviewer frequently asserts field-norm / "core result" severities without external grounding — the W1 / §F.3.4 failure shape. This is a SEPARATE signal from FNR/FPR: a reviewer can pass the binary gate and still carry a high severity-miscalibration rate. Grounded per Phase 3.5; classifies grounding, not norm-correctness.>

## Systematic biases detected
<natural-language narrative identifying patterns, e.g.
 "Reviewer tends to over-score originality on cross-disciplinary papers"
 "Reviewer under-scores qualitative methodology by ~8 points vs ground truth"
>

## Recommendations for session use
- Treat this reviewer's rubric scores as having calibration error ±X points
- For accept/reject decisions, the reviewer misses X% of reject cases (FNR)
- For decisions near the accept/reject boundary, escalate to human judgement
```

### Phase 5: Session attachment

If session persistence is enabled, the Calibration Report is attached to every subsequent review in the same session as a **confidence disclosure header**. The disclosure appears in the editorial letter before the verdict:

```
> **Reviewer Confidence Disclosure (from calibration session <id>):**
> This reviewer has measured balanced accuracy 0.XX, FNR 0.XX, FPR 0.XX on a
> gold set of <N> papers in <domain>. Rubric scores below have calibration
> error ±X points. Treat borderline decisions with human judgement.
```

This is non-negotiable in calibration-enabled sessions: the user cannot hide the disclosure. The point of calibration is to make error profiles legible; suppressing the disclosure defeats the mode.

---

## Ensembling methodology notes

Lu 2026 Methods A.1.1 describes reviewer ensembling across 5 independent runs with majority voting. This mode follows that spec with two changes:

1. **Median instead of mean for rubric scores**: mean is vulnerable to single-run outliers (e.g., a run that hallucinates a methodological flaw); median is robust.
2. **Fresh context per run**: Lu 2026 allowed within-session memory across runs. ARS uses fresh context to prevent cascading errors from a single run's misreading.

Users with token budget concerns can reduce `runs_per_paper` to 3. Below 3, ensembling is meaningless — do not allow 1 or 2.

---

## Failure cases this mode does NOT fix

Calibration reports this reviewer's error profile on a **specific** gold set in a **specific** domain. It does not:

- Predict performance on papers outside that domain
- Detect frame-lock within a single paper review (that's `devils_advocate_reviewer` territory)
- Catch implementation-bug-as-finding cases (that's the AI Research Failure Mode Checklist, ROADMAP_v3.2.md item 2)
- Replace the `re-review` mode for revision verification

If the user's gold set is itself biased (e.g., all papers from one lab, all from one year), calibration reports a biased profile. Emit a warning during intake if papers share obvious metadata clusters.

### Same-family / rubric-aware judging — read the numbers as a possible under-estimate

There is a second reason a measured profile can be optimistic, independent of the gold set. It belongs to the broader **same-source evaluation risk**, which has two forms:

- **Factual form** — *same-source hallucination*: when the model that wrote the work and the model verifying it share training data, a fabricated reference that "feels right" passes undetected. This is the citation-integrity risk documented in the Anti-Hallucination Mandate (`academic-pipeline/agents/integrity_verification_agent.md`), countered there by independent reference lookup.
- **Behavioral form** — *same-family rubric optimization* (rubric-aware judging): an evaluator may, to some degree, optimize toward *what the rubric appears to reward* rather than toward the correct judgment. When the produced-work model and the evaluator model are from the same family and may be rubric-aware, the calibration error you measure can be **optimistic — read it as a possible under-estimate of the true error, not a ceiling.**

This is an interpretive caveat only. ARS does **not** detect, prevent, or correct rubric-aware judging — the behavior can be unverbalized and is not reliably visible in chain-of-thought. The note changes how you *read* the numbers; it does not change any threshold or gate.

**Cross-model evaluation — stronger evidence where available.** Running the evaluation across model families provides **stronger evidence** than a same-family-only run; it still does **not** detect or rule out rubric-aware judging. Positioning:

- In ordinary reviewer / judge paths, cross-model is **opt-in, "for best results"** — the citation-claim alignment judge already supports a non-default judge model, and the suite is designed to work single-model.
- **Calibration mode is the exception**: calibration itself is opt-in, but once invoked `ARS_CROSS_MODEL` is **default-on** (see "Cross-model verification" under Phase 1) — at least one of the runs should use a different family when configured.
- Absent cross-model is **warn-and-continue**, never a gate.
- Sending a user's manuscript to another provider still requires the explicit consent / privacy step in `shared/cross_model_verification.md` — this recommendation does not weaken that boundary.

**A single-model spot-check (weak, optional).** With no second model, you can reword the rubric and re-judge, then check whether the verdict changed. Be clear about what this does: it only tells you whether a *change of wording* shifts the judgment — surface wording sensitivity. It does **not** reveal whether the model is quietly optimizing toward the grader (that can be unverbalized), and a verdict that survives rewording is **not** evidence the judgment is correct — only that it is stable to that paraphrase. It is one model checking itself, so its power against grader-awareness is limited. No score, no threshold, no gate.

### Directional prior: assume leniency relative to human expert review (FARS external anchor)

Beyond the same-family optimism above, there is a citable **directional** prior on the sign of the error: when the simulated 5-reviewer panel's output is read as a pass/fail signal, assume it runs **lenient relative to human expert review** until your own calibration measurement shows otherwise. FARS (Tang et al. 2026, arXiv:2606.31651) provides a deployment-scale external anchor: on the FARS deployment corpus, an ICLR-style automated reviewer (Stanford Agentic Reviewer) averaged 5.00 over the 165 papers it reviewed, while the paper-level mean from 282 human expert reviews covering 140 of those papers was 3.23 on the same 0-10 scale — a ~1.8-point gap (a descriptive difference between overlapping-but-unequal paper sets, not a paired estimate), and the automated score never functioned as an acceptance probability, only as a relative ranking.

How to use this prior:

- The **direction** is a working prior, not a law: FARS measured one setup (ICLR-style ML reviewing, one reviewer system), so carrying its sign to other domains, rubrics, or this panel is a heuristic extrapolation — which is exactly why it lands as a default-until-measured assumption rather than a fact. Under this prior, a panel "accept" is weaker evidence than a panel "reject", and a panel score is better read as a relative ranking within a batch than as an acceptance probability.
- The **magnitude** (~1.8 points) is **NOT portable** across domains, rubrics, or model setups. Never apply it as a correction factor, threshold shift, or score adjustment — if you need a number for your setup, measure it with this mode (Phases 2/4, using the optional human reviewer scores in the gold set).
- This is an interpretive caveat only: no behavior, schema, gate, or threshold changes. The simulated panel remains advisory infrastructure behind human checkpoints — the caveat is about how to read its output, not about its authority.

---

## Integration with existing modes

| Existing mode | Interaction with calibration |
|---|---|
| `full` | Calibration runs `full` 5x per gold paper. No change to `full` itself. |
| `re-review` | Calibration profile attaches to re-review decisions. |
| `quick` | Calibration profile attaches. Confidence disclosure notes that `quick` has additional uncalibrated error on top of the measured profile. |
| `methodology-focus` | Calibration should ideally be run with methodology-heavy gold papers if this mode is the user's target. |
| `guided` | Not applicable — guided mode is Socratic dialogue, rubric scores are not the primary output. |

---

## Resolved design decisions (2026-04-09)

- **Activation**: opt-in only. User invokes `calibration` mode explicitly. ARS does not auto-calibrate on first use in a new domain.
- **Persistence**: session-scoped only. No cross-session caching of profiles, no `~/.ars_calibration_cache/`, no privacy questions about storing paper content on disk.
- **Shipped gold sets**: not planned for v3.2. Users bring their own gold set. Shipping a built-in ML gold set was considered and rejected to avoid domain-coverage bias and staleness.
- **Continuous/self-calibration**: rejected. Using the reviewer's own historical decisions as pseudo-ground-truth is circular and would make the error profile look better over time without actually improving accuracy.

---

## References

- Lu, C. et al. (2026). Towards end-to-end automation of AI research. *Nature* 651, 914-919. doi:10.1038/s41586-026-10265-5 — Table 1 (reviewer validation), Methods A.1.1 (ensembling).
- Tang, Q., Hu, X., Liu, X., Chen, Y. & Shao, Y. (2026). FARS: A fully automated research system deployed at scale. arXiv:2606.31651 — deployment-scale automated-vs-human reviewer comparison (automated mean over 165 papers; 282 human expert reviews over 140 papers); source of the leniency-direction anchor above.
- Efron, B. & Tibshirani, R. J. (1993). *An Introduction to the Bootstrap*. Chapman & Hall/CRC — bootstrap CI methodology.
- ARS `shared/cross_model_verification.md` — cross-model reviewer integration.
- ARS `academic-paper-reviewer/references/quality_rubrics.md` — scoring rubric definitions.

## v3.6.2 sprint contract status

v3.6.2 introduces sprint contracts for `reviewer_full` and `reviewer_methodology_focus` only. A template for this mode will follow in a subsequent patch release. Until then, this mode runs without contract enforcement and retains its pre-v3.6.2 behaviour.
