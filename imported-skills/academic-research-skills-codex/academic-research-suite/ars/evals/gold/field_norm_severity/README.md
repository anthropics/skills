# Field-Norm Severity Gold Set

Issue: #215

A first-party regression fixture of severity-miscalibration cases drawn verbatim from Kim et al. 2026 (arXiv:2605.20668v1, "On the limits and opportunities of AI reviewers"). It pins the two documented failure shapes the #215 changes target, so prompt/protocol edits can be checked against real, traceable cases.

## What this is (and is not)

This is a **regression fixture**, not a detector calibration set. There is no deterministic predictor for "field-norm severity miscalibration" — judging it requires the field prior the paper shows AI reviewers lack. So the validator (`scripts/check_field_norm_severity.py`) checks **data integrity + first-party provenance**, not FNR/FPR. With n=10 it makes no distributional-calibration claim.

## Subtypes

- `field_norm_boundary` — paper W1 (n=54, the largest weakness class): the AI critique is content-correct against a discipline-neutral standard but mis-rated because it lacks the subfield's accepted-practice prior. Example: a CERN/LHCb reproducibility request that ignores the collaboration's internal-artifact norm.
- `significance_boundary` — paper §F.3.4 (56 errors): the AI meta-reviewer's habitual "would addressing this change the core result?" formula under-weights methodological rigour / scope / translational relevance and over-weights presentation issues with technical terminology.

Both are `severity_miscalibration: true`; the subtype distinguishes the driver. They are not mutually exclusive in nature (a case can be both field-norm-like and significance-like, e.g. the Coulombic-efficiency case), so the subtype records the dominant driver rather than partitioning the space.

## Provenance

Every case carries `provenance` with a stable, extraction-independent anchor: the paper section/example ID (e.g. `§F.3.4 Pattern A Example 1`), the paper's own citation token (e.g. `P9 · GPT-5.2 · item 5 · primary`), the reviewer model, and a verbatim quote snippet. Anchors are section/example IDs, **not** session-scoped line numbers (those came from a transient pdftotext extract and would rot).

## Exception fixtures

`sgb-005-exception` (SAR safety at 11.7T MRI) carries `exception: true` + `exception_reason`. The paper notes experts agreed with the AI's direction in **that specific case** while still citing it under the broader under-rating pattern. It is retained — not as a clean positive case — to document that the "does not change the core result" formula is not always wrong, so a severity check must not blanket-flag it.

## Run

```bash
python -m scripts.check_field_norm_severity
```
