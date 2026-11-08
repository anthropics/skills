# Failure modes this skill is built around

Each worker rule in `rules.md` (and the orchestrator's completion report in SKILL.md) exists because the failure it prevents was observed and measured in real chart-abstraction work at academic medical centers. This file is the evidence catalog — read it when deciding whether a rule can be relaxed for a use case (usually: no).

| # | Failure mode | What it looks like | Rule that prevents it |
|---|---|---|---|
| 1 | **Batched-document recall collapse** | When N notes are concatenated into one prompt, recall on later notes drops sharply relative to processing each note alone. The miss is silent — no error, just absent findings. | Rule 1 (one note per call) |
| 2 | **Required-field fabrication** | When the schema marks a field required and the note lacks it, the model completes it: "June 2020" → "2020-06-01"; redacted drug name → a plausible drug. | Rule 2 (null by default) |
| 3 | **Fabricated terminology codes** | Model emits SNOMED / CUI / MeSH / MedDRA / ICD identifiers that are syntactically well-formed but do not exist, or exist but map to the wrong concept. | Rule 4 (never emit a code) + orchestrator's validation pass |
| 4 | **Parametric-knowledge leakage** | Told "extract only what the note says," the model still applies its own clinical knowledge — corrects a wrong drug indication, fills a normal range, infers a diagnosis from findings. | Rule 3 (extract, don't know) |
| 5 | **Assertion flattening** | "Watch for nausea" extracted as nausea-present. "No chest pain" extracted as chest-pain-present. "Mother had breast cancer" extracted as patient-has-breast-cancer. "Started on lisinopril for hypertension" extracted as hypertension-caused-by-lisinopril. | Rule 6 (classify assertion) |
| 6 | **Silent output truncation** | Under "list all X," the model returns a subset and presents it as complete. On long inputs the dominant error is omission, not hallucination. | Orchestrator's completion report (SKILL.md step 4) |
| 7 | **Unit/value confusion on numerics** | Raw vs. percent-predicted swapped; pre- vs. post-bronchodilator swapped; implausible values (FEV1 = 470%) passed through. | Rule 7 (range-check numerics) |
| 8 | **Uncitable values** | A correct-looking value with no source span — the reviewer cannot verify it without re-reading the whole note, which defeats the purpose. | Rule 5 (cite every value) |

## Why these matter for the skill design

- Failures 1, 6, 7 are **silent** — there is no signal in the output that anything went wrong. The guard has to be structural (one note, explicit completeness count, range flag), not a post-hoc check.
- Failures 2, 3, 4 share a root cause: the model prefers a confident answer over an honest null. The guard is the same in each case — make `null` the default and make any positive value carry proof (span, validated code).
- Failure 5 is a labeling problem, not a detection problem — the model usually *finds* the negated/hypothetical mention, it just reports it under the wrong polarity. A fixed assertion taxonomy (see `assertion-classes.md`) forces the distinction.

## What the skill does NOT solve

- **Reasoning over the extracted values** (causality, temporality across notes, eligibility logic) — that is a downstream skill's job.
- **OCR / scanned-document quality** — if the input is a low-quality scan, extraction quality is bounded by OCR quality. Flag illegible spans as `null_reason: "mentioned_unclear"`.
- **Cross-note reconciliation** — two notes that disagree about a value are reconciled by the caller, not this skill.
