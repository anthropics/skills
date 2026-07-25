# Literature Pipeline Scoring

Score candidates on a 100-point scale. Recalculate totals from dimensions; never trust inherited or imported totals.

Use these scores for discovery triage only. A score can prioritize reading,
but it does not turn metadata or abstracts into manuscript evidence.

## Scoring Dimensions

| # | Dimension | Weight | Key question | Gate |
|---|---|---|---|---|
| 1 | Topic fit | 30 | Does this paper directly address the research question? | If below 10, candidate cannot rank top tier |
| 2 | Evidence layer | 20 | What level of evidence does it provide? | Full source/data evidence scores above metadata |
| 3 | Method relevance | 15 | Experimental method, characterization, or model fit? | Generic methods score lower than domain-specific |
| 4 | Material-system proximity | 15 | Same material family, binder/matrix, scale, environment? | Cross-family papers score lower |
| 5 | Source quality | 10 | Journal, peer review, DOI completeness, citation reliability? | Predatory or unverified sources score 0 |
| 6 | Actionability | 10 | Clear next use in DOE, data, figure, writing, or review? | Vague papers score lower than actionable |

## Dimension Scoring Guide

### Topic fit (0–30)

| Score | Description |
|---|---|
| 25–30 | Directly addresses the research question with the same material system and phenomenon |
| 18–24 | Addresses a closely related question or material system |
| 10–17 | Tangentially relevant; useful context but not directly applicable |
| 0–9 | Out of scope; cannot rank top tier regardless of other scores |

### Evidence layer (0–20)

| Score | Description |
|---|---|
| 16–20 | Original experimental data, mechanistic analysis, or validated model |
| 11–15 | Review with systematic analysis, meta-analysis, or comparative study |
| 6–10 | Descriptive review, case study, or limited data |
| 0–5 | Opinion, commentary, or purely theoretical without validation |

### Method relevance (0–15)

| Score | Description |
|---|---|
| 12–15 | Same or directly comparable experimental methods and characterization |
| 8–11 | Related methods that can be adapted or compared |
| 4–7 | Different methods but in the same domain |
| 0–3 | Incompatible methods or no experimental component |

### Material-system proximity (0–15)

| Score | Description |
|---|---|
| 12–15 | Same material family, same binder/matrix, same scale |
| 8–11 | Same material family, different binder/matrix or scale |
| 4–7 | Adjacent material family with transferable principles |
| 0–3 | Completely different material system |

### Source quality (0–10)

| Score | Description |
|---|---|
| 8–10 | Top-tier peer-reviewed journal, complete DOI, well-cited |
| 5–7 | Reputable journal, minor metadata gaps |
| 2–4 | Conference paper, preprint, or low-impact journal |
| 0–1 | Unverified source, predatory journal, or missing DOI |

### Actionability (0–10)

| Score | Description |
|---|---|
| 8–10 | Clear, specific next use: fills a citation gap, provides a method template, or supplies comparison data |
| 5–7 | Potentially useful but requires further reading to confirm |
| 2–4 | Interesting context but no clear immediate use |
| 0–1 | No actionable content for the current research |

## Required Labels

Every candidate must carry three labels:

1. **`source_depth`**: `metadata-only`, `abstract-screened`, `full-text-read`, or `data-extracted`.
2. **`next_action`**: `read`, `cite-gap-audit`, `monitor`, `exclude`, or `archive`.
3. **`evidence_boundary`**: One sentence explaining what the candidate can and cannot support.

## Score Breakdown Fields

The public candidate table stores the six dimensions as separate numeric
columns. Do not add a JSON `score_breakdown` column.

| Contract field | Score dimension |
|---|---|
| `topic_fit` | Topic fit |
| `evidence_layer_score` | Evidence layer |
| `method_relevance` | Method relevance |
| `material_system_proximity` | Material-system proximity |
| `source_quality` | Source quality |
| `actionability` | Actionability |

`score_total` must equal the sum of these six fields.

## Rules

- Do not allow journal prestige to override poor topic fit.
- Metadata-only candidates must not be treated as evidence for manuscript claims.
- A candidate flagged as `exclude` or `archive` must have a documented reason.
- Recalculate `score_total` from dimensions every time; do not cache or inherit.
- Do not raise scores to compensate for a failed source, missing full text, or
  weak metadata coverage. Record the degradation instead.
- If `topic_fit < 10`, the candidate cannot appear in the top tier even when
  source quality, journal prestige, or citation count is strong.
- If `source_depth` is `metadata-only` or `abstract-screened`, set
  `next_action` to `read`, `cite-gap-audit`, `monitor`, or `exclude`; do not
  set it to `archive` unless a reason is recorded.

## Calibration

After 2-3 pipeline runs, review the score distribution with the user or the
research-state owner:

- If top-tier papers routinely score 90+, the rubric is too loose; lower
  topic-fit or actionability scores unless the paper directly answers the
  active research question.
- If no candidate reaches 60, check whether the search terms are too narrow,
  the field is sparse, or the material-system proximity weights need adjustment.
- If prestigious but off-topic papers outrank domain-relevant papers, enforce
  the `topic_fit < 10` gate and reduce source-quality influence.
- If many metadata-only candidates rank highly, check whether evidence-layer
  scores are inflated; metadata-only records should normally stay in a
  discovery or monitor tier.
