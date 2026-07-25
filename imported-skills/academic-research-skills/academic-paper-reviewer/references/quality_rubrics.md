# Quality Rubrics for Academic Paper Review

## Purpose

Provides calibrated scoring rubrics for the 7 review dimensions used by all reviewers (R1, R2, R3, DA). Ensures consistent, reproducible scoring across different papers and review sessions.

## Known error profile (v3.2)

These rubrics define *what* to measure, not *how accurate* the measurement is. A single LLM reviewer's absolute rubric score has calibration error that depends on domain, paper type, and model version.

For users who want to know this reviewer's empirical FNR / FPR / balanced accuracy before relying on these rubric scores, run the opt-in **calibration mode** (see `calibration_mode_protocol.md`). Calibration mode compares this reviewer's decisions against a user-supplied gold set and produces a Calibration Report that attaches as a confidence disclosure to subsequent reviews in the same session.

Without calibration, treat rubric scores as *ordinally* meaningful (papers scored 85 are better than papers scored 65) but *not cardinally* interpretable (a 85 does not guarantee venue acceptance).

## Scoring Scale

All dimensions scored 0-100. Final weighted score determines editorial decision.

## Decision Mapping

| Weighted Average | Decision |
|-----------------|----------|
| >= 80 | Accept |
| 65-79 | Minor Revision |
| 50-64 | Major Revision |
| < 50 | Reject |

---

## Dimension 1: Originality (Weight: 20%)

| Score Range | Descriptor | Behavioral Indicators |
|------------|------------|----------------------|
| 90-100 | Exceptional | Novel theoretical framework supported by empirical evidence; opens entirely new research direction; implications span 3+ fields; no prior work addresses this exact question |
| 75-89 | Strong | Novel methodology OR novel application of existing theory to new context; clear contribution beyond incremental extension; implications for 2+ fields |
| 60-74 | Adequate | Extends existing framework with new data, population, or context; contribution is clear but incremental; single-field implications |
| 45-59 | Weak | Replicates existing study with minor variations; contribution is marginal; "so what?" question not convincingly answered |
| < 45 | Insufficient | No discernible original contribution; duplicates existing work without justification; purely descriptive without analytical insight |

## Dimension 2: Methodological Rigor (Weight: 25%)

| Score Range | Descriptor | Behavioral Indicators |
|------------|------------|----------------------|
| 90-100 | Exceptional | Research design perfectly aligned with RQ; all validity threats addressed; appropriate statistical methods with power analysis; transparent reporting (all EQUATOR items); reproducible |
| 75-89 | Strong | Sound design with minor gaps; most validity threats addressed; appropriate methods with minor reporting omissions; largely reproducible |
| 60-74 | Adequate | Acceptable design but some validity concerns; methods appropriate but justification lacking; some reporting gaps (missing effect sizes, CIs) |
| 45-59 | Weak | Design has significant flaws; method choice questionable; multiple reporting gaps; reproducibility doubtful |
| < 45 | Insufficient | Fundamental design flaws that invalidate findings; inappropriate methods; results cannot be trusted |

## Dimension 3: Evidence Sufficiency (Weight: 25%)

| Score Range | Descriptor | Behavioral Indicators |
|------------|------------|----------------------|
| 90-100 | Exceptional | >40 sources, 80%+ peer-reviewed, multi-method triangulation, primary + secondary data, all claims well-supported, counter-evidence acknowledged |
| 75-89 | Strong | 25-40 sources, 70%+ peer-reviewed, adequate evidence for main claims, some triangulation |
| 60-74 | Adequate | 15-25 sources, 60%+ peer-reviewed, key claims supported but some gaps, limited triangulation |
| 45-59 | Weak | <15 sources OR <50% peer-reviewed, several unsupported claims, no triangulation |
| < 45 | Insufficient | Severely under-sourced, major claims unsupported, relies heavily on grey literature or anecdotal evidence |

## Dimension 4: Argument Coherence (Weight: 15%)

| Score Range | Descriptor | Behavioral Indicators |
|------------|------------|----------------------|
| 90-100 | Exceptional | Crystal-clear logical flow from problem -> gap -> RQ -> method -> findings -> implications; every section builds on previous; no logical jumps; counterarguments pre-empted |
| 75-89 | Strong | Clear logical flow with minor gaps; most transitions well-handled; argument generally persuasive |
| 60-74 | Adequate | Main argument visible but some sections feel disconnected; occasional logical jumps; conclusions mostly follow from evidence |
| 45-59 | Weak | Argument structure unclear; significant logical gaps; conclusions overreach evidence; reader must infer connections |
| < 45 | Insufficient | No coherent argument; sections appear unrelated; conclusions do not follow from evidence; circular reasoning |

## Dimension 5: Writing Quality (Weight: 15%)

| Score Range | Descriptor | Behavioral Indicators |
|------------|------------|----------------------|
| 90-100 | Exceptional | Professional academic prose; precise terminology; excellent paragraph structure; zero grammatical errors; appropriate register throughout |
| 75-89 | Strong | Good academic writing; minor stylistic inconsistencies; few grammatical issues; terminology mostly precise |
| 60-74 | Adequate | Acceptable writing but room for improvement; some verbose passages; occasional imprecise terminology; some grammar issues |
| 45-59 | Weak | Below journal standards; frequent verbose/unclear passages; terminology inconsistent; multiple grammar issues |
| < 45 | Insufficient | Unacceptable writing quality; incomprehensible passages; severe grammar problems; not suitable for peer review |

## Optional Dimensions (reviewer-specific)

### Literature Integration (R2 Domain Expert focus)

| Score Range | Descriptor |
|------------|------------|
| 90-100 | Comprehensive coverage of seminal + recent works; identifies theoretical lineage; positions paper precisely in scholarly conversation |
| 75-89 | Good coverage; most key works cited; reasonable positioning in literature |
| 60-74 | Adequate but gaps in coverage; some important works missing; positioning somewhat vague |
| < 60 | Significant literature gaps; key works missing; poor positioning |

### Significance & Impact (R3 Perspective Reviewer focus)

| Score Range | Descriptor |
|------------|------------|
| 90-100 | Clear practical implications for policy/practice AND theory; addresses urgent real-world problem; likely to influence field direction |
| 75-89 | Good practical OR theoretical implications; addresses relevant problem; moderate influence potential |
| 60-74 | Some implications but narrowly scoped; relevance clear but impact limited |
| < 60 | Minimal practical or theoretical significance; unclear why this matters |

---

## Aggregation Formula

```
Final Score = (Originality x 0.20) + (Methodology x 0.25) + (Evidence x 0.25) + (Coherence x 0.15) + (Writing x 0.15)
```

Optional dimensions are reported separately and factored into the editorial synthesis narrative but do not change the numerical score.

---

## Calibration Notes

- Scores should reflect the paper's quality relative to the target journal's standards
- A "75" for Nature is not equivalent to "75" for a regional journal
- When in doubt, err toward the middle of a range
- Reviewers should explicitly state which range descriptor best matches, then fine-tune within that range
- If two dimensions are at odds (e.g., excellent methodology but weak writing), do NOT average down — report both scores honestly
