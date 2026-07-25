# Content-First QA Pipeline

Use this reference when auditing, revising, or polishing a materials manuscript,
proposal, review, or section draft after initial drafting. The core rule is
**content before language**: scientific logic is checked before style polishing.

For state-machine runs, use this file together with:

- [state-machine/evaluation-rubric.md](state-machine/evaluation-rubric.md)
- [state-machine/stopping-rules.md](state-machine/stopping-rules.md)
- [state-machine/validation-checklist.md](state-machine/validation-checklist.md)

## Gate Order

### Gate 2: Content Expert Review

Check the scientific layer first:

- Does the argument match the evidence?
- Are methods, DOE choices, material systems, and test conditions sufficient?
- Are alternative explanations acknowledged?
- Does a review cover the necessary subfields and controversies?
- Are novelty and gap claims bounded?

For review papers, use coverage and critical-depth checks. For experimental
papers, use methods and mechanism checks. For proposals, use feasibility and
innovation checks.

### Gate 1: Language And AI-Style Detection

Run language cleanup only after Gate 2. In English, look for vague AI phrasing,
over-smoothed logic, inflated verbs, and unsupported certainty. In Chinese,
degrade this gate to a manual readability scan if automated style signals are
not reliable.

### Gate 3: Auto-Validation

Check format, completeness, and traceability:

- Every factual claim has citation, dataset, DOE rationale, or figure support.
- Methods are reproducible enough for the target journal.
- Abbreviations, variables, units, and figure/table numbering are consistent.
- Conclusions do not exceed the data boundary.
- References cited in text exist in the reference list.

### Gate 4: Score Threshold

Score the draft by dimension and route revisions by the lowest-scoring
dimension. Use the eight anchored dimensions in
[state-machine/evaluation-rubric.md](state-machine/evaluation-rubric.md):
task_scope_clarity, scientific_tension, evidence_match,
materials_method_reproducibility, argument_chain, innovation_specificity,
risk_boundary, and language_quality.

Before recommending another full revision loop, apply
[state-machine/stopping-rules.md](state-machine/stopping-rules.md). Stop when
there have been maximum three full revision rounds, two consecutive score
improvements below 0.5, missing key evidence, unresolved specialist conflict,
or the target threshold has been reached.

Recommended thresholds:

| Mode | Threshold | Notes |
|---|---:|---|
| paper | 7.0 | Full manuscript or submission section |
| proposal | 7.0 | Feasibility and innovation both matter |
| review | 7.0 | Coverage and synthesis depth both matter |
| internal | 5.0 | Lab note, meeting memo, or internal draft |
| quick | none | Mark only blocking issues |

## Why Gate 2 Comes First

If style polishing happens before expert review, polished paragraphs may still
be scientifically wrong. Materials-writing should therefore revise content,
evidence boundaries, and logic before improving wording.

## Output Format

Return a QA report with:

1. Gate summary: pass / revise / stop.
2. Highest-risk content issue.
3. Language issues only after content issues.
4. Auto-validation gaps.
5. Dimension scores and the targeted next revision.
6. Current artifact, score/status, remaining risks, stop-or-continue reason,
   and one next action.
