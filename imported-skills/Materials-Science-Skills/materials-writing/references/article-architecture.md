# Article Architecture

Use this reference when writing or rebuilding manuscript sections. It describes how the one-sentence argument expands into each section's moves. These are structural patterns, not wording templates.

## Full-paper argument chain

A strong materials paper can usually be reduced to:

`field-scale need -> unresolved bottleneck -> proposed move -> decisive evidence -> broader implication -> boundary`

Each section carries one link of this chain, and each link must be visible to the reader:

| Section | Link | What it must earn |
|---|---|---|
| Abstract | compresses the full chain | the reader sees the problem, contribution, result, and boundary in one paragraph |
| Introduction | earns the gap | field progress leads to a specific missing evidence, not just a missing topic |
| Methods | justifies the evidence | the measurements are reproducible and the conditions are controlled |
| Results | shows the data | observations are quantified and compared against baselines |
| Discussion | interprets and limits | mechanism evidence is cross-validated, alternatives are addressed, boundaries are stated |
| Conclusion | restates the contribution without inflating it | contribution, limitation, next step, and overclaim boundary are all present |

If one link is missing, mark it as missing rather than writing around it.

## Section move lists

### Abstract

1. Background pain or field stake.
2. Contribution of this paper.
3. Key result, preferably quantitative.
4. Mechanism or workflow evidence.
5. Bounded implication.

### Introduction

1. Field progress and why the topic matters.
2. Current performance boundary or contradiction.
3. Strategy evolution in prior work.
4. The remaining evidence gap.
5. This paper's design and how it is validated.

### Methods

1. Synthesis or preparation route.
2. Characterization techniques and their purpose.
3. Performance test setup and conditions.
4. Statistical treatment and replicate count.

### Results

1. Observation of the phenomenon.
2. Quantitative measurement.
3. Comparison against baseline or prior work.
4. Statistical significance or trend.

### Discussion

1. Meaning of the findings.
2. Comparison with prior literature.
3. Mechanism evidence (cross-validated).
4. Alternative explanations and why they are excluded.
5. Boundary conditions.

### Conclusion

1. Contribution restated.
2. Decisive evidence named.
3. Broader implication.
4. Boundary condition.
5. Future work.

## Diagnostics

After a full read, check:

- Can you state the contribution in one sentence?
- Does every claim have explicit evidence?
- Is the gap stated explicitly, not implied?
- Is the boundary condition declared, not hidden?
- Does each section open with its move, not with throat-clearing?
- Does the conclusion restate rather than inflate the contribution?

## Relationship to argument-chain.md

`argument-chain.md` is the fast one-sentence argument template (Problem -> Gap -> Hypothesis -> Evidence -> Boundary). This reference is the deeper full-paper architecture: how that one sentence expands into section-level moves.

## Materials-specific structures

Experimental paper, dual-line: a `performance line` (what the material does) and a `mechanism line` (why it does it). The two lines should converge in the discussion so that performance is explained by mechanism, not merely correlated with it.

Trade-off paper: `contradiction -> resolution -> dual-indicator verification`. State the competing demands, show how the design breaks the trade-off, then verify both indicators (the gained one and the preserved one) so the trade-off is actually broken rather than relocated.
