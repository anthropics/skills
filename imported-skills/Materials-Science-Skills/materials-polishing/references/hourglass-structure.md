# Hourglass Structure for Materials Manuscripts

Each major section of a materials paper has a characteristic information flow
shape. Polishing must preserve and strengthen this shape — never flatten it.

---

## Introduction — Narrowing Funnel

The introduction moves from **broad to specific**. Every paragraph narrows the
scope until the gap is clear.

```
Layer 1: Engineering problem / material family
   Layer 2: Specific material system / application
      Layer 3: What has been done (literature)
         Layer 4: What remains unresolved (the gap)
            Layer 5: Study objective + evidence plan
```

### Paragraph-level pattern

| Paragraph | Content | Direction |
|---|---|---|
| 1 | Engineering context: where this material is used, why it matters | Broad |
| 2 | Material system: what specific system this study addresses | Narrower |
| 3 | Literature: what others have found, what methods they used | Narrower |
| 4 | Gap: what remains unresolved, conflicting, or insufficiently tested | Narrowest |
| 5 | Objective: what this study does, what evidence it provides | Focused |

### Common violations

| Violuation | Example | Fix |
|---|---|---|
| Widening after the gap | After stating the gap, the author introduces new background | Move background before the gap |
| Missing gap | Literature review ends without identifying what is missing | Add explicit gap statement |
| Too broad opening | "Road construction is very important for national development" | Start with the specific material and function |
| Literature list without synthesis | "Many researchers studied A, B, C, D" | Group by theme, state what is known and what is not |
| Methods in Introduction | "In this study, we used SEM and FTIR..." | Move to Methods or final paragraph only |

### Good example

> Emulsified asphalt tack coats are widely used to improve interlayer bonding
> in asphalt pavements [1,2]. Waterborne epoxy modification has been shown to
> improve the cohesion and moisture resistance of emulsified asphalt systems
> [3–5]. However, the relationship between epoxy curing kinetics, emulsion
> stability, and interface bonding strength remains insufficiently resolved
> [6,7]. In particular, whether epoxy curing can develop without compromising
> demulsification and workability has not been systematically tested [8].
> This study investigates the bonding performance of waterborne epoxy modified
> emulsified asphalt across a dosage range, with FTIR and microscopy evidence
> to support mechanism interpretation.

---

## Discussion — Widening Funnel

The discussion moves from **specific to broad**. It starts with what happened
and widens to what it means.

```
Layer 1: Key result (what happened)
   Layer 2: Mechanism (why it happened)
      Layer 3: Literature comparison (how it fits)
         Layer 4: Engineering implication (what it means)
            Layer 5: Limitation + future work (what we don't know)
```

### Paragraph-level pattern

| Paragraph | Content | Direction |
|---|---|---|
| 1 | Restate key finding with quantitative detail | Specific |
| 2 | Explain mechanism: what evidence supports the interpretation | Specific |
| 3 | Compare with literature: how results relate to published work | Wider |
| 4 | Engineering implication: what this means for practice | Wider |
| 5 | Limitation and future work: what remains untested | Widest |

### Common violations

| Violuation | Example | Fix |
|---|---|---|
| New data in Discussion | Presenting new results not shown in Results section | Move to Results |
| Methods in Discussion | Describing how the test was done | Already in Methods; remove |
| Speculation without hedging | "This proves the mechanism" | "This is consistent with..." |
| Missing limitation | Discussion ends on a positive note without boundary | Add limitation paragraph |
| Literature list without comparison | "A found X. B found Y. C found Z." | Synthesize: "Our results are consistent with A but differ from B because..." |

### Good example

> The 15% WER group showed the highest mean bond strength (0.78 MPa) under
> the tested curing condition. FTIR analysis revealed the disappearance of
> the 915 cm⁻¹ epoxide peak, consistent with ring-opening crosslinking during
> curing. This observation is in agreement with Kong et al. (2024), who
> reported similar peak disappearance in waterborne epoxy–asphalt systems.
> However, unlike Li et al. (2023), who used a different curing agent, our
> system showed a broader curing window. The improved bonding strength may
> therefore be attributed to a combination of epoxy crosslinking and enhanced
> interfacial adhesion. From an engineering perspective, the 15% dosage
> represents a balance between bonding performance and sprayability, though
> field validation under traffic and moisture exposure remains necessary.

---

## Results — Evidence Ladder

Results paragraphs follow a **data-first** structure:

```
Observation → Quantification → Comparison → Mechanism support → Boundary
```

### Sentence-level pattern

1. **Lead sentence**: state the trend or observation.
2. **Quantify**: add value, condition, test standard, and replicate count.
3. **Compare**: compare with control or baseline.
4. **Mechanism** (if available): add characterization evidence.
5. **Boundary** (if needed): state limitation of the observation.

### Example

> The bond strength increased with WER content up to 15% (Fig. 2a). The 15%
> WER group reached a mean pull-off strength of 0.78 ± 0.06 MPa after 7 d
> curing (ASTM D7234), which was 73% higher than the control (0.45 ± 0.04
> MPa). FTIR showed a decrease in the 915 cm⁻¹ epoxide peak for this group
> (Fig. 3), suggesting partial curing. The improvement was not sustained at
> 20% WER, where viscosity may have limited emulsion stability.

---

## Conclusions — Closing Triangle

The conclusions move from **specific finding to general implication**:

```
Specific finding → General implication → Bounded recommendation
```

### Pattern

1. **Specific**: what this study found (1–2 sentences, past tense).
2. **General**: what it means for the field (1 sentence, present tense).
3. **Boundary**: what remains to be tested (1 sentence, future-oriented).

### Example

> Waterborne epoxy modification at 15% content increased the bond strength of
> emulsified asphalt by 73% under the tested curing condition. This
> improvement is consistent with epoxy crosslinking and enhanced interfacial
> adhesion. Field validation under traffic, moisture, and temperature cycling
> is recommended before engineering deployment.

---

## Abstract — Compressed Hourglass

The abstract compresses the full paper into a single hourglass:

```
Context (1 sentence, broad)
  → Gap (1 sentence, narrow)
    → Methods (1 sentence)
      → Key result (1–2 sentences, quantitative)
        → Implication (1 sentence, bounded)
```

### Example

> Waterborne epoxy modification has been used to improve the performance of
> emulsified asphalt, but the relationship between epoxy content and interface
> bonding strength is not well established. This study investigated the bond
> strength of waterborne epoxy modified emulsified asphalt (WER-EA) at
> different epoxy contents using pull-off tests (ASTM D7234) and FTIR
> analysis. The 15% WER group showed the highest mean bond strength
> (0.78 MPa), 73% higher than the control. FTIR results are consistent with
> epoxy crosslinking as a contributing mechanism. The findings support WER
> modification as a promising approach for improving interlayer bonding,
> subject to field validation.

---

## Polishing the Shape

When polishing, do not just fix sentences — verify the **shape** of each
section:

| Section | Expected shape | If wrong |
|---|---|---|
| Introduction | Narrowing funnel | Move broad context before the gap |
| Results | Evidence ladder | Lead with data, not interpretation |
| Discussion | Widening funnel | Move new data to Results; add limitation |
| Conclusions | Closing triangle | Remove methods; add boundary |
| Abstract | Compressed hourglass | Verify all 5 layers present |
