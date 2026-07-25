# Materials Science Language Rulebook

Use clear, evidence-bound manuscript language.

## Sentence Control

- Target: most sentences under 30 words. Hard ceiling: 35 words.
- Put the material, test, result, and interpretation in a logical order.
- Avoid stacking three causal links in one sentence.
- Use one measured result per sentence when discussing data.
- Each sentence should express one main proposition.
- Do not join two independent clauses with only a comma.
- Dependent clauses must stay attached to a main clause.

### Sentence length audit

After drafting, scan for sentences exceeding 35 words. Split or restructure:

- bad: `The WER modified emulsified asphalt, which was prepared with 20% WER content and cured at 60°C for 24 h, showed a bonding strength of 0.41 MPa that was 73.2% higher than the base asphalt measured under the same conditions using the pull-off test according to ASTM D7234.` (49 words)
- better: `The WER-EA with 20% WER content showed a bonding strength of 0.41 MPa after curing at 60°C for 24 h (ASTM D7234 pull-off test). This was 73.2% higher than the base asphalt.` (35 words, split into 2)

## Tense Rules

| Section | Tense | Example |
|---|---|---|
| Abstract (methods) | past | `The bonding strength was measured using...` |
| Abstract (results) | past | `The results showed that...` |
| Abstract (implication) | present | `These findings suggest that...` |
| Introduction (known facts) | present | `WER improves the high-temperature performance of asphalt.` |
| Introduction (previous studies) | past | `Zhang et al. reported that...` |
| Methods | past | `Specimens were prepared and tested according to...` |
| Results | past | `The bonding strength increased with WER content.` |
| Discussion (interpretation) | present | `This improvement may be attributed to the crosslinking reaction.` |
| Discussion (comparison) | past or present | `Our results are consistent with those of Kong et al.` |
| Conclusions | present | `WER-EA shows superior bonding performance.` |
| Conclusions (specific findings) | past | `The optimal WER content was 20%.` |

### Tense audit checklist

- [ ] Methods section: all procedures in past tense
- [ ] Results section: all observations in past tense
- [ ] Discussion: interpretation in present, comparison with literature in past or present
- [ ] No mixing of past and present within a single paragraph without justification
- [ ] Figure/Table references: present tense (`Figure 1 shows...`, `Table 3 lists...`)

## Preferred Verbs

### Evidence strength ladder

Choose verbs that match the evidence level:

**Strong** (direct measurement confirmed by multiple methods):

- show, demonstrate, establish, reveal, identify, confirm
- Use only when the design and data justify a strong claim

**Moderate** (consistent trend, single method, or limited conditions):

- suggest, indicate, support the view that, are consistent with, point to
- Use when the interpretation is plausible but not definitive

**Speculative** (mechanism inference beyond direct observation):

- may reflect, could arise from, appears to, seems likely, might be explained by
- Use when moving beyond direct observation

### Domain-specific verb table

| Evidence situation | Prefer | Avoid unless directly proven |
|---|---|---|
| measured trend | showed, exhibited, increased, decreased | proved, confirmed |
| inferred mechanism | suggested, indicated, may be attributed to | demonstrated, verified |
| direct mechanism evidence | confirmed by FTIR/SEM/rheology | speculated |
| comparison | outperformed, was higher than, was lower than | was excellent |
| engineering implication | may improve, has potential to | can completely solve |
| durability claim | maintained X after Y exposure | guaranteed long-term performance |
| field application | is expected to perform, shows promise for | will solve the problem |

## Hedging and Qualification

Use hedging to calibrate claim strength:

### Hedging patterns

- `The results suggest that...` (not `prove that`)
- `This improvement may be associated with...` (not `is caused by`)
- `Within the investigated dosage range...` (not `in general`)
- `Under the tested curing condition...` (not `under all conditions`)
- `Compared with the control group...` (not `compared with all materials`)
- `This finding should be interpreted with caution because...`
- `To our knowledge, this is the first study to...` (not `This is the first study to`)

### Hedging audit

Flag and soften:

- `prove` → `show`, `demonstrate`
- `conclusively` → remove
- `unprecedented` → `to our knowledge, not previously reported`
- `best` → `among the highest`, `optimal within the tested range`
- `superior` → `higher`, `better under the tested conditions`
- `first` → `to our knowledge, the first` (only if verified)
- `always` → `under the tested conditions`
- `never` → `was not observed in this study`
- `completely` → remove or qualify
- `perfect` → remove or qualify

## Reviewer-Safe Phrases

### Agreement and clarification

- We appreciate the reviewer's insightful comment.
- The reviewer raises a valid point regarding...
- We agree with the reviewer that...
- Thank you for this suggestion, which has improved the manuscript.

### Disagreement with evidence

- We respectfully note that...
- The available evidence suggests that...
- While this is a reasonable concern, our data indicate that...

### Limitation acknowledgment

- A limitation of this study is that...
- We acknowledge that...
- These findings should be interpreted within the context of...
- The generalizability of these results is limited by...

### Future work

- Further work is needed to determine whether...
- Future studies should examine...
- A useful next step would be to...

## Materials Science Style

- Always keep units and test conditions near the result.
- Name the control group before claiming improvement.
- Do not call a material "green" or "environmentally friendly" without LCA, emission, or resource-bound evidence.
- Do not call a mechanism "confirmed" without direct mechanism evidence.
- Do not use `significant` without statistical test results.
- Use SI units; spell out units in text (megapascals, not MPa) at first use.
- Standard names: write in full at first mention with abbreviation in parentheses.
- Test standards: cite the standard number (ASTM D7234, JTG E20-T 0715) near the result.
- Specimen dimensions: always state geometry and size near the measured value.
- Temperature, loading rate, and curing conditions must appear near any performance claim.
