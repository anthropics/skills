# Assertion classification

A clinical finding's relationship to the patient is captured on **three independent axes**, not one label. Set only the axes the note moves off default; omit the rest.

| axis | values | default | what moves it |
|---|---|---|---|
| `presence` | `present` · `absent` · `possible` | `present` | negation ("denies", "no evidence of", "afebrile") → `absent`. Hedging ("possible", "cannot exclude", "?", "borderline") → `possible`. |
| `temporality` | `current` · `historical` · `hypothetical` | `current` | past/resolved ("history of", "prior", "s/p") → `historical`. Conditional, anticipated, monitored-for, prophylaxis-for, rule-out → `hypothetical`. |
| `experiencer` | `patient` · `family_member` · `other` | `patient` | finding asserted of a relative → `family_member`. Asserted of donor, fetus, or other non-patient → `other`. |

The axes are independent: "mother denied prior MI" is `{presence: absent, temporality: historical, experiencer: family_member}`. No precedence rule, no information loss.

## Examples

| note text | presence | temporality | experiencer |
|---|---|---|---|
| "Patient reports nausea." | present | current | patient |
| "Denies chest pain." | **absent** | current | patient |
| "Possible pneumonia." | **possible** | current | patient |
| "History of DVT in 2018." | present | **historical** | patient |
| "Monitor for GI bleed." / "Rule out PE." / "for DVT prophylaxis" | present | **hypothetical** | patient |
| "Mother with breast cancer." | present | current | **family_member** |
| "No family history of early CAD." | **absent** | current | **family_member** |
| "Father may have had Huntington's." | **possible** | **historical** | **family_member** |

## Projection to i2b2 2010

For benchmark scoring against the i2b2/n2c2 2010 assertion task, project to its flat 6-class label deterministically:

```
if experiencer != patient        → associated_with_someone_else
elif temporality == hypothetical → hypothetical
elif presence == absent          → absent
elif presence == possible        → possible
else                             → present
```

(`historical` has no i2b2 class; it projects to `present`/`absent`/`possible` per the other axes.)

## Provenance

This is the ConText orthogonal-axes model (Harkema, Dowling, Thornblade, Chapman. *J Biomed Inform.* 2009;42(5):839-51) as operationalized in the ShARe/SHARPn schema (Mowery et al., CLEF 2014; Elhadad et al., SemEval-2015 Task 14), with deterministic projection to the i2b2 2010 assertion classes (Uzuner, South, Shen, DuVall. *JAMIA.* 2011;18(5):552-6) for benchmark compatibility. It is the output shape used by cTAKES, MedSpaCy, Amazon Comprehend Medical, and Google Healthcare NLP, and maps directly to SNOMED CT situation-with-explicit-context attributes (408729009 finding context / 408731000 temporal context / 408732007 subject relationship context).
