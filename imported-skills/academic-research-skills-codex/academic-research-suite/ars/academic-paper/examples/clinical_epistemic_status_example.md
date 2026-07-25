# Clinical Epistemic Status Example

This example shows how to detect silent epistemic upgrades in clinical and health research writing. It is a documentation example, not a schema decision for the final `epistemic_status` vocabulary.

Use this when a draft turns preliminary, observational, in-vitro, or hypothesis-level evidence into stronger clinical or causal language.

---

## Scenario

A draft contains the following sentence:

> In this EHR cohort, GLP-1 receptor agonist use prevented cardiovascular hospitalization in patients with type 2 diabetes and should be prioritized in routine care based on this study alone.

The cited source is a retrospective electronic health record cohort study. The source text says:

> In this retrospective cohort, GLP-1 receptor agonist exposure was associated with a lower rate of cardiovascular hospitalization after adjustment for measured covariates. Residual confounding remains possible, and prospective trials are needed before practice recommendations can be made.

The citation may be real and correctly formatted, but the draft still overstates the source.

---

## Status Mapping

This example uses the current 5-tier claim-confidence vocabulary as the primary status. The biomedical research-design labels are illustrative future `evidence_type` examples, not co-equal schema fields.

| Field | Conservative label | Why |
|---|---|---|
| Current 5-tier claim-confidence status | `Supported` | The finding has empirical support from the cited source, but the source remains observational and limited by residual confounding. |
| Illustrative future `evidence_type` | `observational_evidence` | The study design supports association language, not an intervention-level causal claim. |
| Disallowed upgrade | `causal_claim` / `validated_conclusion` | The source explicitly says residual confounding remains possible and trials are needed. |

Do not treat the illustrative `evidence_type` label as a schema decision. For this example, the safety rule is simpler: the draft cannot use stronger language than the source supports.

---

## Silent Upgrade Audit

| Source signal | Draft language | Upgrade type | Safer rewrite |
|---|---|---|---|
| "retrospective cohort" | "prevented" | Observational to causal | "was associated with a lower rate of..." |
| "associated with" | "prevented" | Association to cause | "was associated with..." |
| "after adjustment for measured covariates" | omitted | Confounding hedge dropped | "after adjustment for measured covariates, with residual confounding possible..." |
| "prospective trials are needed" | "should be prioritized in routine care based on this study alone" | Single-source evidence summary to clinical recommendation | "this cited EHR cohort alone does not establish routine-care prioritization..." |
| "patients with type 2 diabetes" | broad clinical population implied | Population scope widened | "in the studied type 2 diabetes cohort..." |

---

## Checklist

Before accepting a clinical claim, verify:

1. **Study design**: Does the source describe an RCT, cohort, case-control study, cross-sectional study, in-vitro study, animal model, qualitative study, or hypothesis paper?
2. **Verb strength**: Does the draft use verbs such as "causes", "prevents", "proves", "establishes", or "should be used" when the source only says "associated", "suggests", "may", or "needs validation"?
3. **Clinical action**: Does the draft move from evidence summary to diagnosis, treatment, triage, deployment, or routine-care recommendation?
4. **Population scope**: Does the draft generalize beyond the source population, setting, disease stage, or inclusion criteria?
5. **Endpoint, effect-size, and timeframe scope**: Does the draft preserve the same endpoint, effect measure, absolute-vs-relative framing, comparator, and follow-up period used by the source?
6. **Protected hedges**: Are phrases such as "retrospective", "observational", "in this cohort", "preliminary", "may", "associated with", and "requires validation" preserved?
7. **Human review boundary**: If the claim affects clinical interpretation, does the draft frame the output as research synthesis rather than patient-specific advice?

---

## Example Verdict

```yaml
# Illustrative only; not a #183 schema proposal.
claim_under_review: "In this EHR cohort, GLP-1 receptor agonist use prevented cardiovascular hospitalization in patients with type 2 diabetes and should be prioritized in routine care based on this study alone."
source_design: "retrospective cohort"
source_anchor: "associated with a lower rate... residual confounding remains possible... prospective trials are needed"
source_finding_status: "Supported"
draft_claim_problem: "silent_upgrade_detected"
illustrative_evidence_type: "observational_evidence"
silent_upgrade_detected: true
upgrade_kind:
  - "association_to_cause"
  - "observational_to_clinical_recommendation"
  - "hedge_drop"
required_rewrite: "After adjustment for measured covariates, GLP-1 receptor agonist exposure was associated with a lower rate of cardiovascular hospitalization in the studied type 2 diabetes EHR cohort; residual confounding remains possible, and this cited EHR cohort alone does not establish routine-care prioritization."
clinical_safety_note: "Research synthesis only. Not patient-specific diagnosis, treatment, triage, or clinical decision support."
```

The YAML block is illustrative. It is not a proposed schema for #183; fields such as `upgrade_kind`, `clinical_safety_note`, `source_finding_status`, `draft_claim_problem`, and `illustrative_evidence_type` are included only to make the clinical overclaim pattern visible.

---

## Mini Examples

These synthetic cases can guide future examples without committing to the final schema:

| Case | Weak source status | Unsafe draft upgrade | Expected correction |
|---|---|---|---|
| Association to cause | Observational association | "X caused lower mortality" | "X was associated with lower mortality in the studied cohort" |
| In-vitro to clinical use | Bench-only mechanism | "X is ready for patient treatment" | "X showed an in-vitro mechanism that requires animal and clinical validation" |
| Hypothesis to conclusion | Discussion hypothesis | "The study demonstrates X" | "The authors hypothesize X; direct evidence was not tested" |

---

## Relation to Epistemic Status Work

This example is related to issue #183. It uses the existing 5-tier claim-confidence vocabulary as primary and treats biomedical design-stage labels as illustrative future `evidence_type` examples. The clinical safety invariant is that downstream writing must not silently upgrade a source's evidentiary status, conclusion strength, population scope, or clinical actionability.
