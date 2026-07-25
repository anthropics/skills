# Clinical Citation Verification Checklist

This example shows how to apply citation verification discipline to a health or clinical research draft. It is intentionally a checklist and example, not a new agent behavior contract.

Use this when a draft cites clinical outcomes, diagnostic accuracy, treatment effects, safety claims, screening performance, or health-policy conclusions.

---

## Scenario

A draft contains the following claim:

> AI-assisted retinal image screening achieved 99% sensitivity and 98% specificity for diabetic retinopathy detection and should be deployed broadly in primary care.

The claim cites one paper, but the draft does not include a DOI, PubMed ID, trial registry ID, page number, table number, or quoted source passage.

---

## Verification Checklist

| Check | Required evidence | Pass condition | Fail condition |
|---|---|---|---|
| Reference existence | DOI, PMID, arXiv ID, trial registry ID, or resolvable title-author-year lookup | The cited work resolves in an external index or publisher page | Citation cannot be resolved or metadata conflicts |
| Claim anchor | Page, section, table, figure, or short quoted passage | The cited source contains the specific number or statement | Source exists but does not contain the claimed evidence |
| Population match | Study population and setting | Draft claim matches the source population and setting | Draft generalizes from a narrow or different population |
| Outcome match | Sensitivity, specificity, effect size, endpoint, or qualitative finding | Draft uses the same endpoint and metric definition | Draft swaps endpoint, timeframe, comparator, or metric |
| Strength of conclusion | Source conclusion and limitations | Draft preserves uncertainty and limitations | Draft turns "may", "in this dataset", or "needs validation" into broad deployment advice |
| Clinical boundary | Human review and intended use | Draft frames output as research, evidence synthesis, or tool evaluation | Draft becomes patient-specific diagnosis, treatment, triage, or deployment instruction |

---

## Example Audit Result

| Field | Result |
|---|---|
| Claim | AI-assisted retinal image screening achieved 99% sensitivity and 98% specificity and should be deployed broadly in primary care. |
| Citation status | `existence_unverified` |
| Anchor status | `anchor_missing` |
| Support status | `unsupported_until_verified` |
| Clinical safety status | `overclaim_risk` |
| Required next step | Resolve the citation externally, then locate the exact source passage or table supporting both metrics. |

---

## Safer Rewrite Pattern

If the citation cannot yet be verified:

> Evidence status: unverified. The draft claims diagnostic performance for AI-assisted diabetic retinopathy screening, but the cited source has not been resolved and no source-text anchor is available. Do not report the sensitivity, specificity, or deployment recommendation until the reference is externally resolved and the exact supporting passage is located.

If the citation exists but only supports a narrow setting:

> In the cited validation dataset, the AI-assisted retinal image system reported [metric] for [population/setting]. This does not by itself establish broad primary-care deployment readiness; additional external validation, workflow evaluation, and qualified clinical review are required.

---

## Output Template

```markdown
## Clinical Citation Verification

### Claim Under Review
- Claim:
- Citation key:
- Paper section:

### Deterministic Lookup
- DOI / PMID / registry ID:
- External lookup result:
- Metadata match:

### Source Anchor
- Page / section / table / figure:
- Supporting passage:
- Anchor status:

### Claim-to-Source Match
- Population:
- Outcome:
- Metric:
- Limitation preserved:

### Verdict
- VERIFIED / MINOR_DISTORTION / MAJOR_DISTORTION / UNVERIFIABLE / UNVERIFIABLE_ACCESS:
- Rationale:

### Clinical Safety Note
- This is research, evidence synthesis, or documentation support only. It is not patient-specific diagnosis, treatment, triage, or clinical decision support.
```

---

## Relation to Citation Verification Work

This example is related to the deterministic citation verification gate proposed in issue #182. It demonstrates the manual clinical checklist that such a gate should preserve: reference existence is necessary, but not sufficient. The cited source must also anchor the exact clinical claim, population, metric, and conclusion strength.
