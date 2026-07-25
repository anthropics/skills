# IRB/Ethics Review Checklist

Structured checklist for study_manager_agent ETHICS phase. Agent presents each item, user answers, agent records status.

## Instructions

- Present one category at a time
- For each item, record: PASS / NEEDS_ACTION / NOT_APPLICABLE
- Any NEEDS_ACTION in categories 1-3 → ethics_status: ETHICS_BLOCKED
- Any applicable NEEDS_ACTION in category 4 → ethics_status: ETHICS_BLOCKED
- Category 5.1 missing required approval/exemption → ethics_status: ETHICS_PENDING
- Any NEEDS_ACTION in category 5.2-6.4 → ethics_status: ETHICS_PENDING
- `ETHICS_PENDING` means planning may continue, but participant recruitment and data collection cannot start until status becomes `READY`
- All required items PASS or NOT_APPLICABLE, and institutional approval is `Approved` or `Exempt` when required → ethics_status: READY

---

## Category 1: Informed Consent (CRITICAL)

| # | Item | Check |
|---|------|-------|
| 1.1 | Consent pathway documented | Required for all studies involving human participants; signed, digital, or IRB-approved waiver/implied consent depending on study type |
| 1.2 | Consent form in participant-accessible language | No jargon; translated if needed |
| 1.3 | Consent form describes: purpose, procedures, duration | Must be explicit |
| 1.4 | Consent form describes: risks and benefits | Even if minimal risk |
| 1.5 | Consent form states: voluntary participation, right to withdraw | Must be unconditional |
| 1.6 | Consent form states: data handling and confidentiality | How data will be stored, who has access |
| 1.7 | For online studies: appropriate consent mechanism | Click-through, e-signature, information sheet, or IRB-approved implied consent |
| 1.8 | For minors (< 18): parental consent + child assent | Both required |

## Category 2: Privacy and Data Protection (CRITICAL)

| # | Item | Check |
|---|------|-------|
| 2.1 | Data anonymized or pseudonymized | Direct identifiers removed or coded |
| 2.2 | Secure storage location defined | Encrypted drive, institutional server, not personal cloud |
| 2.3 | Data retention period defined | How long kept, when destroyed |
| 2.4 | Access control specified | Who can access raw data, under what conditions |
| 2.5 | Data transfer method secure | Encrypted transmission if sent electronically |
| 2.6 | Compliance with local data protection laws | GDPR, PDPA, or local equivalent |

## Category 3: Risk Assessment (CRITICAL)

| # | Item | Check |
|---|------|-------|
| 3.1 | Physical risks assessed | Any physical procedure or environmental exposure |
| 3.2 | Psychological risks assessed | Sensitive topics, stress, discomfort |
| 3.3 | Social risks assessed | Stigma, discrimination, professional consequences |
| 3.4 | Risk mitigation plan documented | For each identified risk |
| 3.5 | Debriefing protocol (if deception used) | Must explain deception and provide support |
| 3.6 | Support resources available | Counseling, hotline, or referral for distressed participants |

## Category 4: Vulnerable Populations

| # | Item | Check |
|---|------|-------|
| 4.1 | Minors: additional protections in place | Age-appropriate materials, parental consent |
| 4.2 | Prisoners/detainees: no coercion | Voluntary participation genuinely free |
| 4.3 | Patients: therapeutic misconception addressed | Clear that research is not treatment |
| 4.4 | Students/employees: power differential mitigated | Cannot affect grades/employment |
| 4.5 | Cognitively impaired: capacity assessment | Legally authorized representative if needed |

## Category 5: Institutional Requirements

| # | Item | Check |
|---|------|-------|
| 5.1 | IRB/ethics committee approval status | Approved / Submitted / Not yet submitted / Exempt |
| 5.2 | Protocol registration (if required) | ClinicalTrials.gov, OSF, or other registry |
| 5.3 | Funding agency requirements met | Some funders have additional ethics requirements |

## Category 6: Data Management Plan

| # | Item | Check |
|---|------|-------|
| 6.1 | Data collection instruments validated | Reliability/validity evidence for scales |
| 6.2 | Data cleaning plan documented | How missing data, outliers will be handled |
| 6.3 | Analysis plan pre-specified | Prevent post-hoc fishing |
| 6.4 | Data sharing plan | Will anonymized data be shared? Under what terms? |
