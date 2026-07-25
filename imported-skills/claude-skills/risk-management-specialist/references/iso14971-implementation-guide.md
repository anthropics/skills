# ISO 14971:2019 Implementation Guide

Complete implementation framework for medical device risk management per ISO 14971:2019.

---

## Table of Contents

- [Risk Management Planning](#risk-management-planning)
- [Risk Analysis](#risk-analysis)
- [Risk Evaluation](#risk-evaluation)
- [Risk Control](#risk-control)
- [Overall Residual Risk Evaluation](#overall-residual-risk-evaluation)
- [Risk Management Report](#risk-management-report)
- [Production and Post-Production Activities](#production-and-post-production-activities)

---

## Risk Management Planning

### Risk Management Plan Content

| Element | Requirement | Documentation |
|---------|-------------|---------------|
| Scope | Medical device and lifecycle stages covered | Scope statement |
| Responsibilities | Personnel and authority assignments | Organization chart, RACI |
| Review Requirements | Timing and triggers for reviews | Review schedule |
| Acceptability Criteria | Risk acceptance matrix and policy | Risk acceptability criteria |
| Verification Activities | Methods for control verification | Verification plan |
| Production/Post-Production | Activities for ongoing risk management | Surveillance plan |

### Risk Management Plan Template

```
RISK MANAGEMENT PLAN

Document Number: RMP-[Product]-[Rev]
Product: [Device Name]
Revision: [X.X]
Effective Date: [Date]

1. SCOPE AND PURPOSE
   1.1 Medical Device Description: [Description]
   1.2 Intended Use: [Statement]
   1.3 Lifecycle Stages Covered: [Design/Production/Post-Market]
   1.4 Plan Objectives: [Objectives]

2. RESPONSIBILITIES AND AUTHORITIES
   | Role | Responsibility | Authority |
   |------|----------------|-----------|
   | Risk Management Lead | Overall RM process | RM decisions |
   | Design Engineer | Risk identification | Design changes |
   | QA Manager | RM file review | File approval |
   | Clinical | Clinical input | Clinical risk assessment |

3. RISK ACCEPTABILITY CRITERIA
   3.1 Risk Matrix: [Reference to matrix]
   3.2 Acceptability Policy: [Acceptable/Reduction-required (AFAP for EU)/Unacceptable definitions]
   3.3 Benefit-Risk Considerations: [When applicable]

4. VERIFICATION ACTIVITIES
   4.1 Risk Control Verification Methods: [Test, Analysis, Review]
   4.2 Verification Timing: [Design phase, V&V]
   4.3 Acceptance Criteria: [Pass/fail criteria]

5. PRODUCTION AND POST-PRODUCTION
   5.1 Information Collection: [Sources]
   5.2 Review Triggers: [Events requiring review]
   5.3 Update Process: [RM file update procedure]

6. REVIEW AND APPROVAL
   Prepared By: _________________ Date: _______
   Reviewed By: _________________ Date: _______
   Approved By: _________________ Date: _______
```

### Risk Acceptability Criteria Definition

| Risk Level | Definition | Action Required |
|------------|------------|-----------------|
| Broadly Acceptable | Risk so low that no action needed | Document and monitor (EU MDR: still reduce as far as possible) |
| Tolerable after reduction AFAP | Risk reduced as far as possible | Verify all further reduction options exhausted; consider benefit |
| Unacceptable | Risk exceeds acceptable threshold | Risk control mandatory |

> **EU MDR note:** For CE-marked devices the criterion is **as far as possible (AFAP)** without economic considerations (MDR Annex I GSPR 1–4; EN ISO 14971:2019/A11:2021 Z-annexes). ALARP — which weighs cost against benefit of further reduction — is not acceptable under the EU MDR; it may persist in some non-EU jurisdictions, where the deviation from EU requirements must be flagged explicitly. ISO 14971:2019 removed ALARP from its normative text.

### Risk Matrix Example (5x5)

| Probability \ Severity | Negligible | Minor | Serious | Critical | Catastrophic |
|------------------------|------------|-------|---------|----------|--------------|
| Frequent | Medium | High | High | Unacceptable | Unacceptable |
| Probable | Low | Medium | High | High | Unacceptable |
| Occasional | Low | Medium | Medium | High | High |
| Remote | Low | Low | Medium | Medium | High |
| Improbable | Low | Low | Low | Medium | Medium |

**Risk Level Actions:**
- **Low (Acceptable):** Document; EU MDR: still reduce as far as possible
- **Medium (reduce AFAP):** Reduce as far as possible, document why further reduction is impossible
- **High (reduce AFAP):** Risk reduction required; demonstrate all further options exhausted
- **Unacceptable:** Risk reduction mandatory before proceeding

---

## Risk Analysis

### Hazard Identification Methods

| Method | Application | Standard Reference |
|--------|-------------|-------------------|
| FMEA | Component/subsystem failures | IEC 60812 |
| FTA | System-level failure analysis | IEC 61025 |
| HAZOP | Process hazard identification | IEC 61882 |
| PHA | Preliminary hazard assessment | - |
| Use FMEA | Use-related hazards | IEC 62366-1 |

### Intended Use Analysis Checklist

| Category | Questions to Address |
|----------|---------------------|
| Medical Purpose | What condition is treated/diagnosed? |
| Patient Population | Age, health status, contraindications? |
| User Population | Healthcare professional, patient, caregiver? |
| Use Environment | Hospital, home, ambulatory? |
| Duration | Single use, repeated, continuous? |
| Body Contact | External, internal, implanted? |

### Hazard Categories (Informative Annex C)

| Category | Examples |
|----------|----------|
| Energy | Electrical, thermal, mechanical, radiation |
| Biological | Bioburden, pyrogens, biocompatibility |
| Chemical | Residues, degradation products, leachables |
| Operational | Incorrect output, delayed function, unexpected operation |
| Information | Incomplete instructions, inadequate warnings |
| Use Environment | Electromagnetic, mechanical stress |

### Hazardous Situation Documentation

```
HAZARD ANALYSIS WORKSHEET

Product: [Device Name]
Analyst: [Name]
Date: [Date]

| ID | Hazard | Hazardous Situation | Sequence of Events | Harm | P1 | P2 | Initial Risk |
|----|--------|--------------------|--------------------|------|----|----|--------------|
| H-001 | [Hazard] | [Situation] | [Sequence] | [Harm] | [Prob] | [Sev] | [Level] |

P1 = Probability of hazardous situation occurring
P2 = Probability of harm given hazardous situation
Initial Risk = Risk before controls
```

### Risk Estimation

**Probability Categories:**

| Level | Term | Definition | Frequency |
|-------|------|------------|-----------|
| 5 | Frequent | Expected to occur | >10⁻³ |
| 4 | Probable | Likely to occur | 10⁻³ to 10⁻⁴ |
| 3 | Occasional | May occur | 10⁻⁴ to 10⁻⁵ |
| 2 | Remote | Unlikely to occur | 10⁻⁵ to 10⁻⁶ |
| 1 | Improbable | Very unlikely | <10⁻⁶ |

**Severity Categories:**

| Level | Term | Definition | Patient Impact |
|-------|------|------------|----------------|
| 5 | Catastrophic | Results in death | Death |
| 4 | Critical | Results in permanent impairment | Permanent impairment |
| 3 | Serious | Results in injury requiring intervention | Injury requiring treatment |
| 2 | Minor | Results in temporary injury | Temporary discomfort |
| 1 | Negligible | Inconvenience or temporary discomfort | No injury |

---

## Risk Evaluation

### Evaluation Workflow

1. Apply risk acceptability criteria to estimated risk
2. Determine if risk is acceptable, requires further reduction (AFAP), or is unacceptable
3. For risks requiring reduction, document the AFAP demonstration
4. For unacceptable risks, proceed to risk control
5. Document evaluation rationale
6. **Validation:** All risks evaluated against criteria; rationale documented

### Risk Acceptability Decision

| Initial Risk | Benefit Available | Decision |
|--------------|-------------------|----------|
| Acceptable | N/A | Accept, document |
| Reduced AFAP | No | Verify all reduction options exhausted |
| Reduced AFAP | Yes | Include in benefit-risk |
| Unacceptable | No | Design change required |
| Unacceptable | Yes | Benefit-risk analysis |

### AFAP Demonstration (EU MDR)

| Criterion | Evidence Required |
|-----------|-------------------|
| All control options considered | Analysis of every feasible alternative per the control hierarchy |
| Further reduction impossible | Evidence remaining options are technically infeasible or do not further reduce risk |
| State of the art | Review of similar devices |
| User acceptance | Stakeholder input |

> Economic considerations must not enter the acceptability decision for EU-market devices (MDR Annex I GSPR 2; EN ISO 14971:2019/A11:2021 Z-annexes). ALARP-style cost-benefit weighing of further risk reduction is prohibited in this context.

---

## Risk Control

### Risk Control Hierarchy

| Priority | Control Type | Examples |
|----------|--------------|----------|
| 1 | Inherent safety by design | Remove hazard, substitute material |
| 2 | Protective measures in device | Guards, alarms, software limits |
| 3 | Information for safety | Warnings, training, IFU |

### Risk Control Option Analysis

```
RISK CONTROL OPTION ANALYSIS

Hazard ID: [H-XXX]
Risk Level: [Unacceptable/High]

| Option | Control Type | Effectiveness | Feasibility | New Risks | Selected |
|--------|--------------|---------------|-------------|-----------|----------|
| Option 1 | [Type] | [H/M/L] | [H/M/L] | [Yes/No] | [Yes/No] |
| Option 2 | [Type] | [H/M/L] | [H/M/L] | [Yes/No] | [Yes/No] |

Selected Option: [Option X]
Rationale: [Justification]
```

### Risk Control Implementation Record

```
RISK CONTROL IMPLEMENTATION

Control ID: RC-[XXX]
Related Hazard: H-[XXX]

Control Description: [Description]
Control Type: [ ] Inherent Safety [ ] Protective Measure [ ] Information

Implementation:
- Specification/Requirement: [Reference]
- Design Document: [Reference]
- Verification Method: [Test/Analysis/Review]
- Verification Criteria: [Pass criteria]

Verification:
- Protocol Reference: [Document]
- Execution Date: [Date]
- Result: [ ] Pass [ ] Fail
- Evidence Reference: [Document]

New Risks Introduced: [ ] Yes [ ] No
If Yes: [New Hazard ID references]

Residual Risk:
- P1: [Probability]
- P2: [Severity]
- Residual Risk Level: [Level]

Approved By: _________________ Date: _______
```

### Risk Control Verification Methods

| Method | Application | Evidence |
|--------|-------------|----------|
| Test | Quantifiable control effectiveness | Test report |
| Inspection | Physical control presence | Inspection record |
| Analysis | Design analysis confirmation | Analysis report |
| Review | Document/drawing review | Review record |

---

## Overall Residual Risk Evaluation

### Evaluation Process

1. Compile all individual residual risks
2. Consider cumulative effects of residual risks
3. Assess overall residual risk acceptability
4. Conduct benefit-risk analysis if required
5. Document overall evaluation conclusion
6. **Validation:** All residual risks compiled; overall evaluation complete

### Benefit-Risk Analysis

| Factor | Assessment |
|--------|------------|
| Clinical Benefit | Documented therapeutic benefit |
| State of the Art | Comparison to alternative treatments |
| Patient Expectation | Benefit patient would accept |
| Medical Opinion | Clinical expert input |
| Risk Quantification | Residual risk characterization |

### Benefit-Risk Documentation

```
BENEFIT-RISK ANALYSIS

Product: [Device Name]
Date: [Date]

BENEFITS:
1. Primary Clinical Benefit: [Description]
   - Evidence: [Reference]
   - Magnitude: [Quantification]

2. Secondary Benefits: [List]

RISKS:
1. Residual Risks Summary:
   | Risk Category | Count | Highest Level |
   |---------------|-------|---------------|
   | Acceptable | [N] | Low |
   | Reduced AFAP | [N] | Medium/High |

2. Cumulative Considerations: [Assessment]

COMPARISON:
- State of the Art: [How device compares]
- Alternative Treatments: [Risk comparison]
- Patient Acceptance: [Expected acceptance]

CONCLUSION:
[ ] Benefits outweigh risks - Acceptable
[ ] Benefits do not outweigh risks - Not Acceptable

Rationale: [Justification]

Approved By: _________________ Date: _______
```

---

## Risk Management Report

### Report Content Requirements

| Section | Content |
|---------|---------|
| Results of Risk Analysis | Summary of hazards and risks identified |
| Risk Control Decisions | Controls selected and implemented |
| Overall Residual Risk | Evaluation and acceptability conclusion |
| Benefit-Risk Conclusion | If applicable |
| Review and Approval | Formal sign-off |

### Risk Management Report Template

```
RISK MANAGEMENT REPORT

Document Number: RMR-[Product]-[Rev]
Product: [Device Name]
Date: [Date]

1. EXECUTIVE SUMMARY
   - Total hazards identified: [N]
   - Risk controls implemented: [N]
   - Residual risks: [N] acceptable, [N] reduced AFAP
   - Overall conclusion: [Acceptable/Not Acceptable]

2. RISK ANALYSIS SUMMARY
   - Methods used: [FMEA, FTA, etc.]
   - Scope coverage: [Lifecycle stages]
   - Hazard categories addressed: [List]

3. RISK EVALUATION SUMMARY
   | Risk Level | Before Control | After Control |
   |------------|----------------|---------------|
   | Unacceptable | [N] | [N] |
   | High | [N] | [N] |
   | Medium | [N] | [N] |
   | Low | [N] | [N] |

4. RISK CONTROL SUMMARY
   - Inherent safety controls: [N]
   - Protective measures: [N]
   - Information for safety: [N]
   - All controls verified: [Yes/No]

5. OVERALL RESIDUAL RISK
   - Individual residual risks: [Summary]
   - Cumulative assessment: [Conclusion]
   - Acceptability: [Acceptable/Reduced as far as possible (AFAP) demonstrated]

6. BENEFIT-RISK ANALYSIS (if applicable)
   - Conclusion: [Statement]

7. PRODUCTION AND POST-PRODUCTION
   - Monitoring plan: [Reference]
   - Review triggers: [List]

8. CONCLUSION
   [Statement of overall risk acceptability]

9. APPROVAL
   Risk Management Lead: _________________ Date: _______
   Quality Assurance: _________________ Date: _______
   Management Representative: _________________ Date: _______
```

---

## Production and Post-Production Activities

### Information Sources

| Source | Information Type | Review Frequency |
|--------|------------------|------------------|
| Complaints | Use-related issues, failures | Continuous |
| Service Reports | Field failures, repairs | Monthly |
| Vigilance Reports | Serious incidents | Immediate |
| Literature | Similar device issues | Quarterly |
| Regulatory Feedback | Authority communications | As received |
| Clinical Data | Post-market clinical follow-up | Per PMCF plan |

### Risk Management File Update Triggers

| Trigger | Action Required |
|---------|-----------------|
| New hazard identified | Risk analysis update |
| Control failure | Risk control reassessment |
| Serious incident | Immediate risk review |
| Design change | Impact assessment |
| Standards update | Compliance review |
| Regulatory feedback | Risk evaluation update |

### Risk Management Review Record

```
RISK MANAGEMENT REVIEW RECORD

Review Date: [Date]
Review Type: [ ] Periodic [ ] Triggered
Trigger (if applicable): [Description]

INFORMATION REVIEWED:
| Source | Period | Findings |
|--------|--------|----------|
| Complaints | [Period] | [Summary] |
| Vigilance | [Period] | [Summary] |
| Literature | [Period] | [Summary] |

RISK MANAGEMENT FILE STATUS:
- Current and complete: [ ] Yes [ ] No
- Updates required: [ ] Yes [ ] No

ACTIONS:
| Action | Owner | Due Date |
|--------|-------|----------|
| [Action 1] | [Name] | [Date] |

CONCLUSION:
[ ] No changes to risk profile
[ ] Risk profile updated - see [Document Reference]
[ ] Further investigation required

Reviewed By: _________________ Date: _______
```
