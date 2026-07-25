---
name: "risk-management-specialist"
description: Medical device risk management specialist implementing ISO 14971 throughout product lifecycle. Provides risk analysis, risk evaluation, risk control, and post-production information analysis. Use when user mentions risk management, ISO 14971, risk analysis, FMEA, fault tree analysis, hazard identification, risk control, risk matrix, benefit-risk analysis, residual risk, risk acceptability, or post-market risk.
---

# Risk Management Specialist

ISO 14971:2019 risk management implementation throughout the medical device lifecycle.

---

## Table of Contents

- [Risk Management Planning Workflow](#risk-management-planning-workflow)
- [Risk Analysis Workflow](#risk-analysis-workflow)
- [Risk Evaluation Workflow](#risk-evaluation-workflow)
- [Risk Control Workflow](#risk-control-workflow)
- [Post-Production Risk Management](#post-production-risk-management)
- [Risk Assessment Templates](#risk-assessment-templates)
- [Decision Frameworks](#decision-frameworks)
- [Tools and References](#tools-and-references)

---

## Risk Management Planning Workflow

Establish risk management process per ISO 14971.

### Workflow: Create Risk Management Plan

1. Define scope of risk management activities:
   - Medical device identification
   - Lifecycle stages covered
   - Applicable standards and regulations
2. Establish risk acceptability criteria:
   - Define probability categories (P1-P5)
   - Define severity categories (S1-S5)
   - Create risk matrix with acceptance thresholds
3. Assign responsibilities:
   - Risk management lead
   - Subject matter experts
   - Approval authorities
4. Define verification activities:
   - Methods for control verification
   - Acceptance criteria
5. Plan production and post-production activities:
   - Information sources
   - Review triggers
   - Update procedures
6. Obtain plan approval
7. Establish risk management file
8. **Validation:** Plan approved; acceptability criteria defined; responsibilities assigned; file established

### Risk Management Plan Content

| Section | Content | Evidence |
|---------|---------|----------|
| Scope | Device and lifecycle coverage | Scope statement |
| Criteria | Risk acceptability matrix | Risk matrix document |
| Responsibilities | Roles and authorities | RACI chart |
| Verification | Methods and acceptance | Verification plan |
| Production/Post-Production | Monitoring activities | Surveillance plan |

### Risk Acceptability Matrix (5x5)

| Probability \ Severity | Negligible | Minor | Serious | Critical | Catastrophic |
|------------------------|------------|-------|---------|----------|--------------|
| **Frequent (P5)** | Medium | High | High | Unacceptable | Unacceptable |
| **Probable (P4)** | Medium | Medium | High | High | Unacceptable |
| **Occasional (P3)** | Low | Medium | Medium | High | High |
| **Remote (P2)** | Low | Low | Medium | Medium | High |
| **Improbable (P1)** | Low | Low | Low | Medium | Medium |

### Risk Level Actions

| Level | Acceptable | Action Required |
|-------|------------|-----------------|
| Low | Yes | Document and accept; still reduce as far as possible (EU MDR) |
| Medium | After reduction AFAP | Reduce as far as possible; document why further reduction is impossible |
| High | After reduction AFAP | Reduction required; demonstrate all further options exhausted |
| Unacceptable | No | Design change mandatory |

> **EU MDR — AFAP, not ALARP:** For CE-marked devices, risks must be reduced **as far as possible (AFAP)** without economic considerations (MDR Annex I, GSPR 1–4; EN ISO 14971:2019/A11:2021 Z-annexes deviation). ALARP ("as low as reasonably practicable"), which permits cost-benefit weighing in acceptability decisions, is **not an acceptable criterion under the EU MDR** — a notified body will flag it. ISO 14971:2019 itself removed ALARP from the normative text. ALARP may persist in some non-EU jurisdictions (e.g., the UK HSE tradition); if used outside the EU, flag the deviation from EU requirements explicitly.

---

## Risk Analysis Workflow

Identify hazards and estimate risks systematically.

### Workflow: Conduct Risk Analysis

1. Define intended use and reasonably foreseeable misuse:
   - Medical indication
   - Patient population
   - User population
   - Use environment
2. Select analysis method(s):
   - FMEA for component/function analysis
   - FTA for system-level analysis
   - HAZOP for process deviations
   - Use Error Analysis for user interaction
3. Identify hazards by category:
   - Energy hazards (electrical, mechanical, thermal)
   - Biological hazards (bioburden, biocompatibility)
   - Chemical hazards (residues, leachables)
   - Operational hazards (software, use errors)
4. Determine hazardous situations:
   - Sequence of events
   - Foreseeable misuse scenarios
   - Single fault conditions
5. Estimate probability of harm (P1-P5)
6. Estimate severity of harm (S1-S5)
7. Document in hazard analysis worksheet
8. **Validation:** All hazard categories addressed; all hazards documented; probability and severity assigned

### Hazard Categories Checklist

| Category | Examples | Analyzed |
|----------|----------|----------|
| Electrical | Shock, burns, interference | ☐ |
| Mechanical | Crushing, cutting, entrapment | ☐ |
| Thermal | Burns, tissue damage | ☐ |
| Radiation | Ionizing, non-ionizing | ☐ |
| Biological | Infection, biocompatibility | ☐ |
| Chemical | Toxicity, irritation | ☐ |
| Software | Incorrect output, timing | ☐ |
| Use Error | Misuse, perception, cognition | ☐ |
| Environment | EMC, mechanical stress | ☐ |

### Analysis Method Selection

| Situation | Recommended Method |
|-----------|-------------------|
| Component failures | FMEA |
| System-level failure | FTA |
| Process deviations | HAZOP |
| User interaction | Use Error Analysis |
| Software behavior | Software FMEA |
| Early design phase | PHA |

### Probability Criteria

| Level | Name | Description | Frequency |
|-------|------|-------------|-----------|
| P5 | Frequent | Expected to occur | >10⁻³ |
| P4 | Probable | Likely to occur | 10⁻³ to 10⁻⁴ |
| P3 | Occasional | May occur | 10⁻⁴ to 10⁻⁵ |
| P2 | Remote | Unlikely | 10⁻⁵ to 10⁻⁶ |
| P1 | Improbable | Very unlikely | <10⁻⁶ |

### Severity Criteria

| Level | Name | Description | Harm |
|-------|------|-------------|------|
| S5 | Catastrophic | Death | Death |
| S4 | Critical | Permanent impairment | Irreversible injury |
| S3 | Serious | Injury requiring intervention | Reversible injury |
| S2 | Minor | Temporary discomfort | No treatment needed |
| S1 | Negligible | Inconvenience | No injury |

See: [references/risk-analysis-methods.md](references/risk-analysis-methods.md)

---

## Risk Evaluation Workflow

Evaluate risks against acceptability criteria.

### Workflow: Evaluate Identified Risks

1. Calculate initial risk level from probability × severity
2. Compare to risk acceptability criteria
3. For each risk, determine:
   - Acceptable: Document and accept (EU MDR: still reduce as far as possible)
   - Reduction required (AFAP): Proceed to risk control
   - Unacceptable: Mandatory risk control
4. Document evaluation rationale
5. Identify risks requiring benefit-risk analysis
6. Complete benefit-risk analysis if applicable
7. Compile risk evaluation summary
8. **Validation:** All risks evaluated; acceptability determined; rationale documented

### Risk Evaluation Decision Tree

```
Risk Estimated
      │
      ▼
Apply Acceptability Criteria
      │
      ├── Low Risk ──────────► Accept and document
      │
      ├── Medium Risk ───────► Reduce as far as possible (AFAP)
      │   │                    Document why further reduction impossible
      │   ▼
      │   Further reduction possible?
      │   │
      │   Yes──► Implement control
      │   No───► Document AFAP rationale (no economic considerations)
      │
      ├── High Risk ─────────► Risk reduction required
      │   │                    Must demonstrate reduction AFAP
      │   ▼
      │   Implement control
      │   Verify residual risk
      │
      └── Unacceptable ──────► Design change mandatory
                               Cannot proceed without control
```

### AFAP Demonstration Requirements (EU MDR)

| Criterion | Evidence Required |
|-----------|-------------------|
| All control options considered | Analysis of every feasible control per the hierarchy (design, protective measures, information) |
| Further reduction impossible | Evidence each remaining option is technically infeasible or does not further reduce risk |
| State of the art | Comparison to similar devices and current standards |
| Stakeholder input | Clinical/user perspectives |

> Economic considerations (cost of further risk reduction) **must not** enter the EU acceptability decision (MDR Annex I GSPR 2; EN ISO 14971:2019/A11:2021). Cost may inform business decisions about whether to market the device — never whether a risk is acceptable.

### Benefit-Risk Analysis Triggers

| Situation | Benefit-Risk Required |
|-----------|----------------------|
| Residual risk remains high | Yes |
| No feasible risk reduction | Yes |
| Novel device | Yes |
| Unacceptable risk with clinical benefit | Yes |
| All risks low | No |

---

## Risk Control Workflow

Implement and verify risk control measures.

### Workflow: Implement Risk Controls

1. Identify risk control options:
   - Inherent safety by design (Priority 1)
   - Protective measures in device (Priority 2)
   - Information for safety (Priority 3)
2. Select optimal control following hierarchy
3. Analyze control for new hazards introduced
4. Document control in design requirements
5. Implement control in design
6. Develop verification protocol
7. Execute verification and document results
8. Evaluate residual risk with control in place
9. **Validation:** Control implemented; verification passed; residual risk acceptable; no unaddressed new hazards

### Risk Control Hierarchy

| Priority | Control Type | Examples | Effectiveness |
|----------|--------------|----------|---------------|
| 1 | Inherent Safety | Eliminate hazard, fail-safe design | Highest |
| 2 | Protective Measures | Guards, alarms, automatic shutdown | High |
| 3 | Information | Warnings, training, IFU | Lower |

### Risk Control Option Analysis Template

```
RISK CONTROL OPTION ANALYSIS

Hazard ID: H-[XXX]
Hazard: [Description]
Initial Risk: P[X] × S[X] = [Level]

OPTIONS CONSIDERED:
| Option | Control Type | New Hazards | Feasibility | Selected |
|--------|--------------|-------------|-------------|----------|
| 1 | [Type] | [Yes/No] | [H/M/L] | [Yes/No] |
| 2 | [Type] | [Yes/No] | [H/M/L] | [Yes/No] |

SELECTED CONTROL: Option [X]
Rationale: [Justification for selection]

IMPLEMENTATION:
- Requirement: [REQ-XXX]
- Design Document: [Reference]

VERIFICATION:
- Method: [Test/Analysis/Review]
- Protocol: [Reference]
- Acceptance Criteria: [Criteria]
```

### Risk Control Verification Methods

| Method | When to Use | Evidence |
|--------|-------------|----------|
| Test | Quantifiable performance | Test report |
| Inspection | Physical presence | Inspection record |
| Analysis | Design calculation | Analysis report |
| Review | Documentation check | Review record |

### Residual Risk Evaluation

| After Control | Action |
|---------------|--------|
| Acceptable | Document, proceed |
| Reduced AFAP | Document rationale (no economic considerations), proceed |
| Still unacceptable | Additional control or design change |
| New hazard introduced | Analyze and control new hazard |

---

## Post-Production Risk Management

Monitor and update risk management throughout product lifecycle.

### Workflow: Post-Production Risk Monitoring

1. Identify information sources:
   - Customer complaints
   - Service reports
   - Vigilance/adverse events
   - Literature monitoring
   - Clinical studies
2. Establish collection procedures
3. Define review triggers:
   - New hazard identified
   - Increased frequency of known hazard
   - Serious incident
   - Regulatory feedback
4. Analyze incoming information for risk relevance
5. Update risk management file as needed
6. Communicate significant findings
7. Conduct periodic risk management review
8. **Validation:** Information sources monitored; file current; reviews completed per schedule

### Information Sources

| Source | Information Type | Review Frequency |
|--------|------------------|------------------|
| Complaints | Use issues, failures | Continuous |
| Service | Field failures, repairs | Monthly |
| Vigilance | Serious incidents | Immediate |
| Literature | Similar device issues | Quarterly |
| Regulatory | Authority feedback | As received |
| Clinical | PMCF data | Per plan |

### Risk Management File Update Triggers

| Trigger | Response Time | Action |
|---------|---------------|--------|
| Serious incident | Immediate | Full risk review |
| New hazard identified | 30 days | Risk analysis update |
| Trend increase | 60 days | Trend analysis |
| Design change | Before implementation | Impact assessment |
| Standards update | Per transition period | Gap analysis |

### Periodic Review Requirements

| Review Element | Frequency |
|----------------|-----------|
| Risk management file completeness | Annual |
| Risk control effectiveness | Annual |
| Post-market information analysis | Quarterly |
| Risk-benefit conclusions | Annual or on new data |

---

## Risk Assessment Templates
→ See references/risk-assessment-templates.md for details

## Decision Frameworks

### Risk Control Selection

```
What is the risk level?
        │
        ├── Unacceptable ──► Can hazard be eliminated?
        │                    │
        │                Yes─┴─No
        │                 │     │
        │                 ▼     ▼
        │            Eliminate  Can protective
        │            hazard     measure reduce?
        │                           │
        │                       Yes─┴─No
        │                        │     │
        │                        ▼     ▼
        │                   Add       Add warning
        │                   protection + training
        │
        └── High/Medium ──► Apply hierarchy
                            starting at Level 1
```

### New Hazard Analysis

| Question | If Yes | If No |
|----------|--------|-------|
| Does control introduce new hazard? | Analyze new hazard | Proceed |
| Is new risk higher than original? | Reject control option | Acceptable trade-off |
| Can new hazard be controlled? | Add control | Reject control option |

### Risk Acceptability Decision

| Condition | Decision |
|-----------|----------|
| All risks Low | Acceptable |
| Medium risks reduced AFAP | Acceptable |
| High risks reduced AFAP, documented | Acceptable if benefits outweigh |
| Any Unacceptable residual | Not acceptable - redesign |

---

## Tools and References

### Scripts

| Tool | Purpose | Usage |
|------|---------|-------|
| [risk_matrix_calculator.py](scripts/risk_matrix_calculator.py) | Calculate risk levels and FMEA RPN | `python risk_matrix_calculator.py --help` |

**Risk Matrix Calculator Features:**
- ISO 14971 5x5 risk matrix calculation
- FMEA RPN (Risk Priority Number) calculation
- Interactive mode for guided assessment
- Display risk criteria definitions
- JSON output for integration

### References

| Document | Content |
|----------|---------|
| [iso14971-implementation-guide.md](references/iso14971-implementation-guide.md) | Complete ISO 14971:2019 implementation with templates |
| [risk-analysis-methods.md](references/risk-analysis-methods.md) | FMEA, FTA, HAZOP, Use Error Analysis methods |

### Quick Reference: ISO 14971 Process

| Stage | Key Activities | Output |
|-------|----------------|--------|
| Planning | Define scope, criteria, responsibilities | Risk Management Plan |
| Analysis | Identify hazards, estimate risk | Hazard Analysis |
| Evaluation | Compare to criteria, AFAP assessment (EU) | Risk Evaluation |
| Control | Implement hierarchy, verify | Risk Control Records |
| Residual | Overall assessment, benefit-risk | Risk Management Report |
| Production | Monitor, review, update | Updated RM File |

---

## Related Skills

| Skill | Integration Point |
|-------|-------------------|
| [quality-manager-qms-iso13485](../quality-manager-qms-iso13485/) | QMS integration |
| [capa-officer](../capa-officer/) | Risk-based CAPA |
| [regulatory-affairs-head](../regulatory-affairs-head/) | Regulatory submissions |
| [quality-documentation-manager](../quality-documentation-manager/) | Risk file management |
