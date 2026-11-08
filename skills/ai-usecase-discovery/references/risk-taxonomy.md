# Risk Taxonomy for AI Use Cases

## Risk Classification Framework

Every use case should be assessed across four risk axes.

---

### Axis 1: Consequence Severity

| Level | Description | Examples |
|---|---|---|
| **Critical** | Physical harm, loss of life, major legal liability | Medical diagnosis AI, autonomous vehicle control, safety-critical industrial systems |
| **High** | Significant financial harm, major discrimination risk, irreversible impact | Credit decisions, hiring decisions, insurance underwriting, fraud flags |
| **Moderate** | Financial loss, user frustration, reputational damage | Incorrect product recommendations, billing errors, misdirected support |
| **Low** | Minor UX degradation, recoverable errors | Typo suggestions, content tagging, search ranking |
| **Negligible** | No meaningful harm possible | Internal analytics, A/B test allocation, internal dashboards |

---

### Axis 2: Detectability

Can users or operators detect when the AI is wrong?

| Level | Description |
|---|---|
| **Invisible** | AI output is acted on without human review. Errors go unnoticed until downstream harm occurs. |
| **Partially visible** | Outputs are visible but users may not question them. Trust leads to uncritical acceptance. |
| **Visible** | Users can see and assess AI output before acting. Errors are often caught. |
| **Reviewed** | Human-in-the-loop before action. Near-certain error detection. |

---

### Axis 3: Regulatory Exposure

| Regulation | Trigger Conditions | Implication |
|---|---|---|
| **EU AI Act** | "High-risk" use cases: biometric ID, critical infra, education, employment, credit, law enforcement, healthcare | Mandatory conformity assessment, human oversight, transparency |
| **GDPR / DPDP** | Processing EU/Indian personal data for AI training or profiling | Consent requirements, right to explanation, data minimization |
| **HIPAA** | Any PHI used in training or inference in the US | BAA required with AI vendors, strict data handling |
| **CCPA** | CA consumer data used for AI training | Opt-out rights, disclosure requirements |
| **FCRA / Equal Credit** | Credit scoring or financial decisioning | Adverse action notices, bias testing requirements |
| **EEOC / Hiring Laws** | AI used in screening or ranking candidates | Disparate impact analysis required |
| **RBI / SEBI (India)** | AI in financial products, lending, investment advice | Algorithmic accountability, audit trail |
| **FDA SaMD** | AI/ML in medical software for diagnosis or treatment | Premarket review pathway required |

---

### Axis 4: Reversibility

| Level | Description | Examples |
|---|---|---|
| **Irreversible** | Action cannot be undone once AI output is acted on | Loan denial, account suspension, content removal |
| **Costly to reverse** | Reversible but expensive or reputationally damaging | Incorrect fulfillment, wrong pricing applied at scale |
| **Reversible** | Can be corrected with reasonable effort | Incorrect tag, wrong recommendation, misclassified ticket |
| **Self-correcting** | System naturally corrects over time | Search ranking, feed personalization |

---

## Risk Score Matrix

Combine the four axes to classify overall risk:

| Consequence | Detectability | Regulatory | Reversibility | Risk Level |
|---|---|---|---|---|
| Critical / High | Invisible | Regulated | Irreversible | 🔴 CRITICAL |
| High | Partially visible | Regulated | Costly to reverse | 🔴 HIGH |
| Moderate | Visible | Some regulation | Reversible | 🟡 MODERATE |
| Low | Reviewed | Minimal | Reversible | 🟢 LOW |
| Negligible | Any | None | Self-correcting | 🟢 NEGLIGIBLE |

---

## Mitigation Patterns by Risk Level

**🔴 CRITICAL / HIGH**
- Mandatory human-in-the-loop before any consequential action
- Full audit trail of all AI decisions
- Explainability requirement (can the AI explain why?)
- Bias testing before deployment
- Legal/compliance review before launch
- Consider whether AI should be used at all

**🟡 MODERATE**
- Human review for low-confidence outputs (confidence threshold routing)
- Monitoring dashboard with drift detection
- Clear user disclosure that AI is involved
- Feedback mechanism for users to flag errors
- Gradual rollout with holdout group

**🟢 LOW / NEGLIGIBLE**
- Standard monitoring
- A/B test to validate improvement
- Logging for debugging
- No special safeguards required beyond good engineering practice