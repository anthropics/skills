# AI Training Data Rights — The Decision: "Can we train on this data?"

This reference answers exactly one decision per data source: **may we use this for AI training, and for which use case?** It does so by combining three independent dimensions into a verdict.

Pair with `scripts/ai_training_data_audit.py` for automation. **Not legal advice.**

## The Three Dimensions

### Dimension 1: Origin

Where did this data come from, and what consent flow accompanied it?

| Origin | Strength | Notes |
|---|---|---|
| `1st-party-explicit-opt-in` | Strongest | User saw a notice for THIS purpose and clicked agree. GDPR Art. 6(1)(a). |
| `1st-party-tos-only` | Weak | Bundled TOS doesn't satisfy GDPR Art. 6 for materially different purposes (training). |
| `partner-licensed` | Depends | Only as strong as the partner's original consent flow + your license scope. |
| `scraped` | Insufficient | No lawful basis under GDPR Art. 6; potentially Computer Fraud and Abuse Act / copyright exposure. |
| `synthetic` | Strong | But synthetic data inherits risks from its seed source if any. |

### Dimension 2: Data Class

What's in the data?

| Class | Implication |
|---|---|
| `anonymous-aggregate` | Safest. K-anonymity ≥ 5 maintained. |
| `behavioral` | Usually safe with proper consent. Watch for re-identification. |
| `pii` | Highest scrutiny. Requires lawful basis + deletion-on-request handling. |
| `third-party-content` | User-uploaded files, snippets, transcripts that include external content. Copyright + DMCA exposure. |
| `regulated` | PHI, PCI, COPPA-children data, biometrics. Framework-specific consent required. |

### Dimension 3: Use Case

What are you doing with it?

| Use case | Risk profile |
|---|---|
| `in-product-personalization` | Lowest risk; recommended within-product. Performance of contract often covers this. |
| `fine-tune-our-model` | Medium risk. Specific opt-in usually needed for non-anonymous classes. |
| `train-foundation-model` | High risk. Re-identification + memorization concerns; almost never permissible for PII without specific consent. |
| `external-sharing` | Highest risk. Recipient becomes a data controller (GDPR Art. 26 / 28 analysis required). |

## The Verdict Matrix (excerpt — full logic in audit tool)

| Origin × Class × Use Case | Verdict |
|---|---|
| `scraped` × any × any | NO-GO (no exceptions for training) |
| `1st-party-tos-only` × `pii` × `fine-tune-our-model` | NO-GO (TOS insufficient for material purpose change) |
| `1st-party-explicit-opt-in` × `pii` × `in-product-personalization` | GO (strongest position) |
| `1st-party-tos-only` × `behavioral` × `fine-tune-our-model` | GO (with DPIA + deletion handling) |
| `partner-licensed` × `anonymous-aggregate` × `train-foundation-model` | GO (with license-scope review) |
| `synthetic` × `anonymous-aggregate` × `train-foundation-model` | GO (with provenance log) |
| any × `regulated` × `train-foundation-model` | NO-GO (framework prohibits raw use) |

Run `python scripts/ai_training_data_audit.py` for the full matrix applied to your sources.

## GDPR Art. 6 Lawful Basis Decision Tree (EU residents only)

If any EU resident data flows, GDPR applies. Pick exactly one lawful basis per purpose:

1. **Art. 6(1)(a) Consent.** The user said yes to THIS specific purpose. Most defensible. Must be granular, freely given, revocable.
2. **Art. 6(1)(b) Performance of contract.** Processing is necessary to deliver the service the user purchased. Works for in-product personalization within reasonable expectations.
3. **Art. 6(1)(c) Legal obligation.** You're required by law. Rare for training data.
4. **Art. 6(1)(d) Vital interests.** Life or death. Practically never applies to AI training.
5. **Art. 6(1)(e) Public interest.** Government / public mission. Rarely applies to private companies.
6. **Art. 6(1)(f) Legitimate interest.** Balancing test: your interest vs the user's rights. Requires Legitimate Interest Assessment (LIA). Defensible for fraud detection, security; weak for personalization beyond user expectations.

**Practical takeaway:** For training data outside in-product personalization, default to Art. 6(1)(a) explicit consent. Art. 6(1)(f) is increasingly disfavored by EU regulators for AI training (see EDPB Opinion 28/2024).

## EU AI Act High-Risk Triggers

The EU AI Act (in force 2026) imposes additional data governance requirements for high-risk AI systems. You are high-risk if your AI is used for:

- Biometric identification (other than verification)
- Critical infrastructure management
- Education access / scoring
- Employment / worker management (including hiring algorithms)
- Access to essential services (credit, insurance, public benefits)
- Law enforcement
- Migration / border control
- Administration of justice

If you are high-risk, **Art. 10 (data governance)** requires:
- Training-data quality criteria (representativeness, accuracy, completeness)
- Bias examination + mitigation
- Provenance documentation per source
- Pre-deployment conformity assessment

If you're low-risk (most B2B SaaS), the heavy obligations are GDPR-side, not AI-Act-side. But you still need provenance logs for Art. 53 (general-purpose models).

## US State Patchwork

| Law | What it covers |
|---|---|
| California CCPA / CPRA | Right to know, delete, opt-out of sale (incl. some training scenarios) |
| Colorado AI Act (CO SB 21-169 successor) | Bias audit requirements for AI in consumer decisions |
| New York City Local Law 144 | Bias audit required for AI in hiring (NYC employers) |
| Illinois BIPA | Biometric data requires explicit written consent |
| Texas TCPA | Capture-of-biometric-identifier rules |
| Washington My Health My Data Act | Consumer health data including inference |

## Practical Decision Pattern

For every new AI training initiative:

1. **List the data sources you plan to use** (be exhaustive — including "internal" ones)
2. **Tag each with origin × class × use case**
3. **Run `ai_training_data_audit.py`**
4. **For NO-GO:** Document the kill reason in the legal log. Either drop the source or change the use case.
5. **For MITIGATE:** Assign owner + remediation. Block training until complete.
6. **For GO:** Document the lawful basis and maintain the provenance log.
7. **Cross-check with cs-general-counsel-advisor** on top-3 mitigation items.
8. **Cross-check with cs-ciso-advisor** on data flow security.
9. **Log the decision via `/cs:decide`.**

## When This Reference Doesn't Help

- **Building synthetic data pipelines.** The synthetic data origin tag covers strategy, not generation; talk to engineering.
- **Differential privacy implementations.** Engineering territory. See `engineering/database-designer/` for guidance.
- **EU AI Act conformity assessments.** Requires a specialist; this reference identifies the trigger, not the remediation.
- **Class actions / litigation defense.** Outside counsel territory; this reference is preventive.

---

**Source authorities (non-exhaustive):**
- GDPR (Regulation (EU) 2016/679)
- EU AI Act (Regulation (EU) 2024/1689)
- EDPB Opinion 28/2024 on processing of personal data in AI models
- CCPA / CPRA (California Civil Code § 1798.100 et seq.)
- hiQ Labs, Inc. v. LinkedIn Corp., 938 F.3d 985 (9th Cir. 2019)
- NYT Co. v. OpenAI (filing, 2024, ongoing)
- Authors Guild v. Google, 804 F.3d 202 (2d Cir. 2015)
