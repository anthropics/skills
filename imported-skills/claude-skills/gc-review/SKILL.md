---
name: "gc-review"
description: "/cs:gc-review <plan> — General Counsel interrogation of contracts, IP, regulatory, term sheets, and employment-law surface. Use when reviewing a term sheet before signing, redlining a customer MSA, or checking IP assignment and regulatory exposure on a new product."
---

# /cs:gc-review — General Counsel Forcing Questions

**Command:** `/cs:gc-review <plan>`

The General Counsel lens. Six questions before any contract, term sheet, IP move, or regulatory commitment. This is a lane gstack has zero of — and one where a single missed clause costs more than a year of engineering.

> ⚠️ **Not legal advice.** This command surfaces the right questions to ask before talking to outside counsel. Always engage qualified counsel for binding decisions.

## When to Run

- Before signing any contract > $100K or > 1 year
- Before issuing equity (employee grants, advisor grants)
- Before a term sheet response
- Before entering a regulated market (healthcare, fintech, defense)
- Before any open-source license decision in core IP
- Before an M&A LOI

## The Six GC Questions

### 1. IP Ownership
**Who owns the IP being created or shared in this transaction?**
- Work-for-hire vs license vs joint.
- For employees and contractors: written IP assignment in place?
- For OSS: license compatibility checked?

### 2. Liability & Indemnity
**What's the liability cap, and what's carved out from it?**
- Standard cap: 12 months of fees.
- Carve-outs: IP infringement, data breach, willful misconduct.
- Mutual indemnity desirable.

### 3. Data Processing
**What personal data is involved, and is a DPA in place?**
- GDPR / CCPA scope?
- Subprocessor flow-down?
- Data residency requirements?

### 4. Termination & Renewal
**What's the termination right, what's the notice period, and what's auto-renew?**
- Termination for convenience vs cause.
- Notice period (30 / 60 / 90 days).
- Auto-renewal trap?

### 5. Regulatory Surface
**Does this expose the company to a new regulatory regime?**
- Healthcare → HIPAA.
- Fintech → BSA/AML, state money-transmitter.
- Medical device → FDA, MDR, ISO 13485.
- Data → GDPR, CCPA, state breach laws.

### 6. Employment / Equity
**If this is a hire or contractor: jurisdiction, classification, equity grant, IP assignment?**
- Misclassification risk?
- Equity vesting standard (4-year, 1-year cliff)?
- Acceleration triggers?
- 409A current?

## Workflow

1. Read the contract / term sheet end to end
2. Run the six questions
3. Identify the top-3 issues that need outside counsel review
4. Apply the verdict

## Output Format

```markdown
# GC Review: <plan>
**Date:** YYYY-MM-DD

## Document
- Type: <contract / term sheet / grant / DPA>
- Counterparty: <name>
- $ value or scope: <amount>

## Issues
| # | Issue | Risk | Recommendation |
|---|---|---|---|
| 1 | <e.g., uncapped IP indemnity> | HIGH | Cap at fees paid, mutual |
| 2 | <e.g., 5-year auto-renew> | MED | 1-year max, 60-day notice |
| 3 | <e.g., no DPA, EU data> | HIGH | Require DPA before sign |

## Regulatory Trigger
- New regime triggered? <yes/no>
- Specific frameworks: <HIPAA / GDPR / etc.>

## Outside Counsel Action Items
- [ ] <specific item 1>
- [ ] <specific item 2>
- [ ] <specific item 3>

## Verdict
🟢 SIGN AS-IS (rare)
🟡 NEGOTIATE — counter on top-3 issues
🔴 DO NOT SIGN — material risk
```

## Routing

- `/cs:ciso-review` — for any data-touching contract
- `/cs:cfo-review` — for any commitment > 1 year or > 1% of revenue
- `/cs:decide` — log the verdict after outside counsel review

## Workflow Integration with `general-counsel-advisor` skill

Since v2.5.1, this command is backed by a full skill at `../../../skills/general-counsel-advisor/` with two Python tools:

```bash
# Automated contract scan (12 founder-killer patterns)
python ../../../skills/general-counsel-advisor/scripts/contract_risk_scanner.py path/to/contract.txt

# Term sheet scoring (0-100 founder-friendliness)
python ../../../skills/general-counsel-advisor/scripts/term_sheet_analyzer.py path/to/term_sheet.json
```

The `cs-general-counsel-advisor` agent orchestrates both tools plus 3 references (contracts playbook, IP + regulatory, term sheet decoder).

## Related

- Skill: [`general-counsel-advisor`](../../../skills/general-counsel-advisor/SKILL.md) — full skill with Python tools + references
- Agent: [`cs-general-counsel-advisor`](../../agents/cs-general-counsel-advisor.md)
- Compliance execution: `../../../../ra-qm-team/`
- Adjacent: `../../../skills/ma-playbook/`

---

**Version:** 1.0.0
