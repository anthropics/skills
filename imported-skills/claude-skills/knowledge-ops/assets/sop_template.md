# SOP Template — fill out before running `sop_generator.py`

Use this template to capture the SOP metadata before invoking the generator.
Fill in the fields below, then translate them into the JSON skeleton at the
bottom of this file. Feed that JSON into the generator:

```
python3 scripts/sop_generator.py --input my-sop.json --profile ops
python3 scripts/sop_generator.py --input my-sop.json --profile regulated  # for SOX / HIPAA / ISO 13485 / FDA
```

---

## SOP metadata

- **SOP name:** _(e.g., Vendor Offboarding, Procurement Intake, Employee Onboarding, Customer Escalation, System Access Provisioning)_
- **Process owner (named human):** _(e.g., alex@company.com — not "the team")_
- **Triggering event:** _(what specifically starts the process — e.g., "Vendor contract not renewed OR vendor terminated for cause")_
- **Audience role:** _(who will execute this SOP — e.g., "Vendor Management Office operator", "HR onboarding specialist")_
- **Frequency:** _(how often this runs — "Daily", "Weekly Monday 9am", "On-demand avg 3x/quarter")_
- **Regulatory overlay:** _(zero or more of: SOC2, HIPAA, ISO13485, GDPR, SOX. If "none", confirm by listing data classes the process touches.)_

---

## Inputs and outputs

**Inputs required before starting:**

- _(input 1 — e.g., "Vendor legal name")_
- _(input 2 — e.g., "Contract end date")_
- _(input 3 — e.g., "List of systems with vendor access")_

**Outputs produced:**

- _(output 1 — e.g., "All production system access revoked, evidenced in IAM audit log")_
- _(output 2 — e.g., "Vendor data deletion certified")_
- _(output 3 — e.g., "Final invoice reconciled and paid")_

---

## Steps outline

Six rows to start; add or remove. **Each step must be a noun-phrase action**, not a paragraph.

| # | Step name (action) | Notes |
|---|--------------------|-------|
| 1 | _e.g., Notify vendor of offboarding intent (30 days written notice)_ | |
| 2 | _e.g., Inventory data classes and system access vendor holds_ | |
| 3 | _e.g., Revoke production system access (IAM, VPN, SaaS)_ | |
| 4 | _e.g., Confirm data deletion (vendor certification) or data return_ | |
| 5 | _e.g., Final invoice reconciliation and payment_ | |
| 6 | _e.g., Archive vendor record in VMO registry with offboarding evidence_ | |

---

## How-much (cost model)

- **Estimated execution time:** _(minutes per execution — e.g., 240)_
- **Estimated cost per execution:** _(USD, labor + license + third-party fees — e.g., 800)_

---

## JSON skeleton

```json
{
  "sop_name": "Vendor Offboarding",
  "process_owner": "alex@company.com (Vendor Management Lead)",
  "triggering_event": "Vendor contract not renewed OR vendor terminated for cause",
  "audience_role": "Vendor Management Office (VMO) operator",
  "frequency": "On-demand (avg 3 executions per quarter)",
  "regulatory_overlay": ["SOC2"],
  "inputs": [
    "Vendor legal name",
    "Contract end date",
    "List of systems with vendor access",
    "List of data classes vendor processed"
  ],
  "outputs": [
    "All production system access revoked (evidenced)",
    "Vendor data deleted or returned (evidenced)",
    "Final invoice reconciled and paid",
    "Vendor record archived in VMO registry with offboarding evidence"
  ],
  "steps_outline": [
    "Notify vendor of offboarding intent (written, 30 days notice)",
    "Inventory data classes and system access vendor holds",
    "Revoke production system access (IAM, VPN, SaaS)",
    "Confirm data deletion (vendor certification) or data return",
    "Final invoice reconciliation and payment",
    "Archive vendor record in VMO registry with offboarding evidence"
  ],
  "estimated_minutes": 240,
  "estimated_cost_usd": 800
}
```

---

## Authoring discipline checklist

Before submitting the JSON to the generator, confirm:

- [ ] **Owner is a named human**, not "the team" — required by Gawande *Checklist Manifesto* discipline.
- [ ] **Triggering event is specific.** "When needed" is not a trigger.
- [ ] **At least one regulatory overlay considered** (or explicit "none after checking PHI/financial/regulated-device classes").
- [ ] **Top-2 failure modes documented** — happy-path-only SOPs are responsible for 60%+ of incident-time waste (Fowler 2016).
- [ ] **"How-much" is filled in.** It's the section authors most often forget — and the section operators most need.
- [ ] **`--profile regulated` selected** if SOP touches SOX, HIPAA, ISO 13485, FDA 21 CFR Part 211, or SOC 2 controls.

After generation, run the runbook validator on any embedded step lists that include state-mutating operations:

```
python3 scripts/runbook_validator.py --input generated-sop.md
```
