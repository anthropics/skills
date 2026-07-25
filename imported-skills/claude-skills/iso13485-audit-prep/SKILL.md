---
name: "iso13485-audit-prep"
description: "/cs:iso13485-audit-prep <scope> — ISO 13485 QMS audit 6-question forcing interrogation. Design controls + CAPA + post-market focused. Use before Clause 8.2.4 internal audit, MDR / FDA QSR alignment review, or product-launch DHF closure audit."
---

# /cs:iso13485-audit-prep — ISO 13485 QMS Forcing Questions

**Command:** `/cs:iso13485-audit-prep <scope>`

The ISO 13485 QMS auditor pressure-tests any medical-device QMS work. Six traceability-obsessed questions before any internal audit, MDR / FDA QSR review, or product launch.

## When to Run

- Before annual Clause 8.2.4 internal audit
- Before MDR / FDA QSR alignment review (substantially harmonized post Feb 2026)
- Before new-device commercial launch (DHF closure audit)
- After significant CAPA closure event (effectiveness verification audit)
- Post-recall event (root cause + corrective action audit)
- Quarterly during regulatory submission preparation

## The Six QMS Questions

### 1. Pull three random DHFs. Are design verification + validation evidence complete?
**Most-cited finding area.**
- DHF must include: design plan + inputs + outputs + verification + validation + transfer + changes
- Sample stratified by product class (I, IIa, IIb, III per MDR)
- Reference `iso13485_audit_playbook.md` for the per-DHF checklist
- Verify traceability matrix from user needs through clinical evidence

### 2. Show me the last 5 CAPAs with effectiveness verification evidence.
**Second-most-cited finding area.**
- Containment / correction / corrective action distinction documented
- Root cause analysis depth: 5 Why minimum
- Effectiveness verification = measurable evidence, not "we updated the procedure"
- Closure approved by appropriate authority
- Repeat CAPAs across products = systemic issue trigger

### 3. When was process validation (IQ/OQ/PQ) last revalidated?
**Clause 7.5.6 — often stale.**
- Initial validation at process introduction
- Revalidation triggers: process change, equipment change, material change, periodic schedule
- Trend monitoring (SPC) where statistical techniques apply per Clause 8.4
- Cross-check with cs-fda-qsr-auditor for 21 CFR 820.75 alignment

### 4. Show me the risk management file for the highest-risk product.
**Clause 7.1 + ISO 14971:2019.**
- Risk management plan exists per product
- Hazard identification covers reasonable foreseeable misuse
- Risk control hierarchy applied: inherent safety > protective measures > information for safety
- Residual risk evaluated + accepted with rationale
- Post-production information feeds back into RMF
- For AI-enabled medical devices: layer ISO 42001 A.5 impact assessment on top

### 5. Show me post-market surveillance evidence — last 6 months.
**Clause 8.2.1 — high-stakes for MDR + FDA.**
- Customer complaint log + investigation closure
- Vigilance reports (serious incident / FSCA) submitted per applicable regulation
- Trend analysis evidence + management review input
- Post-market clinical follow-up (PMCF) for MDR high-risk devices
- MDR reports per 21 CFR 803 for US-marketed devices (cross-check with cs-fda-qsr-auditor)

### 6. Where's the management review evidence covering all Clause 5.6 inputs?
**Annual minimum; semi-annual for mature programs.**
- Required inputs per Clause 5.6.2: audit results, customer feedback, process performance, product conformity, status of preventive + corrective actions, follow-up from prior reviews, changes that could affect QMS, recommendations for improvement, regulatory requirements
- Outputs per Clause 5.6.3: improvement decisions, product requirement changes, resource needs
- Integrated review across frameworks (per `multi_framework_audit_playbook.md`) preferred

## Workflow

```bash
# 1. Audit programme optimization
python ra-qm-team/skills/qms-audit-expert/scripts/audit_schedule_optimizer.py audit_scope.json

# 2. Mock audit for readiness check
python ../../skills/compliance-os/scripts/audit_simulator.py iso13485_scope.json

# 3. CAPA system review
# Route to ra-qm-team/skills/capa-officer/ tools

# 4. Risk management file review
# Route to ra-qm-team/skills/risk-management-specialist/ tools
```

## Output Format

```markdown
# ISO 13485 Audit Prep: <scope>
**Date:** YYYY-MM-DD

## The Decision Being Made
[programme-plan | DHF-closure | CAPA-health | post-market-trend | pre-cert | MDR-FDA-alignment]

## Design Control Status (sampled DHFs)
- DHFs sampled: <list product IDs>
- Verification evidence: pass/fail per DHF
- Validation evidence: pass/fail per DHF
- Clinical evidence (per MDR Annex XIV / FDA 510(k)): pass/fail
- Traceability matrix complete: yes/no per DHF

## CAPA Health
- CAPAs sampled: N
- Root cause analysis depth: adequate/inadequate per CAPA
- Effectiveness verification: complete/incomplete per CAPA
- Aging CAPAs > 90 days: N
- Repeat issues across products: <list>

## Process Validation Status
- Validations on schedule: %
- Stale validations (> 12 months since revalidation): <list>
- Statistical techniques applied per Clause 8.4: yes/no

## Risk Management File Status
- Sampled product RMFs: <list>
- Post-production updates in last 12 months: <count per product>
- Residual risk acceptance signed: yes/no

## Post-Market Surveillance
- Complaint trending: stable/rising
- MDR / vigilance reports filed timely: %
- PMCF on schedule (where required): yes/no

## Management Review Status
- Last review date: YYYY-MM-DD
- Required Clause 5.6.2 inputs present: yes/no
- Open action items past due: N

## Cross-Framework Impact
- EU MDR alignment: clean / gaps in <list>
- FDA QSR alignment (post-Feb 2026): substantially harmonized; FDA-specific overlays per cs-fda-qsr-auditor
- ISO 42001 AIMS overlay (if AI-enabled device): pass/fail per Annex A

## Verdict
🟢 READY | 🟡 CLOSE-DHF-GAPS-FIRST | 🔴 NOT-READY

## Top 3 Actions
[3 concrete next steps with owner + corrective-action timeline]
```

## Routing

- `/cs:compliance-readiness` — for multi-framework view
- `/cs:fda-qsr-audit-prep` — for FDA-specific overlay
- `/cs:aims-audit` — for AI-enabled medical device ISO 42001 layer
- `/cs:gdpr-audit-prep` — for personal-data overlap (clinical data, customer data)
- `/cs:cpo-review` — for executive product strategy decisions
- `/cs:decide` — to log the verdict

## Related

- Agent: [`cs-cqm-iso13485`](../../agents/cs-cqm-iso13485.md)
- Skill: [`qms-audit-expert`](../../../ra-qm-team/skills/qms-audit-expert/SKILL.md)
- Playbook: [iso13485_audit_playbook.md](../../../ra-qm-team/skills/qms-audit-expert/references/iso13485_audit_playbook.md)
- Adjacent: `../fda-qsr-audit-prep/`, `../aims-audit/`, `../compliance-readiness/`

---

**Version:** 1.0.0
