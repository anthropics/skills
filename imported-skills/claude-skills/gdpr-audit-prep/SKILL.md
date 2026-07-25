---
name: "gdpr-audit-prep"
description: "/cs:gdpr-audit-prep <scope> — GDPR audit 6-question Article-cited forcing interrogation. Use before annual internal GDPR review, post-breach internal audit, DPA investigation readiness, or acquisition due diligence."
---

# /cs:gdpr-audit-prep — GDPR DPO Forcing Questions

**Command:** `/cs:gdpr-audit-prep <scope>`

The GDPR DPO auditor pressure-tests any privacy compliance work. Six Article-cited questions before any internal audit, breach response, DPA investigation, or acquisition due diligence.

## When to Run

- Before annual internal GDPR audit
- Before quarterly Article 30 RoPA refresh
- Before launching new high-risk processing (Article 35 DPIA required)
- Post-breach (Articles 33-34)
- Before DPA investigation response or supervisory authority engagement
- During acquisition due diligence (target company privacy posture)
- Quarterly during high-volume new-feature shipping

## The Six DPO Questions

### 1. Show me the Article 30 RoPA — with last-updated date.
**Most-cited finding area.**
- Must include all Article 30(1)(a)-(g) elements for controllers
- Must include all Article 30(2)(a)-(d) elements for processors
- Updated within reasonable time of changes (90 days expected)
- Joint controller arrangements documented per Article 26

### 2. For this processing activity, what's the lawful basis under Article 6?
**Article 6 is exclusive — pick ONE basis per purpose.**
- Six options: consent / contract / legal obligation / vital interests / public task / legitimate interests
- Where "legitimate interests": LIA documented
- Where "consent": records per Article 7; withdrawal mechanism
- Special categories (Article 9) require an Article 9(2) exception

### 3. For high-risk processing, where's the DPIA per Article 35?
**Required for high-risk; sample 3-5 activities.**
- Article 35(7)(a)-(d) required elements:
  - Systematic description of processing
  - Necessity + proportionality assessment
  - Risks to rights + freedoms
  - Measures to address risks
- DPO consulted per Article 35(2)
- Article 36 prior consultation triggered for residual high risk
- For AI systems: integrates with EU AI Act Article 27 FRIA (cross-check with cs-ai-act-compliance)

### 4. Show me a DSAR from the last 30 days — and the response timing.
**Articles 15-22 operational workflow.**
- Response within 1 month (Article 12(3)); extension up to 2 months for complex requests
- Identity verification process documented
- Right of access response includes all Article 15 information
- Right to erasure (Article 17) workflow covers backups + processors

### 5. Show me Transfer Impact Assessments for the largest non-EU transfers.
**Schrems II discipline.**
- Adequacy decision OR SCCs (Article 46) OR derogation (Article 49)
- TIA per EDPB Recommendations 01/2020 + 02/2020
- Supplementary measures where TIA flagged risk
- US transfers covered by EU-US Data Privacy Framework adequacy (Jul 2023) — verify list of certified entities

### 6. Show me the breach log per Article 33(5) — all breaches, not just notifiable ones.
**Article 33(5) requires logging ALL breaches.**
- Internal breach detection mechanism documented
- Article 33 DPA notification within 72 hours (where required)
- Article 34 data subject notification (where high risk)
- Root cause + corrective action via CAPA system
- Cross-check with cs-ciso-iso27001 for A.5.24-27 incident management alignment

## Workflow

```bash
# 1. Compliance posture
python ra-qm-team/skills/gdpr-dsgvo-expert/scripts/gdpr_compliance_checker.py compliance_state.json

# 2. DPIA for high-risk activities
python ra-qm-team/skills/gdpr-dsgvo-expert/scripts/dpia_generator.py processing_activity.json

# 3. DSAR workflow validation
python ra-qm-team/skills/gdpr-dsgvo-expert/scripts/data_subject_rights_tracker.py dsar_log.json

# 4. Cross-framework reuse with ISO 27001 + SOC 2 + ISO 42001
python ../../skills/compliance-os/scripts/cross_framework_mapper.py program.json
```

## Output Format

```markdown
# GDPR Audit Prep: <scope>
**Date:** YYYY-MM-DD
**Article Citations:** Every finding cites Article + paragraph; no paraphrase.

## The Decision Being Made
[RoPA-refresh | DPIA-required | DSAR-workflow | transfer-risk | breach-followup | DPA-readiness]

## Article 30 RoPA Status
- Last refresh: YYYY-MM-DD
- Required elements present: yes/no per processing activity
- Joint controller arrangements: documented/missing

## Article 6 Lawful Basis Discipline
- Activities reviewed: N
- Legitimate-interests claims without LIA: <list>
- Article 9 special categories with documented exception: yes/no

## Article 35 DPIA Quality
- High-risk activities requiring DPIA: <list>
- DPIAs complete per Article 35(7): pass/fail per activity
- Article 36 prior consultation triggered: <list>

## Data Subject Rights (Articles 12-22)
- DSARs in last 90 days: N
- Average response time: X days (target: ≤ 30)
- Right to erasure backup-processor flow: complete/incomplete

## Article 28 Processor Management
- Processors reviewed: N
- Contracts with all Article 28(3)(a)-(j) clauses: % complete
- Sub-processor flow-down notification mechanism: yes/no

## Schrems II Transfer Status
- Non-EU transfers: <list>
- Mechanism per transfer: adequacy / SCCs / derogation
- TIA on file: yes/no per transfer
- Supplementary measures where needed: <list>

## Article 33-34 Breach Discipline
- Breach log last 12 months: N
- Article 33 notification timing: ≤ 72h ratio
- Article 34 data subject notification (where high risk): on-time ratio

## Cross-Framework Impact
- ISO 27001 Article 32 alignment: clean / gaps
- EU AI Act Article 27 FRIA integration: applicable / not
- SOC 2 Privacy TSC alignment (if scope): clean / gaps

## Verdict
🟢 DPA-READY | 🟡 GAPS-IDENTIFIED | 🔴 NOT-READY

## Top 3 Actions
[3 concrete next steps with owner + Article-cited timeline]

## Outside Counsel Required
[Article-level ambiguities flagged: Schrems II supplementary measure adequacy, EU AI Act ↔ GDPR interaction, sectoral derogation interpretation, novel DPA enforcement]
```

## Routing

- `/cs:compliance-readiness` — for multi-framework view
- `/cs:iso27001-audit-prep` — for Article 32 organizational measures
- `/cs:ai-act-readiness` — for EU AI Act Article 27 FRIA integration
- `/cs:soc2-audit-prep` — for SOC 2 Privacy TSC overlap
- `/cs:gc-review` — for novel-case legal review

## Related

- Agent: [`cs-dpo-gdpr`](../../agents/cs-dpo-gdpr.md)
- Skill: [`gdpr-dsgvo-expert`](../../../ra-qm-team/skills/gdpr-dsgvo-expert/SKILL.md)
- Playbook: [gdpr_audit_playbook.md](../../../ra-qm-team/skills/gdpr-dsgvo-expert/references/gdpr_audit_playbook.md)
- Adjacent: `../iso27001-audit-prep/`, `../ai-act-readiness/`, `../soc2-audit-prep/`, `../compliance-readiness/`

---

**Version:** 1.0.0
