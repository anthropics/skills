---
name: "soc2-audit-prep"
description: "/cs:soc2-audit-prep <scope> — SOC 2 Type II readiness 6-question forcing interrogation. Observation-period focused. Use before Type II observation begins, mid-period checkpoint, or pre-field-test month-10 readiness."
---

# /cs:soc2-audit-prep — SOC 2 Type II Forcing Questions

**Command:** `/cs:soc2-audit-prep <scope>`

The SOC 2 Type II auditor pressure-tests any SOC 2 work. Six observation-period-disciplined questions before any Type II cycle.

## When to Run

- Pre-observation period (months 1-2 of cycle)
- Mid-observation period (month 6 checkpoint)
- Pre-field-test (month 10)
- Post-report (planning next cycle)
- After scope change (adding TSC category)
- After major incident during observation period

## The Six SOC 2 Type II Questions

### 1. What's the scope, and which TSC categories are in?
**Security always required; others elective based on customer ask.**
- Common Criteria (CC1-CC9) under Security always
- Availability (A1): for SaaS with SLA commitments
- Processing Integrity (PI1): for systems processing transactional / financial data
- Confidentiality (C1): for systems handling proprietary / confidential data
- Privacy (P1-P8): for systems handling personal data (overlap with GDPR if applicable)
- AICPA AT-C 205 description of system: complete + accurate + boundaries clear

### 2. Did any control skip a cycle during observation period?
**Type II requires consistent operation — single skipped cycle = likely exception.**
- Quarterly controls (e.g., access reviews): all 4 quarters covered
- Monthly controls (e.g., vulnerability scans): all months covered
- Continuous controls (e.g., logging): no gaps during period
- Annual controls (e.g., BCP exercises, training): completed within period

### 3. Show me the change-management evidence for any control implemented mid-period.
**Mid-period changes = high audit risk.**
- New controls implemented during observation: documented with change-management
- Modified controls: rationale + effective date + impact on prior samples
- Removed controls: rationale + customer impact assessment
- Strategy: avoid mid-period changes; defer to next cycle

### 4. Where's the exception log, and what's the materiality assessment?
**Real-time exception logging — not retroactive.**
- Each exception logged when discovered, not at audit time
- Per exception: what / when / impact / remediation / owner
- Materiality assessment: does the exception affect overall control operation?
- Audit firm threshold: typically 1-2 exceptions per control acceptable; 3+ = finding

### 5. Show me sample evidence from each TSC criterion in the FIRST month of observation.
**Not the last week — the first month.**
- Audit firm samples across the observation period
- Front-loaded evidence demonstrates operational discipline
- Back-loaded evidence (last 30 days) = "scrambling" signal
- Sample IDs should be reproducible from operational systems

### 6. What's the cross-walk to ISO 27001, and which evidence reuses?
**75% control overlap — the canonical pair.**
- Run `cross_framework_mapper.py` for HIGH-confidence overlap themes
- Each shared artefact cited by both audits (one collection, two reports)
- Coordinate audit calendar with cs-ciso-iso27001
- Avoid producing duplicate evidence files for same control

## Workflow

```bash
# 1. Scoping + gap analysis (pre-observation)
python ra-qm-team/skills/soc2-compliance/scripts/gap_analyzer.py current_state.json

# 2. Control matrix with ISO 27001 cross-walk
python ra-qm-team/skills/soc2-compliance/scripts/control_matrix_builder.py program.json

# 3. Continuous evidence tracking (during observation)
python ra-qm-team/skills/soc2-compliance/scripts/evidence_tracker.py evidence_log.json

# 4. Mock audit (pre-field-test month 10)
python ../../skills/compliance-os/scripts/audit_simulator.py soc2_scope.json
```

## Output Format

```markdown
# SOC 2 Type II Audit Prep: <scope>
**Date:** YYYY-MM-DD
**Observation Period:** YYYY-MM-DD to YYYY-MM-DD

## The Decision Being Made
[scoping | pre-observation | observation-status | pre-field | report-response]

## TSC Scope
- Security: included
- Availability: <yes/no>
- Processing Integrity: <yes/no>
- Confidentiality: <yes/no>
- Privacy: <yes/no>

## Observation Period Status
- Months elapsed: N / 12
- Controls operated consistently: % of total
- Cycle skips identified: <list>
- Mid-period control changes: N (each documented with change-mgmt: yes/no)

## Exception Log
- Total exceptions logged: N
- Per-control max exceptions: M (audit firm tolerance: typically 1-2)
- Material exceptions (overall control affected): <list>
- Remediation status per exception: complete/in-progress

## Sample Evidence Coverage
- Month 1-3 evidence: complete/gaps
- Month 4-6 evidence: complete/gaps
- Month 7-9 evidence: complete/gaps
- Month 10-12 evidence: complete/gaps (only for pre-report status)

## ISO 27001 Cross-Walk Reuse
- HIGH-confidence overlap themes: N
- Shared artefacts in evidence pool: <count>
- Duplicate evidence collection avoided: % savings

## Audit Firm Readiness
- Scoping discussion: complete/pending
- Description of system per AT-C 205: complete/pending
- Walkthrough rehearsal: complete/pending
- Sample preparation: complete/pending

## Verdict
🟢 ON-TRACK | 🟡 NEEDS-ATTENTION | 🔴 MATERIAL-RISK

## Top 3 Actions
[3 concrete next steps with owner + observation-period timing]
```

## Routing

- `/cs:compliance-readiness` — for multi-framework view
- `/cs:iso27001-audit-prep` — for ISO 27001 cross-walk pair (75% overlap)
- `/cs:gdpr-audit-prep` — for Privacy TSC overlap
- `/cs:ciso-review` — for executive cybersecurity strategy

## Related

- Agent: [`cs-soc2-auditor`](../../agents/cs-soc2-auditor.md)
- Skill: [`soc2-compliance`](../../../ra-qm-team/skills/soc2-compliance/SKILL.md)
- Playbook: [soc2_audit_playbook.md](../../../ra-qm-team/skills/soc2-compliance/references/soc2_audit_playbook.md)
- Adjacent: `../iso27001-audit-prep/`, `../gdpr-audit-prep/`, `../compliance-readiness/`

---

**Version:** 1.0.0
