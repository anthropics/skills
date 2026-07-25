---
name: "compliance-readiness"
description: "/cs:compliance-readiness <program> — Multi-framework compliance officer 6-question forcing interrogation of any compliance program. Use before starting a new framework, planning the annual audit calendar, or preparing for certification stage 1."
---

# /cs:compliance-readiness — Compliance Officer Forcing Questions

**Command:** `/cs:compliance-readiness <program>`

The multi-framework compliance officer pressure-tests any compliance program. Six questions before any new-framework commitment, audit cycle planning, or certification readiness sign-off.

## When to Run

- Before adopting a new compliance framework
- Before annual audit calendar finalization
- Before certification stage 1 readiness sign-off
- Before management review (Clause 9.3 across frameworks)
- When evidence-collection effort has grown 50%+ year-over-year (a smell)
- When an audit produced > 15% critical findings

## The Six Compliance Officer Questions

### 1. Have you named every applicable framework?
**No framework selector run, no defensible scope.**
- Run `framework_selector.py` with company profile
- Forgetting a framework means rebuilding the audit program later
- Pay attention to industry-specific overlays (financial: NYDFS, FINMA; healthcare: HIPAA, ISO 13485; AI: ISO 42001 + EU AI Act)

### 2. Where do the frameworks overlap, and what's the reuse leverage?
**Single evidence -> N controls = the cornerstone of multi-framework efficiency.**
- Run `cross_framework_mapper.py` with enabled frameworks
- HIGH-confidence mappings: same evidence; MEDIUM: existing + overlay; LOW: new artefact
- Without overlap analysis, you'll collect the same access-review records 3 times

### 3. Who owns each artefact, and what's the reuse-leverage score?
**Joint ownership without accountability is the most common cause of stale evidence.**
- Run `evidence_pool_generator.py` for the artefact inventory
- HIGH-leverage artefacts (≥ 5 mappings) get built first
- Each artefact needs one accountable owner
- Stale evidence is an effective gap — even if the artefact existed historically

### 4. What's the audit calendar, and is auditor independence respected?
**Surveillance audits stacking in the same week is a smell.**
- Use per-framework audit-plan tools (aims_audit_scheduler, isms_audit_scheduler, audit_schedule_optimizer)
- Auditor cannot audit their own work (Clause 9.2 across all ISO standards)
- For small teams: rotate auditors + occasional external auditor

### 5. What does a mock audit produce, and is the severity distribution healthy?
**No mock audit, no readiness signal.**
- Run `audit_simulator.py` with framework + scope
- Healthy distribution: ≥ 40% observation, ≤ 15% critical
- All-critical findings = destructive audit OR genuinely failing program
- All-observation findings = audit too superficial

### 6. What's the management review cadence across frameworks?
**Each framework wants its own management review; an integrated review (per Annex SL) saves 5x exec time.**
- Schedule one quarterly cross-framework review covering all enabled frameworks' Clause 9.3 inputs
- Inputs: risk register changes, open nonconformities, audit findings, incidents, drift, KPIs
- Outputs: action items, resource decisions, scope adjustments

## Workflow

```bash
# 1. Framework selection
python ../../skills/compliance-os/scripts/framework_selector.py profile.json

# 2. Cross-framework overlap
python ../../skills/compliance-os/scripts/cross_framework_mapper.py program.json

# 3. Evidence pool consolidation
python ../../skills/compliance-os/scripts/evidence_pool_generator.py program.json

# 4. Mock audit (per framework)
python ../../skills/compliance-os/scripts/audit_simulator.py scope.json
```

## Output Format

```markdown
# Compliance Readiness: <program>
**Date:** YYYY-MM-DD

## The Decision Being Made
[framework-set | audit-calendar | certification-readiness | evidence-consolidation]

## Framework Set
- Applicable: <list>
- Binding (regulations): <count>
- Certifiable: <count>
- Missing dependencies: <list>

## Cross-Framework Overlap
- Total merged controls in scope: N
- High-leverage artefacts (≥ 5 mappings): M
- Top reuse opportunities: <top 5 artefacts>

## Evidence Pool
- Artefacts in catalog: N
- High-leverage count: M
- Stale evidence rate: X%
- Unowned artefacts: K

## Audit Calendar
- Frameworks scheduled this year: <list>
- Auditor independence respected: Y/N
- Conflicts: <list>

## Mock Audit Results (per framework)
- <framework>: total findings N, critical X%, observation Y%, healthy distribution: Y/N

## Verdict
🟢 READY | 🟡 STAGE-2-CANDIDATE | 🔴 NOT-READY

## Top 3 Actions
[3 concrete next steps with owners + dates]
```

## Routing

- `/cs:aims-audit` — for ISO 42001-specific forcing questions
- `/cs:ai-act-readiness` — for EU AI Act-specific forcing questions
- `/cs:ciso-review` — for cybersecurity strategy
- `/cs:caio-review` — for executive AI strategy
- `/cs:gc-review` — for novel-case legal review
- `/cs:decide` — to log the verdict
- `/cs:freeze 30` — on certification commitments (multi-year financial impact)

## Related

- Agent: [`cs-compliance-officer`](../../agents/cs-compliance-officer.md)
- Skill: [`compliance-os`](../compliance-os/SKILL.md)
- Adjacent: `ra-qm-team/skills/iso42001-specialist/`, `ra-qm-team/skills/eu-ai-act-specialist/`, `ra-qm-team/skills/information-security-manager-iso27001/`, `ra-qm-team/skills/soc2-compliance/`, `ra-qm-team/skills/gdpr-dsgvo-expert/`

---

**Version:** 1.0.0
