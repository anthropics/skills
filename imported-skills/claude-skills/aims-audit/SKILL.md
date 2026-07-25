---
name: "aims-audit"
description: "/cs:aims-audit <scope> — ISO/IEC 42001 AIMS internal-audit 6-question forcing interrogation. Use before certification stage 1, before annual internal audit cycles, or when onboarding a new AI system into an existing AIMS."
---

# /cs:aims-audit — AIMS ISO 42001 Forcing Questions

**Command:** `/cs:aims-audit <scope>`

The ISO 42001 AIMS specialist pressure-tests any AI Management System work. Six questions before any certification commitment, internal audit cycle, or new-system onboarding.

## When to Run

- Before stage 1 ISO 42001 certification audit
- Before annual internal audit cycle (Clause 9.2)
- When onboarding a new AI system into existing AIMS scope
- When AI risk register hasn't been refreshed in > 6 months
- After material model change (re-evaluate risks per Clause 6.1.2)
- When audit findings hint at AIMS / ISMS / QMS duplication

## The Six AIMS Questions

### 1. Does the AIMS scope statement name every AI system?
**Scope omission = certification finding.**
- Including: embedded models, third-party AI services, "experimental" production systems
- Run `aims_gap_analyzer.py` to verify Clause 4.3 evidence
- "AI features added by SaaS vendors we use" = in scope if they affect the company's services

### 2. Does the AI policy commit to lawful use AND beneficial purpose AND human oversight AND continual improvement?
**Missing any of the four = critical nonconformity at stage 1.**
- AI policy is NOT info-sec policy — it has separate substantive content
- Reference ISO 42001 Annex A.2.2 + Clause 5.2
- Marketing-copy "AI ethics" doesn't pass

### 3. What's the risk register coverage, and which Annex A controls treat each risk?
**Risk identification without control mapping = Clause 6.1.3 fails.**
- Run `ai_risk_register_builder.py` per ISO 23894 methodology
- Every high/critical risk must link to ≥ 1 Annex A control
- "Residual verdict: additional_treatment_required" must be closed before stage 1

### 4. Has the AI risk assessment been re-run since the last material model change?
**Concept drift is not a one-time event.**
- Article 9 EU AI Act + ISO 42001 Clause 6.1.2 both require iterative risk assessment
- Material change = retraining on new data, fine-tuning, architecture change, deployment context change
- If "we did it 18 months ago and haven't touched it," the AIMS is broken

### 5. What's the Clause 9.2 internal audit plan, and is auditor independence respected?
**Without 9.2 plan, the AIMS is incomplete.**
- Run `aims_audit_scheduler.py` with scope + auditors + prior findings
- Audit every clause + applicable Annex A control over rolling 3-year cycle
- Same auditor cannot audit own work
- Cross-check with cs-quality-regulatory if integrated with 13485 audit programme

### 6. Has the AIMS been integrated with existing ISMS / QMS, or built in parallel?
**Parallel systems = 5x ongoing maintenance cost.**
- 60% of Clauses 4-10 evidence reuses ISO 27001 / 13485 with AI scope appended
- CAPA loop should be ONE loop with AI-tagged nonconformities, not separate
- Reference `cross_framework_mapping_ai.md` for the reuse map
- Cross-check with cs-ciso-advisor on ISO 27001 alignment

## Workflow

```bash
# 1. AIMS gap analysis
python ra-qm-team/skills/iso42001-specialist/scripts/aims_gap_analyzer.py evidence.json

# 2. AI risk register
python ra-qm-team/skills/iso42001-specialist/scripts/ai_risk_register_builder.py risks.json

# 3. Internal audit plan
python ra-qm-team/skills/iso42001-specialist/scripts/aims_audit_scheduler.py audit_scope.json

# 4. Cross-framework reuse map (via compliance-os)
python ../../skills/compliance-os/scripts/cross_framework_mapper.py program.json
```

## Output Format

```markdown
# AIMS Audit: <scope>
**Date:** YYYY-MM-DD

## The Decision Being Made
[gap-closure | risk-treatment | audit-scope | new-system-onboarding]

## Gap Analysis (Clauses 4-10)
- Weighted coverage: X%
- Critical gaps: N
- Major gaps: M
- Certification readiness: ready | stage_2_candidate | not_ready

## AI Risk Register
- Total risks: N
- By severity: critical=X, high=Y, medium=Z, low=W
- Requires additional treatment: K
- Top risk requiring action: <description>

## Clause 9.2 Audit Plan
- 12-month coverage: clauses=X, controls=Y
- Auditor independence: clean | issues
- Prior-year follow-up: scheduled in Q1

## Cross-Framework Reuse
- ISO 27001 evidence reused: % of AIMS Clauses 4-10
- 13485 evidence reused: % (if applicable)
- Net-new for AIMS: % (mostly Annex A)

## Verdict
🟢 STAGE-1-READY | 🟡 CLOSE-CRITICALS-FIRST | 🔴 NOT-READY

## Top 3 Actions
[3 concrete next steps with owner + date]
```

## Routing

- `/cs:compliance-readiness` — for multi-framework view
- `/cs:ai-act-readiness` — if EU AI Act also applies
- `/cs:caio-review` — for executive AI strategy decisions
- `/cs:ciso-review` — for ISO 27001 cross-framework alignment
- `/cs:decide` — to log the verdict
- `/cs:freeze 30` — on certification commitments

## Related

- Agent: [`cs-aims-iso42001`](../../agents/cs-aims-iso42001.md)
- Skill: [`iso42001-specialist`](../../../ra-qm-team/skills/iso42001-specialist/SKILL.md)
- Adjacent: `../../skills/compliance-os/`, `../ai-act-readiness/`, `../compliance-readiness/`

---

**Version:** 1.0.0
