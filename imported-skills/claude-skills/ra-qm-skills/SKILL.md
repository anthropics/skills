---
name: "ra-qm-skills"
description: "Router/index for the 15 regulatory & quality-management skills bundled in this plugin (ISO 13485 QMS, EU MDR 2017/745, FDA submissions under QMSR, ISO 14971 risk, CAPA, document control, ISO 27001/ISMS, ISO 42001 AIMS, EU AI Act, GDPR/DSGVO, SOC 2, auditing). Use when a compliance request doesn't obviously match one skill and you need to pick the right one (e.g., 'prepare us for an ISO 13485 audit', 'is my AI system high-risk under the AI Act')."
version: 2.9.0
author: Alireza Rezvani
license: MIT
tags:
  - regulatory
  - quality-management
  - iso-13485
  - mdr
  - fda
  - iso-27001
  - gdpr
agents:
  - claude-code
  - codex-cli
  - openclaw
---

# Regulatory Affairs & Quality Management Skills — Router

This plugin bundles **15 compliance skills** for HealthTech/MedTech organizations (this router is the 16th folder under `ra-qm-team/skills/`). Each skill is self-contained.

## Routing table

Match the request, then load `ra-qm-team/skills/<skill>/SKILL.md`. If multiple rows match, ask one clarifying question first.

| Request signals | Skill | Path |
|---|---|---|
| Regulatory strategy, pathway selection, submissions planning | regulatory-affairs-head | `skills/regulatory-affairs-head/` |
| Management review, quality KPIs, QMR governance | quality-manager-qmr | `skills/quality-manager-qmr/` |
| ISO 13485 QMS implementation, process control | quality-manager-qms-iso13485 | `skills/quality-manager-qms-iso13485/` |
| ISO 14971 risk analysis, FMEA, risk files | risk-management-specialist | `skills/risk-management-specialist/` |
| Root cause analysis, corrective/preventive actions | capa-officer | `skills/capa-officer/` |
| Document control, 21 CFR Part 11, DHF/DMR/DHR | quality-documentation-manager | `skills/quality-documentation-manager/` |
| ISO 13485 internal audits, NC classification | qms-audit-expert | `skills/qms-audit-expert/` |
| ISO 27001 audit planning and execution | isms-audit-expert | `skills/isms-audit-expert/` |
| ISMS design, security risk assessment | information-security-manager-iso27001 | `skills/information-security-manager-iso27001/` |
| EU MDR classification, technical files, PSUR | mdr-745-specialist | `skills/mdr-745-specialist/` |
| FDA 510(k)/PMA/De Novo, QMSR | fda-consultant-specialist | `skills/fda-consultant-specialist/` |
| GDPR/DSGVO, DPIA, data subject rights | gdpr-dsgvo-expert | `skills/gdpr-dsgvo-expert/` |
| EU AI Act risk classification, obligations | eu-ai-act-specialist | `skills/eu-ai-act-specialist/` |
| ISO/IEC 42001 AI management system | iso42001-specialist | `skills/iso42001-specialist/` |
| SOC 2 Type I/II readiness, trust criteria | soc2-compliance | `skills/soc2-compliance/` |

## Quick start

```bash
# Example: route a risk-analysis request
cat ra-qm-team/skills/risk-management-specialist/SKILL.md
python3 ra-qm-team/skills/risk-management-specialist/scripts/risk_matrix_calculator.py --help
```

## Rules

- Route to exactly one skill, then follow that skill's workflow. This router ships no tools of its own.
- All outputs are decision support: final compliance determinations route to the named human owner (QMR, DPO, regulatory counsel) — never auto-decide.
- Verify regulatory citations against the current text (e.g., FDA QMSR effective 2026-02-02 replaced the legacy QSR subsections).
