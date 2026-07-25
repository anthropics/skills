---
name: "c-level-skills"
description: "Index and router for the C-level advisory bundle: 33 skills covering 14 C-suite roles, orchestration, cross-cutting capabilities, and culture. Use when exploring what the c-level-advisor bundle contains, deciding which advisor skill fits a question, or finding the entry points (cs-onboard interview, chief-of-staff routing, board-meeting protocol)."
license: MIT
metadata:
  version: 2.1.0
  author: Alireza Rezvani
  category: c-level
  domain: executive-advisory
  updated: 2026-06-11
  skills_count: 33
  scripts_count: 37
  references_count: 68
---

# C-Level Advisory Bundle — Index

This is the bundle index, not an advisor. It tells you what exists and where to start; the skills below do the work.

## Start Here

1. **Onboard** — the `cs-onboard` skill runs the founder interview (`/cs:setup`, 7 dimensions, ~45 min) and writes `~/.claude/company-context.md`. Refresh quarterly with `/cs:update`. This is the canonical context schema every advisor reads.
2. **Ask** — the `chief-of-staff` skill routes any question to the right advisor(s). See its routing matrix for all 14 roles.
3. **Big decisions** — the `board-meeting` skill runs a **6-phase** deliberation: (1) context gathering → (2) independent contributions (isolated) → (3) critic analysis → (4) synthesis → (5) founder review (full stop) → (6) decision extraction. Invoked via `/cs:boardroom` in the c-level-agents plugin.
4. **Memory** — decisions land in the canonical two-layer layout `~/.claude/decisions/{raw,approved}/` (see `../agent-protocol/SKILL.md` → "Decision Memory (Canonical Layout)").

## What's in the Bundle (33 skills)

**14 C-suite roles + critic (15):** ceo-advisor, cfo-advisor, cto-advisor, coo-advisor, cpo-advisor, cmo-advisor, cro-advisor, ciso-advisor, chro-advisor, general-counsel-advisor, chief-data-officer-advisor, chief-ai-officer-advisor, chief-customer-officer-advisor, vpe-advisor — plus the executive-mentor critic (sibling plugin).

**Orchestration (6):** cs-onboard, chief-of-staff, board-meeting, decision-logger, agent-protocol, context-engine.

**Cross-cutting (6):** board-deck-builder, scenario-war-room, competitive-intel, org-health-diagnostic, ma-playbook, intl-expansion.

**Culture & collaboration (6):** culture-architect, company-os, founder-coach, strategic-alignment, change-management, internal-narrative.

Plus this index (1). 37 stdlib-only Python tools and 68 reference docs across the bundle.

## Routing Quick Reference

Full matrix in `../chief-of-staff/SKILL.md` and `../chief-of-staff/references/routing-matrix.md`. Primary roles: CFO (capital/burn), CRO (pipeline/sales), CMO (positioning), CPO (roadmap/PMF), CTO (architecture), COO (ops/OKRs), CHRO (people), CISO (security), GC (contracts/term sheets), CDO (data strategy/training-data rights), CAIO (AI strategy/evals), CCO (retention/GRR), VPE (delivery/DORA), CEO (direction). Multi-domain or irreversible → board meeting.

## Related Layers

- `../../c-level-agents/` — 13 cs-* persona agents + 21 `/cs:*` slash commands on top of these skills
- `../../executive-mentor/` — adversarial `/em:*` critic commands
- `../../CLAUDE.md` — full architecture diagram and integration guide
