---
name: "c-level-agents"
description: "Founder-mode executive team. 13 cs-* C-suite agents (CFO, CMO, CRO, CPO, COO, CHRO, CISO, GC, CDO, CAIO, CCO, VPE, Chief of Staff) and 21 /cs:* slash commands for forcing-question office hours, multi-role boardroom deliberation, strategic sprint pipeline, and meta routing. Use when the founder needs a virtual executive team, when invoking /cs:* commands, or when orchestrating multi-role decisions."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: executive-orchestration
  updated: 2026-05-12
  agents: cs-cfo-advisor, cs-cmo-advisor, cs-cro-advisor, cs-cpo-advisor, cs-coo-advisor, cs-chro-advisor, cs-ciso-advisor, cs-general-counsel-advisor, cs-cdo-advisor, cs-caio-advisor, cs-cco-advisor, cs-vpe-advisor, cs-chief-of-staff
  commands: cs-office-hours, cs-cfo-review, cs-cmo-review, cs-cpo-review, cs-cro-review, cs-cto-review, cs-ciso-review, cs-gc-review, cs-cdo-review, cs-caio-review, cs-cco-review, cs-vpe-review, cs-brief, cs-boardroom, cs-decide, cs-execute, cs-post-mortem, cs-founder-mode, cs-onboard, cs-cross-eval, cs-freeze
---

# c-level-agents — Founder-Mode Executive Team

A virtual C-suite delivered through slash commands and persona agents.

## Keywords

founder mode, virtual c-suite, executive team, boardroom, office hours, cfo review, cmo review, strategic sprint, decision logging, cross-model consensus, persona agents, chief of staff, forcing questions

## What This Plugin Provides

### 13 cs-* Agents (in `agents/`)

Each agent wraps an existing c-level skill and adds:
- A distinct cognitive voice (numerate skeptic, narrative-first, etc.)
- Forcing questions specific to the role
- Workflow orchestration tied to skill Python tools
- Output template: Bottom Line → What → Why → How to Act → Your Decision

See `../../references/persona-voices.md` for voice specs.

### 21 /cs:* Slash Commands (in `skills/`)

**Forcing-question office hours (12):**
- `/cs:office-hours` — YC-style 6-question intake
- `/cs:cfo-review` — unit economics, runway, dilution
- `/cs:cmo-review` — ICP, CAC payback, positioning
- `/cs:cpo-review` — RICE, JTBD, North Star, PMF
- `/cs:cro-review` — pipeline coverage, win rate, NRR
- `/cs:cto-review` — architecture risk, scaling cliff
- `/cs:ciso-review` — threat model, blast radius, compliance
- `/cs:gc-review` — contracts, IP, regulatory, term sheets
- `/cs:cdo-review` — training-data rights, data products, data assets
- `/cs:caio-review` — model selection, evals, AI risk, AI costs
- `/cs:cco-review` — GRR/NRR decomposition, churn root cause, CS coverage
- `/cs:vpe-review` — DORA metrics, cycle time, eng hiring funnel, team structure

**Strategic sprint pipeline (5):**
- `/cs:brief` → `/cs:boardroom` → `/cs:decide` → `/cs:execute` → `/cs:post-mortem`

**Meta + safety (4):**
- `/cs:founder-mode` — auto-routes to the right C-role
- `/cs:onboard` — founder interview → `company-context.md`
- `/cs:cross-eval` — multi-model consensus
- `/cs:freeze` — cooldown lock on a decision

## Quick Start

```
/cs:onboard                          # populate company context first
/cs:office-hours "should we hire a VP Sales?"
/cs:founder-mode "runway pressure"   # auto-routes to CFO
/cs:boardroom briefs/pricing-v3.md   # full panel
```

## Architecture

```
User question
   │
   ├─ Single-role? → cs-{role}-advisor agent
   │                     ↓
   │                  /cs:{role}-review command (forcing Qs)
   │                     ↓
   │                  Skill tools + references
   │                     ↓
   │                  Bottom Line + Memo
   │
   └─ Multi-role?  → /cs:boardroom
                        ↓
                     6-phase deliberation (Phase 2 isolation)
                        ↓
                     /cs:decide → decision-logger (two-layer memory)
                        ↓
                     /cs:execute → 90-day plan
```

## Integration Points

- **Existing 33 c-level skills** — wrapped, not replaced
- **decision-logger** — every `/cs:decide` writes here
- **chief-of-staff** — routing layer the agent orchestrates
- **board-meeting** — protocol the `/cs:boardroom` command runs
- **llm-wiki** — optional persistent memory bridge (see `../../references/llm-wiki-bridge.md`)
- **executive-mentor** — adversarial `/em:*` commands stack cleanly on top

## Design Principles

1. **Voice is bookended, analysis is neutral.**
2. **Artifacts over chat.** Every command produces a Markdown artifact the next command consumes.
3. **Phase 2 isolation in boardroom.** Independent thinking before cross-examination.
4. **Graceful degradation.** `/cs:cross-eval` falls back to Claude-only.
5. **No paid dependencies.** All Python tools are stdlib-only.

## References

- [persona-voices.md](../../references/persona-voices.md)
- [llm-wiki-bridge.md](../../references/llm-wiki-bridge.md)
- [Parent c-level CLAUDE.md](../../../CLAUDE.md)
- [Existing executive-mentor sibling](../../../executive-mentor/)

---

**Version:** 1.0.0
**Last Updated:** 2026-05-12
**Status:** Production Ready
