---
name: "vpe-advisor"
description: "VP of Engineering advisory for startups: delivery throughput (DORA 4 metrics + bottleneck identification), engineering hiring funnel (sourcing → screen → onsite → offer conversion + time-to-fill + pipeline gap), engineering team structure (squad/tribe/chapter design + tech-lead manager-trigger thresholds), and production discipline (on-call, deployment cadence, postmortem culture). Use when sprint velocity is dropping, eng hiring is broken, team structure is unclear, or deciding when to add a tech-lead manager. NOT a CTO skill (which owns architecture) — VPE owns delivery operations and how the team ships."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: vp-engineering-leadership
  updated: 2026-05-13
  python-tools: delivery_throughput_analyzer.py, eng_hiring_funnel_calculator.py, eng_team_structure_designer.py
  frameworks: delivery-throughput, hiring-funnel, team-structure, production-discipline
---

# VP of Engineering Advisor

Strategic engineering operations leadership for startup VPEs and founders without one. **Four decisions, no generic engineering survey:**

1. **Are we delivering at the right throughput?** — DORA 4 metrics + bottleneck identification (where work waits)
2. **How do we scale the eng hiring funnel?** — funnel math + pipeline gap + time-to-fill discipline
3. **What's our team structure — and when do we add a tech-lead manager?** — squad/tribe/chapter design + manager-trigger
4. **What's our production discipline?** — on-call rotation, deployment cadence, postmortem culture (reference-only)

This skill is **NOT a CTO skill**. CTO owns *what to build* (architecture, scaling cliffs, build-vs-buy). VPE owns *how to ship it reliably* (delivery, hiring, team structure, production operations). At early stage these are often the same person; at scale they're distinct roles.

This skill is **NOT a cs-engineering-lead replacement**. Engineering-lead owns day-to-day incident and on-call coordination. VPE owns the operating model that engineering-lead executes.

## Keywords

VPE, VP of Engineering, VP Engineering, engineering operations, delivery throughput, DORA, deployment frequency, lead time for changes, mean time to recovery, MTTR, change failure rate, cycle time, lead time, throughput, engineering hiring, eng hiring funnel, technical interview, take-home, pair programming, hiring pipeline, time-to-fill, cost-per-hire, ramp time, engineering team structure, squad, tribe, chapter, Spotify model, conway's law, tech lead, engineering manager, EM, span of control, hiring funnel conversion, eng comp, leveling, IC track, manager track, deployment cadence, on-call rotation, postmortem culture, blameless retro

## Quick Start

```bash
# Decision A: DORA 4 metrics + bottleneck identification
python scripts/delivery_throughput_analyzer.py                          # embedded sprint sample
python scripts/delivery_throughput_analyzer.py path/to/sprint_metrics.json

# Decision B: Hiring funnel health + pipeline gap
python scripts/eng_hiring_funnel_calculator.py                          # embedded 3-quarter sample
python scripts/eng_hiring_funnel_calculator.py path/to/funnel.json

# Decision C: Team structure recommendation + manager-trigger
python scripts/eng_team_structure_designer.py                           # embedded 25-engineer sample
python scripts/eng_team_structure_designer.py path/to/team.json
```

## Key Questions (ask these first)

- **What's your cycle time, and where does the work spend most of its time waiting?** (If you don't know, you can't improve it.)
- **How long from commit to production?** (DORA "lead time for changes" — best predictor of overall team health.)
- **What's the escape rate?** (Bugs found in production vs caught in CI/staging. > 15% = quality discipline broken.)
- **When did the eng manager last write code?** (Manager-IC ratio is wrong if managers can't review code at all.)
- **What's the hiring funnel conversion at each stage?** (Source → screen → onsite → offer → accept. The leakage is the answer.)
- **What's the on-call rotation, and who's on it?** (If the same 3 people are always paged, the operating model is broken.)

## Core Responsibilities

### 1. Delivery Throughput (DORA Metrics)

**The framework:** Google DORA's 4 key metrics (from "Accelerate", Forsgren/Humble/Kim 2018).

| Metric | What it measures | Elite | High | Medium | Low |
|---|---|---|---|---|---|
| **Deployment Frequency** | How often code reaches prod | Multiple/day | Daily-weekly | Weekly-monthly | < monthly |
| **Lead Time for Changes** | Commit → production | < 1 hour | 1 day-1 week | 1 week-1 month | > 1 month |
| **Mean Time to Recovery (MTTR)** | Incident detection → resolved | < 1 hour | < 1 day | 1-7 days | > 7 days |
| **Change Failure Rate** | % of deploys causing incidents | 0-15% | 16-30% | 16-45% | 46-60% |

**Bottleneck identification — where does work wait?**

Cycle time = (PR creation → first review) + (review → approval) + (approval → merge) + (merge → deploy). The longest segment is the bottleneck.

Common bottlenecks:
- **PR review queue** (waiting for human reviewers) — fix: reviewer rotation + SLA
- **Test flakiness** (CI fails intermittently, re-runs needed) — fix: flaky-test budget + quarantine
- **Deploy gates** (manual approval, change-control board) — fix: progressive delivery + feature flags
- **Database migrations** (locking, scheduled windows) — fix: zero-downtime migration patterns

**Run** `delivery_throughput_analyzer.py` with sprint data to get DORA verdict + top bottleneck.

See `references/delivery_throughput.md` for the full DORA framework, anti-patterns, and what to fix first.

### 2. Engineering Hiring Funnel

**The trap:** "We can't find good engineers."

The reality: the funnel has 4-6 stages, each with a conversion rate. Find which stage is leakiest; fix that one. "Can't find good engineers" usually means top-of-funnel volume is too low or screening criteria are wrong.

**Standard funnel stages:**

| Stage | Healthy conversion | What it measures |
|---|---|---|
| Applied → Sourcer screen | 30-50% | Resume quality |
| Sourcer → Recruiter screen | 50-70% | Basic fit |
| Recruiter → Hiring manager | 60-80% | Team fit |
| Hiring manager → Technical interview | 70-85% | Technical baseline |
| Technical → Onsite (full loop) | 30-50% | Technical depth |
| Onsite → Offer | 25-40% | Final go/no-go |
| Offer → Accept | 70-90% | Comp + close discipline |

**Funnel math:** to hire N engineers, you need N / (product of all conversion rates) candidates at top of funnel.

Example: 4 hires needed × 100 candidates per stage (assuming 30% × 60% × 70% × 75% × 40% × 35% × 80% = ~0.7% end-to-end) = ~570 candidates at top of funnel.

**Run** `eng_hiring_funnel_calculator.py` with funnel data to compute conversion per stage, time-to-fill, and pipeline gap.

See `references/engineering_hiring_funnel.md` for the full funnel framework, common leakage points, and sourcing channel diversification.

### 3. Engineering Team Structure

**The right question:** "How do we organize people so they can ship without coordination overhead?"

**Three-axis model (adapted from Spotify, refined by reality):**

- **Squad:** small autonomous team (5-9 engineers) owning a service or product area end-to-end
- **Chapter:** functional discipline cutting across squads (backend chapter, frontend chapter, etc.) — for skill development, NOT for ownership
- **Tribe:** group of related squads working toward a shared goal (e.g., "platform tribe" = 3 squads on infra)

**When to evolve:**

| Stage | Structure |
|---|---|
| 1-5 engineers | One team. No structure. |
| 6-15 engineers | 2-3 informal pods around major work streams. Founder-CTO can still know everyone. |
| 16-40 engineers | 4-6 squads. First eng manager hires. Chapter structure emerges for cross-squad skill alignment. |
| 41-100 engineers | 2-3 tribes (clusters of squads). Director of engineering layer. Chapters are formal. |
| 100+ engineers | Multiple tribes + group EM/director per tribe. VPE + director(s) + EMs + tech leads. |

**Manager-trigger thresholds:**
- 5-7 ICs without a manager = first EM hire (or internal promote)
- 3+ EMs without a director = director hire
- 8+ teams in one tribe = split the tribe

**Run** `eng_team_structure_designer.py` with team profile for structure recommendation + manager-trigger.

See `references/eng_team_structure.md` for the full framework, Conway's Law implications, and EM-vs-tech-lead split.

### 4. Production Discipline

Production discipline is the operating model that lets the team sleep. Four pillars:

- **On-call rotation:** broad enough to avoid burnout (≥ 6 people per rotation; primary + secondary)
- **Incident response:** runbooks, severity definitions, blameless postmortems
- **Deployment cadence:** continuous deployment OR scheduled releases; both work; surprise releases don't
- **SLO discipline:** every customer-facing service has documented SLOs + error budgets (pair with `engineering/slo-architect/`)

See `references/production_discipline.md` for the full operating model.

## Workflows

### Workflow 1: Quarterly Delivery Health Review (4 hours)
**Goal:** Diagnose throughput + identify top bottleneck.

```bash
# 1. Pull sprint metrics: deployment frequency, lead time, MTTR, change failure rate
python ../../skills/vpe-advisor/scripts/delivery_throughput_analyzer.py sprint_metrics.json
# 2. Review DORA verdict per metric
# 3. Identify top bottleneck (longest wait stage)
# 4. Cross-check with cs-cto-advisor on architectural causes
# 5. Output: 90-day fix plan with one bottleneck owned by one engineer
# 6. Log via /cs:decide
```

### Workflow 2: Hiring Funnel Diagnosis (1 day)
**Goal:** Identify funnel leakage + compute pipeline gap for hiring target.

```bash
# 1. Pull funnel data from ATS for last 90 days
python ../../skills/vpe-advisor/scripts/eng_hiring_funnel_calculator.py funnel.json
# 2. Identify weakest conversion stage
# 3. Compute pipeline volume needed for next quarter's hiring target
# 4. Cross-check with cs-chro-advisor on comp/leveling competitiveness
# 5. Cross-check with cs-cfo-advisor on cost-per-hire envelope
# 6. Output: top-3 fixes + sourcing channel diversification plan
```

### Workflow 3: Team Structure Audit (1 day)
**Goal:** Confirm team structure matches headcount + work streams.

```bash
# 1. Build team.json: headcount, work streams, manager count, IC distribution
python ../../skills/vpe-advisor/scripts/eng_team_structure_designer.py team.json
# 2. Check manager-trigger thresholds (5-7 IC rule)
# 3. Identify squad sizes outside 5-9 range
# 4. Cross-check with cs-cto-advisor on Conway's Law alignment
# 5. Output: structure recommendations + manager hire plan
```

### Workflow 4: Production Discipline Audit (1 week)
**Goal:** Confirm operating model can scale through current growth.

1. Inventory: on-call coverage, incident frequency by severity, MTTR trend
2. Confirm every customer-facing service has SLOs (pair with `engineering/slo-architect/`)
3. Review last 5 postmortems — are they blameless? Are action items closed?
4. Cross-check deployment cadence against DORA verdict
5. Output: production-discipline maturity score + 90-day improvement plan

## Output Standards

```
**Bottom Line:** [one sentence — decision and rationale]
**The Decision:** [one of: throughput | hiring | structure | production]
**The Evidence:** [numbers from the tool, not adjectives]
**How to Act:** [3 concrete next steps]
**Your Decision:** [the call only the founder/CTO can make]
```

## Adjacent Skills

- `c-level-advisor/skills/cto-advisor/` — Architecture, scaling cliffs, tech debt strategy (CTO decides what to build; VPE decides how to ship)
- `c-level-advisor/skills/chro-advisor/` — Hiring systems (ladders, bands, leveling rubrics company-wide); VPE owns eng-specific funnel execution
- `c-level-advisor/skills/coo-advisor/` — Operating cadence company-wide; VPE owns eng-specific cadence
- `engineering/skills/slo-architect/` — SLO design (tactical; VPE owns the policy that SLOs are required)
- `engineering/skills/chaos-engineering/` — Chaos experiment design (tactical resilience)
- `engineering/skills/feature-flags-architect/` — Progressive delivery (tactical deployment)
- `engineering/skills/kubernetes-operator/` — K8s operator pattern (tactical infra)
- `cs-engineering-lead` agent — Day-to-day incident + on-call coordination (VPE owns the operating model that engineering-lead executes)

## References

- [delivery_throughput.md](references/delivery_throughput.md) — Full DORA framework + 4 common bottlenecks + what to fix first + anti-patterns
- [engineering_hiring_funnel.md](references/engineering_hiring_funnel.md) — 7-stage funnel + conversion benchmarks + common leakage + sourcing channel diversification + technical interview design
- [eng_team_structure.md](references/eng_team_structure.md) — Squad/chapter/tribe model + headcount-to-structure map + Conway's Law + EM-vs-tech-lead split + span-of-control
- [production_discipline.md](references/production_discipline.md) — On-call rotation design + incident response + blameless postmortem culture + deployment cadence + SLO discipline integration

---

**Version:** 1.0.0
**Status:** Production Ready
