---
name: capacity-planner
description: "Use when an ops leader (Director of CX, Head of Support, VP Ops, Head of BizOps, Head of IT ops, Head of Finance ops) is sizing ops capacity, building a headcount plan, modeling utilization risk, planning Q3 capacity or annual support capacity, or designing CS coverage — and needs Erlang-C queueing math, P90 demand sizing, shrinkage-adjusted FTE, manager-trigger thresholds, and a quarterly hiring sequence with ramp + attrition. Apply when sustained team utilization is above 80% or when the team is growing >50% in 12 months. Run before committing the headcount budget. This is NOT engineering capacity (see vpe-advisor for DORA + cycle time) and NOT strategic 3-year workforce planning (see chro-advisor)."
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [bizops, capacity, headcount, utilization, queueing-theory, ops-planning, little-law, workforce]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# capacity-planner

Sizing tool for **ops teams that handle queued work** — Support, CX,
Customer Success, BizOps, IT ops, Finance ops. Built on Erlang-C
queueing theory, Little's Law, and the operational-leadership canon
(Fournier, Larson, Cleveland, Reinertsen). Deterministic, stdlib-only,
no LLM calls.

## Purpose

You are an ops leader sized 15 → 35 with no idea how the 35-person org
will actually behave at peak load. Or you are at 88% utilization and
SLA is starting to slip. Or you have a hiring budget approved and need
to sequence it across four quarters without burning out the existing
team. This skill answers those questions with arithmetic, not vibes.

It produces three artifacts:

1. **Capacity sizing** at 70/80/90% utilization against P50/P90/P99
   demand, with P(SLA breach) at each point and a SAFE/WATCH/AT_RISK/CRITICAL
   risk band.
2. **Utilization health** at the per-member traffic-light level plus a
   team verdict (HEALTHY/SQUEEZED/OVERLOADED/UNBALANCED).
3. **12-month quarterly hiring plan** accounting for ramp curves,
   attrition, QoQ demand growth, and span-of-control manager triggers.

## When to use

- **Annual ops capacity planning** (October-November for the following
  fiscal year).
- **Quarterly re-sizing** if demand changed >15% or attrition spiked.
- **Pre-budget defense** — the math that justifies the headcount ask
  to your CFO.
- **Diagnostic** when an ops team is missing SLA and you need to know
  whether it's a sizing problem, a process problem, or a bottleneck
  problem.
- **M&A / new-segment launch** modeling — sizing a new team or
  combined org.

## Workflow

1. **Intake demand**. Pull P50/P90/P99 daily ticket/case volume from
   your work system (Zendesk, Intercom, JSM, ServiceNow, Salesforce).
   If you only have averages, stop and pull the distribution. Single-
   point demand estimates are the most expensive anti-pattern in ops.
2. **Model throughput**. Run `capacity_modeler.py` with your demand,
   AHT, SLA target, current FTE, and shrinkage. Use `--profile` for
   your function (support / cx / bizops / finance-ops / it-ops). Read
   the 80%-utilization row — that's your sizing point.
3. **Flag utilization risk**. Run `utilization_analyzer.py` against
   your current team's actual utilization data. Anyone >85% sustained
   is a throughput-collapse risk per Reinertsen. Spread >30 percentage
   points across team means UNBALANCED — fix that before hiring.
4. **Sequence hiring**. Run `hiring_sequencer.py` with current FTE,
   target EOY, ramp time, attrition, and growth. It will front-load
   hires (Q1 35%, Q4 15%), apply ramp curves, and trigger a manager
   hire when span of control crosses 7 ICs/manager.
5. **Walk the Forcing-question library** (see below). One question at
   a time. Do not skip ahead. Answers must be written down before
   you commit the plan.

## Scripts

- `scripts/capacity_modeler.py` — Erlang-C sizing with shrinkage
  adjustment and P50/P90/P99 breach probabilities. `--profile`
  for industry defaults.
- `scripts/utilization_analyzer.py` — per-member traffic-light +
  team-level health verdict with variance detection.
- `scripts/hiring_sequencer.py` — 12-month quarterly plan with ramp,
  attrition, growth, max-hires-per-quarter constraint, and
  manager-trigger logic.

All three accept `--input <path>` (JSON), `--output {markdown,json}`,
`--sample` (built-in example), and `--help`. Stdlib only.

## Quick example

```bash
# Emits an Erlang-C capacity model (required headcount + P50/P90/P99 breach probabilities) for the built-in example
cd business-operations/skills/capacity-planner && python3 scripts/capacity_modeler.py --sample
```

## References

- `references/queueing_theory_canon.md` — Erlang, Little, Hopp &
  Spearman, Reinertsen, Kingman, Cleveland, ITIL, Armony et al. (8
  sources). The math.
- `references/ops_workforce_planning_canon.md` — Fournier, Larson,
  Google SRE Workbook, Frei, Lawler, Bersin, Gartner, Grove (8
  sources). The people factors.
- `references/capacity_anti_patterns.md` — 11 named anti-patterns
  with cited sources, tool guards, and the meta-discipline that
  Lencioni + Goldratt + Christensen impose. (8+ named sources.)

## Assets

- `assets/capacity_brief_template.md` — 20-minute fill-out template
  with JSON skeletons for all three tools and an output checklist.

## Assumptions

This skill assumes:

- Work is **queued** (tickets, cases, work items) — not project-style.
  If your team's work isn't queued, this is the wrong skill.
- Demand has a **stationary-enough distribution** within a quarter.
  Step-changes (new product launch, M&A, regulatory shift) require
  re-running mid-quarter.
- You have **at least 90 days of historical demand data** to compute
  P50/P90/P99. If not, generate the distribution from your sales /
  user-base forecast first.
- Service is **single-class** within a queue. If you have hard
  priority tiers (P1/P2/P3 with class-specific SLAs), model each as
  a separate queue and sum.
- **Channels are modeled coherently.** Multi-channel teams use the
  appropriate `--profile` with built-in shrinkage premium.

## Anti-patterns

See `references/capacity_anti_patterns.md` for the full taxonomy with
sources. Top eight:

1. Plan-to-100%-utilization (Reinertsen Principle 12)
2. Treat-ramp-as-instant (Larson)
3. Ignore-attrition-in-12-month-plan (Bersin)
4. Hire-ICs-forever-with-no-manager-trigger (Fournier)
5. Size-to-P50-demand-only (Cleveland)
6. No-shrinkage-adjustment (Cleveland, SRE Workbook)
7. Single-channel-model-for-multi-channel-work (Gartner, Kingman)
8. No-surge-plan-for-P99-events (Hopp & Spearman, Reinertsen)

## Distinct from

- **`c-level-advisor/vpe-advisor`** measures *engineering* throughput
  via DORA 4 metrics, story points, deployment frequency, and cycle
  time bottlenecks. It is for engineering teams shipping code. This
  skill is for ops teams handling tickets/cases. Different unit of
  work, different math (Erlang-C vs. DORA), different bottleneck
  (queueing-blind staffing vs. WIP + lead time).
- **`c-level-advisor/chro-advisor`** does *strategic* workforce
  planning (1-5 year capability portfolios, talent supply, leadership
  succession). This skill does *operational* 0-12 month capacity
  sizing against demand. Per Lawler: conflating them gets you hired
  into the wrong jobs.
- **`project-management/*`** tracks delivery throughput on projects
  (Jira velocity, sprint capacity). This skill sizes around steady-
  state queued work.
- **Sibling `process-mapper`** *finds* the bottleneck. This skill
  *sizes the team around* a known bottleneck. Order of operations:
  process-mapper first → capacity-planner second. Hiring around the
  wrong constraint wastes the hires.
- **`business-growth/cs-coverage`** (if it exists) sizes Customer
  Success coverage by ARR/CSM ratio and segment. This skill sizes by
  queued work volume (tickets, cases, escalations). For a CS team
  that handles both relationship work AND a ticket queue, run both.

## Forcing-question library (Matt Pocock grill discipline)

**Discipline**: walk these one at a time. Do not skip ahead. Answers must
be written down. If you can't answer one, that is your next investigation.

### Q1 — "What is your bottleneck, and have you confirmed it empirically?"

**Recommended answer**: a named, measured stage in the workflow with
queue-time data showing where work waits. Not a vibe. Not "escalations
take too long". An actual measured queue.

**Why it's the first question**: Goldratt (*The Goal*, 1984) — every
system has exactly one binding constraint at a time. Sizing around the
wrong constraint wastes hires entirely. If you do not know your
bottleneck, run `process-mapper` BEFORE this skill.

**Canon**: Eli Goldratt, *The Goal* (1984); Reinertsen, *Principles of
Product Development Flow* (2009).

### Q2 — "What service trade-off are you accepting?"

**Recommended answer**: a written, explicit choice — fast vs. empathetic,
broad vs. deep, low-cost vs. high-quality. Frances Frei is unambiguous:
you cannot win all four. The team that tries wins zero.

**Why it matters**: AHT, SLA, and shrinkage inputs are the operational
expression of this trade-off. If they don't agree (e.g., you set AHT for
"empathy" but SLA for "speed"), the plan is internally inconsistent.

**Canon**: Frances Frei & Anne Morriss, *Uncommon Service* (HBR Press,
2012).

### Q3 — "What's your demand P90, and what's the gap to your P99?"

**Recommended answer**: two specific numbers from the last 90 days of
data, with the calendar context of each (e.g., "P90 was 480 tickets/day
on normal Tuesdays; P99 was 720 on the day after the November release").
A team sized to P50 misses SLA half the time. A team sized to P99
overstaffs by 30-50%. P90 is the right operating sizing point per
Cleveland.

**Canon**: Brad Cleveland, *Call Center Management on Fast Forward* (4th
ed., 2019); A.K. Erlang, *The Theory of Probabilities and Telephone
Conversations* (1909).

### Q4 — "At your planned utilization, what is P(SLA breach) at P90 and at P99?"

**Recommended answer**: two probabilities, computed (not guessed) from
Erlang-C with your specific N, AHT, and SLA target. If P(breach at P90)
> 10% you are understaffed at the sizing point. If P(breach at P99) >
50% you have no surge plan and the next peak event will be visible to
the CEO.

**Canon**: Erlang (1909); Hopp & Spearman, *Factory Physics* (3rd ed.,
2008), VUT equation.

### Q5 — "Have you budgeted replacement hires for the attrition you'll see this year?"

**Recommended answer**: yes, with a specific number. At 30% annual
attrition (Bersin BPO midpoint), a 20-FTE team loses ~6 people this year.
If your "add 5 net" plan is actually a "hire 11" plan, the recruiting
volume changes drastically. Anti-pattern #3.

**Canon**: Bersin/Deloitte talent benchmarks (2015-2023); Edward Lawler,
*Strategic Workforce Planning* (USC CEO, 2008).

### Q6 — "When does span of control trigger a manager hire, and who is the candidate?"

**Recommended answer**: a specific quarter (from `hiring_sequencer.py`)
and at least one identified candidate (internal lead or external hire).
Past 7 ICs/manager, 1:1s degrade, feedback cycles slip, attrition
climbs. Past 10 you have a coverage crisis. Hire the manager BEFORE
crossing 10, not after.

**Canon**: Camille Fournier, *The Manager's Path* (O'Reilly, 2017),
ch. 5; Andy Grove, *High Output Management* (1983).

### Q7 — "What is your surge plan for the P99 day?"

**Recommended answer**: an explicit, documented plan — overflow tier,
BPO contracted capacity, on-call rotation, executive escalation tree,
OR a written degradation contract that says "on P99 days we extend SLA
to X minutes and notify customers proactively". If the answer is "we'll
figure it out", the P99 day is a fire visible to the board.

**Canon**: Hopp & Spearman, *Factory Physics* (2008); Reinertsen (2009)
on capacity-margin discipline.

---

**Walk these seven in order. One at a time. Write the answers down. The
plan you submit is only as defensible as your answers to these seven
questions.**
