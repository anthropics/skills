# Flow Metrics & Probabilistic Forecasting Canon

The measurement layer behind `jira_snapshot_bridge.py --to flow`. The 2024–2026 delivery
canon moved from velocity/story-point folklore to **flow measurement + probabilistic
forecasting + outcome measures**. This file anchors every number the bridge emits.

## The four mandatory flow measures (Kanban Guide, May 2025)

The Kanban Guide mandates exactly four measures — teams that track anything must track
these:

| Measure | Definition | Bridge field |
|---|---|---|
| **WIP** | Work items started but not finished | `counts.wip` |
| **Throughput** | Items finished per unit of time | `throughput.done_per_week` |
| **Cycle time** | Elapsed time started → finished | `cycle_time_days.p50/p85/p95` |
| **Work item age** | Elapsed time for *unfinished* started items | `work_item_age` |

Plus a **Service Level Expectation (SLE)**: "we finish items of this type within N days,
X% of the time." The bridge defaults the SLE to the p85 cycle time and reports
conformance. **Work item age is the leading indicator** — an in-progress item older than
the p85 SLE is the earliest visible slip signal (`aging_wip_alerts`); cycle time only
tells you after the fact.

Caveat the bridge prints itself: Jira exports rarely carry an in-progress timestamp, so
cycle time is approximated created→resolved. When your workflow logs a real start
transition, prefer it.

## Percentiles, not averages

Cycle-time distributions are right-skewed; the mean lies. Report p50/p85/p95
(Vacanti). Commit externally at p85, plan internally at p50, treat p95 as the tail-risk
budget.

## Monte Carlo forecasting (replaces story-point velocity)

"When will it be done?" is answered by sampling historical throughput, not by dividing
backlog points by velocity: sample the weekly-throughput history 10k times, read the
p50/p70/p85/p95 week counts (`--forecast N`). Rules the bridge enforces:

- **Refuses on < 10 completed items across < 4 distinct weeks** — thin history produces
  confident nonsense.
- **Seeded RNG** — same data in, same forecast out (audit-reproducible).
- **Ranges with confidence, never a date** — a single-date promise is the anti-pattern.

## Outcome measures above flow

Flow says whether delivery is smooth, not whether it is *valuable*:

- **DORA 2025**: replaced low/high/elite clusters with seven team archetypes over eight
  measures; core 2025 finding — AI *amplifies* an org's existing strengths and
  dysfunctions (individual output up, org delivery flat without enabling capabilities).
- **EBM (Scrum.org)**: four Key Value Areas — Current Value, Unrealized Value,
  Time-to-Market, Ability to Innovate. Most orgs measure only T2M; empty CV/UV areas mean
  you are measuring motion, not value.
- **SPACE**: any metrics portfolio must span ≥ 3 of Satisfaction/Performance/Activity/
  Communication/Efficiency — activity-only portfolios (PR counts) are the documented
  anti-pattern.
- **Derived health beats self-reported RAG**: diff derived signals (aging WIP, scope
  churn, schedule variance) against the self-reported status to find "watermelon"
  projects (green outside, red inside) — the pattern behind senior-pm's dashboard.

## Sources

1. The Kanban Guide (May 2025) — https://kanbanguides.org/the-kanban-guide/
2. Daniel Vacanti, *Actionable Agile Metrics for Predictability* and *When Will It Be
   Done?* (ActionableAgile Press)
3. Scrum.org, "4 Key Flow Metrics and How to Use Them" —
   https://www.scrum.org/resources/blog/4-key-flow-metrics-and-how-use-them-scrums-events
4. Scrum.org, "Monte Carlo Forecasting in Scrum" —
   https://www.scrum.org/resources/blog/monte-carlo-forecasting-scrum
5. DORA, *Accelerate State of DevOps Report 2025* — https://dora.dev/dora-report-2025/
6. Scrum.org, *The Evidence-Based Management Guide* —
   https://www.scrum.org/resources/evidence-based-management
7. Forsgren, Storey et al., "The SPACE of Developer Productivity", ACM Queue —
   https://queue.acm.org/detail.cfm?id=3454124
