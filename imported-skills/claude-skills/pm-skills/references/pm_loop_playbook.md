# The PM Loop Playbook — five reusable delivery loops

Concrete instantiations of the loop contract (Observe → Choose → Act → Verify → Record →
Repeat-or-stop) for day-to-day PM work. Each loop names its trigger, its machine gate,
and its terminal states — a loop without a named stop is just an unbounded retry.

## Loop 1 — Sprint flow loop (weekly)

- **Observe**: `searchJiraIssuesUsingJql` → save snapshot →
  `jira_snapshot_bridge.py --to flow`.
- **Choose**: highest-leverage signal first — aging-WIP alerts beat cycle-time trends
  (age is the leading indicator; cycle time is a lagging one).
- **Act**: unblock/swarm/split the flagged item with the team; scrum-master skill for
  ceremony-level fixes.
- **Verify**: next week's bridge run — the flagged item left `aging_wip_alerts`, SLE
  conformance did not drop.
- **Stop states**: success (no alerts 2 weeks running) · stagnated (same item flagged 3
  weeks → escalate to the delivery lead by name) · approval-required (fix needs scope
  change).

## Loop 2 — Health-report loop (per reporting period)

- **Observe**: bridge `--to sprint` → `velocity_analyzer.py` +
  `sprint_health_scorer.py`; senior-pm's `project_health_dashboard.py` for the portfolio.
- **Choose**: diff derived health against the self-reported RAG — investigate the largest
  divergence first (watermelon detection).
- **Act**: senior-pm workflows (risk register, capacity rebalance).
- **Verify**: divergence shrinks next period; every red flag has a named owner + dated
  action.
- **Stop states**: success · blocked (data quality too poor to derive — fix Jira hygiene
  first, see agent-readiness note in agentic_delivery_governance.md).

## Loop 3 — Retro action loop (per sprint)

The retro is not the loop — the **action-item completion rate** is. Scrum-master's
retrospective_analyzer computes it (fixture: 46.7%).

- **Observe**: `retrospective_analyzer.py` on the retro log.
- **Choose**: oldest open action item with a named owner.
- **Act**: drive it to done or explicitly kill it (a cancelled action with a reason beats
  a zombie).
- **Verify**: completion rate trend up across 3 sprints.
- **Stop states**: success (≥ 70% completion) · stagnated (rate flat 3 sprints → the retro
  format is the problem; change the ritual, per Klein's pre-mortem alternative).

## Loop 4 — RAID hygiene loop (biweekly)

- **Observe**: risk register / RAID log staleness — entries missing owner, next-review
  date, or mitigation; issues open > 30 days.
- **Choose**: stalest critical-severity entry.
- **Act**: senior-pm's `risk_matrix_analyzer.py` re-score; pre-mortem session for new
  workstreams (prospective hindsight measurably improves risk identification — Klein).
- **Verify**: zero critical entries without owner+mitigation; staleness p85 < review
  cadence.
- **Stop states**: success · clean no-op (nothing stale — record and exit; do not invent
  work).

## Loop 5 — Comms cadence loop (weekly)

- **Observe**: which status-broadcast meetings ran this week; which stakeholder updates
  shipped.
- **Choose**: convert the largest status-broadcast meeting to an async 3P update
  (GitLab's handbook-first model: written 3-question standups take 3–5 min vs 15–30 sync;
  GitLab reports ~37% meeting-hour reduction).
- **Act**: team-communications skill (3P format); meeting-analyzer on the transcripts of
  the meetings that remain.
- **Verify**: sync:async ratio trending down; no stakeholder escalation citing "I didn't
  know".
- **Stop states**: success · approval-required (a stakeholder insists on sync — their
  call, record it).

## Rules that hold across all five

1. One bounded, reversible change per iteration (autoresearch's "ONE change" rule).
2. Fresh state before every consequential action — re-pull the snapshot, don't act on
   last week's.
3. Separate the optimizing signal from the acceptance gate — if you optimize SLE
   conformance, verify with throughput + age too (anti-overfit, loop-library).
4. Every escalation names a human and attaches the evidence log.

## Sources

1. Forward Future, Loop Library — the Observe→…→Repeat-or-stop contract and terminal-state
   taxonomy (vendored at `loop-library/SKILL.md`)
2. The Kanban Guide (May 2025) — https://kanbanguides.org/the-kanban-guide/
3. Gary Klein, "Performing a Project Premortem", HBR 2007 —
   https://hbr.org/2007/09/performing-a-project-premortem
4. GitLab Handbook, asynchronous work —
   https://handbook.gitlab.com/handbook/company/culture/all-remote/asynchronous/
5. Sumeet Moghe, *The Async-First Playbook* (2023)
6. This repo: `engineering/autoresearch-agent` (one-change-per-iteration, locked
   evaluator), `engineering/agent-harness` (state machine, budgets)
