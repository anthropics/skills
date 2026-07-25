# Sprint Planning Guide

Sprint planning workflows, capacity calculation, and backlog management.

---

## Table of Contents

- [Sprint Planning Workflow](#sprint-planning-workflow)
- [Capacity Planning](#capacity-planning)
- [Backlog Prioritization](#backlog-prioritization)
- [Sprint Ceremonies](#sprint-ceremonies)
- [Metrics and Tracking](#metrics-and-tracking)

---

## Sprint Planning Workflow

### Pre-Planning (1-2 Days Before)

1. Review and refine backlog items for upcoming sprint
2. Ensure top items have acceptance criteria
3. Validate story point estimates with team
4. Identify dependencies between stories
5. Confirm team availability for sprint
6. **Validation:** Top 1.5x capacity of stories are refined and estimated

### Sprint Planning Meeting

**Duration:** 2 hours for 2-week sprint

**Agenda:**

| Time | Activity | Participants |
|------|----------|--------------|
| 0:00-0:15 | Review sprint goal and priorities | PO presents |
| 0:15-0:45 | Discuss top backlog items | Team asks questions |
| 0:45-1:15 | Team selects stories for sprint | Team decides |
| 1:15-1:45 | Break down stories into tasks | Team collaborates |
| 1:45-2:00 | Confirm commitment and identify risks | All |

### Planning Checklist

**Before Planning:**
- [ ] Backlog groomed with top items refined
- [ ] Previous sprint retrospective actions reviewed
- [ ] Team capacity calculated
- [ ] Dependencies identified
- [ ] Sprint goal drafted

**During Planning:**
- [ ] Sprint goal agreed
- [ ] Stories selected fit within capacity
- [ ] Acceptance criteria reviewed for each story
- [ ] Tasks identified for complex stories
- [ ] Risks and blockers discussed

**After Planning:**
- [ ] Sprint backlog visible to all
- [ ] Sprint goal communicated
- [ ] Calendar blocked for ceremonies
- [ ] Dependencies communicated to other teams

---

## Capacity Planning

### Team Capacity Calculation

```
Sprint Capacity = (Team Members × Sprint Days × Hours/Day × Focus Factor)
                  ÷ Hours per Story Point

Simplified Version:
Sprint Capacity = Average Velocity × Availability Factor
```

### Availability Factors

| Scenario | Factor | Example |
|----------|--------|---------|
| Full sprint, no PTO | 1.0 | 30 points if velocity = 30 |
| 1 team member out 50% | 0.9 | 27 points |
| Holiday during sprint | 0.8 | 24 points |
| Multiple team members out | 0.7 | 21 points |
| Major release/on-call | 0.75 | 22-23 points |

### Capacity Buffer Rules

| Commitment Level | % of Velocity | Purpose |
|------------------|---------------|---------|
| Committed | 80-85% | High confidence delivery |
| Stretch | 10-15% | Optional if things go well |
| Buffer | 5-10% | Unplanned work, bugs |

### Sprint Loading Example

```
Team Velocity: 30 points/sprint
Availability: 90% (one team member partially out)
Adjusted Velocity: 27 points

Sprint Loading:
- Committed work: 23 points (85% of 27)
- Stretch goals: 4 points (15% of 27)
- Buffer: Remaining capacity for bugs/support

Story Selection:
[H] US-001: User dashboard (5 pts) ← Committed
[H] US-002: Export feature (3 pts) ← Committed
[H] US-003: Search filter (5 pts) ← Committed
[M] US-004: Settings page (5 pts) ← Committed
[M] US-005: Help tooltips (3 pts) ← Committed
[L] US-006: Theme options (2 pts) ← Committed
------------------------
Committed Total: 23 points

[L] US-007: Sort options (2 pts) ← Stretch
[L] US-008: Print view (2 pts) ← Stretch
------------------------
Stretch Total: 4 points
```

---

## Backlog Prioritization

### Priority Framework

| Priority | Definition | SLA |
|----------|------------|-----|
| Critical | Blocking users, security, data loss | Immediate |
| High | Core functionality, key user needs | This sprint |
| Medium | Improvements, enhancements | Next 2-3 sprints |
| Low | Nice-to-have, minor improvements | Backlog |

### Prioritization Factors

| Factor | Weight | Questions |
|--------|--------|-----------|
| Business Value | 40% | Revenue impact? User demand? Strategic? |
| User Impact | 30% | How many users? How often used? |
| Risk/Dependencies | 15% | Technical risk? External dependencies? |
| Effort | 15% | Size? Complexity? Uncertainty? |

### WSJF (Weighted Shortest Job First)

For larger items, use SAFe's WSJF:

```
WSJF = Cost of Delay / Job Duration

Cost of Delay = User Value + Time Criticality + Risk Reduction

Scale: 1, 2, 3, 5, 8, 13, 20

Example:
Feature A: CoD = 13, Duration = 5 → WSJF = 2.6
Feature B: CoD = 8, Duration = 2 → WSJF = 4.0 ← Higher priority
```

### Backlog Organization

| Section | Content | Review Frequency |
|---------|---------|------------------|
| Sprint Backlog | Committed for current sprint | Daily |
| Ready | Refined, estimated, prioritized | Each planning |
| Grooming | Needs refinement | Weekly |
| Icebox | Future consideration | Monthly |
| Archive | Completed or obsolete | Quarterly |

---

## Sprint Ceremonies

### Daily Standup

**Duration:** 15 minutes max
**Format:** Each team member answers:

1. What did I complete yesterday?
2. What will I work on today?
3. What blockers do I have?

**Product Owner Role:**
- Listen for blockers needing PO action
- Answer clarifying questions
- Note scope concerns for offline discussion
- Update stakeholders on progress

### Backlog Refinement (Grooming)

**Duration:** 1-2 hours per week
**Timing:** Mid-sprint

**Agenda:**

| Time | Activity |
|------|----------|
| 0:00-0:15 | Review upcoming priorities |
| 0:15-0:45 | Detail acceptance criteria for top items |
| 0:45-1:15 | Estimate new stories |
| 1:15-1:30 | Split large stories |

**Readiness Criteria:**
- [ ] Clear user story format (As a... I want... So that...)
- [ ] Acceptance criteria defined (Given-When-Then)
- [ ] Story point estimate agreed
- [ ] Dependencies identified
- [ ] Fits in one sprint (≤8 points)

### Sprint Review (Demo)

**Duration:** 1 hour for 2-week sprint

**Agenda:**

| Time | Activity | Lead |
|------|----------|------|
| 0:00-0:05 | Sprint goal recap | PO |
| 0:05-0:40 | Demo completed work | Team |
| 0:40-0:50 | Stakeholder feedback | Stakeholders |
| 0:50-1:00 | Roadmap update | PO |

**Demo Checklist:**
- [ ] Only demo completed (done-done) stories
- [ ] Use production or production-like environment
- [ ] Show user perspective, not technical details
- [ ] Collect feedback for backlog items
- [ ] Thank team for accomplishments

### Sprint Retrospective

**Duration:** 1.5 hours for 2-week sprint

**Format Options:**

| Format | Structure |
|--------|-----------|
| Start-Stop-Continue | What to begin, end, keep doing |
| 4Ls | Liked, Learned, Lacked, Longed for |
| Sailboat | Wind (helpers), Anchors (blockers), Rocks (risks) |
| Mad-Sad-Glad | Emotional state about sprint events |

**Action Items:**
- Maximum 2-3 improvement actions per retro
- Assign owner and due date
- Review previous actions at start of next retro

---

## Metrics and Tracking

### Sprint Metrics

| Metric | Formula | Target |
|--------|---------|--------|
| Velocity | Points completed / sprint | Stable ±10% |
| Commitment Reliability | Completed / Committed | >85% |
| Scope Change | Points added or removed | <10% |
| Carryover | Points not completed | <15% |
| Bug Ratio | Bug points / Total points | <20% |

### Velocity Tracking

```
Sprint Velocity Trend:
Sprint 1: 25 points
Sprint 2: 28 points
Sprint 3: 30 points
Sprint 4: 32 points
Sprint 5: 29 points
------------------------
Average: 28.8 points
Trend: Stable (±10%)

Planning Recommendation: Plan for 26-29 points committed
```

### Burndown Chart

Track progress within sprint:

```
Day   Ideal    Actual   Status
---   -----    ------   ------
 0     30       30      On track
 2     24       26      Slightly behind
 4     18       20      Behind
 6     12       14      Recovering
 8      6        6      On track
10      0        2      Minor carryover
```

**Burndown Patterns:**

| Pattern | Meaning | Action |
|---------|---------|--------|
| Flat start | No progress early | Check blockers |
| Late drop | Last-minute completion | Improve WIP limits |
| Scope increase | Line moves up | Address scope creep |
| Early completion | Done before sprint end | Pull stretch items |

### Definition of Done

Story is complete when:

- [ ] Code complete and reviewed
- [ ] Unit tests written and passing
- [ ] Integration tests passing
- [ ] Acceptance criteria verified
- [ ] Documentation updated
- [ ] Deployed to staging
- [ ] PO accepted
- [ ] No critical bugs

### Release Metrics

| Metric | Definition | Target |
|--------|------------|--------|
| Lead Time | Idea to production | <2 sprints |
| Cycle Time | Development start to done | <1 sprint |
| Throughput | Stories completed/sprint | Increasing |
| Defect Escape | Bugs found in production | Decreasing |
