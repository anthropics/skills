---
name: "agile-product-owner"
description: Agile product ownership for backlog management and sprint execution. Covers user story writing, acceptance criteria, sprint planning, and velocity tracking. Use when writing user stories, creating acceptance criteria, planning sprints, estimating story points, breaking down epics, or prioritizing the backlog.
not_for: Kanban-only workflows, waterfall project planning, general task management, non-Scrum agile frameworks (SAFe, LeSS) without adaptation
triggers:
  - write user story
  - create acceptance criteria
  - plan sprint
  - estimate story points
  - break down epic
  - prioritize backlog
  - sprint planning
  - backlog grooming
  - sprint retrospective
  - definition of done
  - INVEST criteria
  - Given When Then
  - user story template
  - sprint capacity
  - velocity tracking
---

# Agile Product Owner

Backlog management and sprint execution toolkit for product owners, including user story generation, acceptance criteria patterns, sprint planning, and velocity tracking.

---

## Table of Contents

- [What Makes This Skill Different](#what-makes-this-skill-different)
- [User Story Generation Workflow](#user-story-generation-workflow)
- [Acceptance Criteria Patterns](#acceptance-criteria-patterns)
- [Epic Breakdown Workflow](#epic-breakdown-workflow)
- [Sprint Planning Workflow](#sprint-planning-workflow)
- [Backlog Prioritization](#backlog-prioritization)
- [Reference Documentation](#reference-documentation)
- [Tools](#tools)

---

## What Makes This Skill Different

- **Capacity math that aligns with reality:** sprint capacity is based on velocity × availability factor, not hope.
- **Acceptance criteria scaled by story size:** minimum AC counts map to story points to avoid under-spec'ing large items.
- **Weighted prioritization that stays consistent:** value 40%, impact 30%, risk 15%, effort 15% keeps tradeoffs explicit.
- **Systematic epic splitting techniques:** five concrete split patterns prevent oversized stories.
- **INVEST validation baked into workflows:** every story includes a validation step, not just guidance.

## User Story Generation Workflow

Create INVEST-compliant user stories from requirements:

1. Identify the persona (who benefits from this feature)
2. Define the action or capability needed
3. Articulate the benefit or value delivered
4. Write acceptance criteria using Given-When-Then
5. Estimate story points using Fibonacci scale
6. Validate against INVEST criteria
7. Add to backlog with priority
8. **Validation:** Story passes all INVEST criteria; acceptance criteria are testable

### User Story Template

```
As a [persona],
I want to [action/capability],
So that [benefit/value].
```

**Example:**
```
As a marketing manager,
I want to export campaign reports to PDF,
So that I can share results with stakeholders who don't have system access.
```

### Story Types

| Type | Template | Example |
|------|----------|---------|
| Feature | As a [persona], I want to [action] so that [benefit] | As a user, I want to filter search results so that I find items faster |
| Improvement | As a [persona], I need [capability] to [goal] | As a user, I need faster page loads to complete tasks without frustration |
| Bug Fix | As a [persona], I expect [behavior] when [condition] | As a user, I expect my cart to persist when I refresh the page |
| Enabler | As a developer, I need to [technical task] to enable [capability] | As a developer, I need to implement caching to enable instant search |

### Persona Reference

| Persona | Typical Needs | Context |
|---------|--------------|---------|
| End User | Efficiency, simplicity, reliability | Daily feature usage |
| Administrator | Control, visibility, security | System management |
| Power User | Automation, customization, shortcuts | Expert workflows |
| New User | Guidance, learning, safety | Onboarding |

---

## Acceptance Criteria Patterns

Write testable acceptance criteria using Given-When-Then format.

### Given-When-Then Template

```
Given [precondition/context],
When [action/trigger],
Then [expected outcome].
```

**Examples:**
```
Given the user is logged in with valid credentials,
When they click the "Export" button,
Then a PDF download starts within 2 seconds.

Given the user has entered an invalid email format,
When they submit the registration form,
Then an inline error message displays "Please enter a valid email address."

Given the shopping cart contains items,
When the user refreshes the browser,
Then the cart contents remain unchanged.
```

### Acceptance Criteria Checklist

Each story should include criteria for:

| Category | Example |
|----------|---------|
| Happy Path | Given valid input, When submitted, Then success message displayed |
| Validation | Should reject input when required field is empty |
| Error Handling | Must show user-friendly message when API fails |
| Performance | Should complete operation within 2 seconds |
| Accessibility | Must be navigable via keyboard only |

### Minimum Criteria by Story Size

| Story Points | Minimum AC Count |
|--------------|------------------|
| 1-2 | 3-4 criteria |
| 3-5 | 4-6 criteria |
| 8 | 5-8 criteria |
| 13+ | Split the story |

See `references/user-story-templates.md` for complete template library.

---

## Epic Breakdown Workflow

Break epics into deliverable sprint-sized stories:

1. Define epic scope and success criteria
2. Identify all personas affected by the epic
3. List all capabilities needed for each persona
4. Group capabilities into logical stories
5. Validate each story is ≤8 points
6. Identify dependencies between stories
7. Sequence stories for incremental delivery
8. **Validation:** Each story delivers standalone value; total stories cover epic scope

### Splitting Techniques

| Technique | When to Use | Example |
|-----------|-------------|---------|
| By workflow step | Linear process | "Checkout" → "Add to cart" + "Enter payment" + "Confirm order" |
| By persona | Multiple user types | "Dashboard" → "Admin dashboard" + "User dashboard" |
| By data type | Multiple inputs | "Import" → "Import CSV" + "Import Excel" |
| By operation | CRUD functionality | "Manage users" → "Create" + "Edit" + "Delete" |
| Happy path first | Risk reduction | "Feature" → "Basic flow" + "Error handling" + "Edge cases" |

### Epic Example

**Epic:** User Dashboard

**Breakdown:**
```
Epic: User Dashboard (34 points total)
├── US-001: View key metrics (5 pts) - End User
├── US-002: Customize layout (5 pts) - Power User
├── US-003: Export data to CSV (3 pts) - End User
├── US-004: Share with team (5 pts) - End User
├── US-005: Set up alerts (5 pts) - Power User
├── US-006: Filter by date range (3 pts) - End User
├── US-007: Admin overview (5 pts) - Admin
└── US-008: Enable caching (3 pts) - Enabler
```

---

## Sprint Planning Workflow

Plan sprint capacity and select stories:

1. Calculate team capacity (velocity × availability)
2. Review sprint goal with stakeholders
3. Select stories from prioritized backlog
4. Fill to 80-85% of capacity (committed)
5. Add stretch goals (10-15% additional)
6. Identify dependencies and risks
7. Break complex stories into tasks
8. **Validation:** Committed points ≤85% capacity; all stories have acceptance criteria

### Capacity Calculation

```
Sprint Capacity = Average Velocity × Availability Factor

Example:
Average Velocity: 30 points
Team availability: 90% (one member partially out)
Adjusted Capacity: 27 points

Committed: 23 points (85% of 27)
Stretch: 4 points (15% of 27)
```

### Availability Factors

| Scenario | Factor |
|----------|--------|
| Full sprint, no PTO | 1.0 |
| One team member out 50% | 0.9 |
| Holiday during sprint | 0.8 |
| Multiple members out | 0.7 |

### Sprint Loading Template

```
Sprint Capacity: 27 points
Sprint Goal: [Clear, measurable objective]

COMMITTED (23 points):
[H] US-001: User dashboard (5 pts)
[H] US-002: Export feature (3 pts)
[H] US-003: Search filter (5 pts)
[M] US-004: Settings page (5 pts)
[M] US-005: Help tooltips (3 pts)
[L] US-006: Theme options (2 pts)

STRETCH (4 points):
[L] US-007: Sort options (2 pts)
[L] US-008: Print view (2 pts)
```

See `references/sprint-planning-guide.md` for complete planning procedures.

---

## Backlog Prioritization

Prioritize backlog using value and effort assessment.

### Priority Levels

| Priority | Definition | Sprint Target |
|----------|------------|---------------|
| Critical | Blocking users, security, data loss | Immediate |
| High | Core functionality, key user needs | This sprint |
| Medium | Improvements, enhancements | Next 2-3 sprints |
| Low | Nice-to-have, minor improvements | Backlog |

### Prioritization Factors

| Factor | Weight | Questions |
|--------|--------|-----------|
| Business Value | 40% | Revenue impact? User demand? Strategic alignment? |
| User Impact | 30% | How many users? How frequently used? |
| Risk/Dependencies | 15% | Technical risk? External dependencies? |
| Effort | 15% | Size? Complexity? Uncertainty? |

### INVEST Criteria Validation

Before adding to sprint, validate each story:

| Criterion | Question | Pass If... |
|-----------|----------|------------|
| **I**ndependent | Can this be developed without other uncommitted stories? | No blocking dependencies |
| **N**egotiable | Is the implementation flexible? | Multiple approaches possible |
| **V**aluable | Does this deliver user or business value? | Clear benefit in "so that" |
| **E**stimable | Can the team estimate this? | Understood well enough to size |
| **S**mall | Can this complete in one sprint? | ≤8 story points |
| **T**estable | Can we verify this is done? | Clear acceptance criteria |

---

## Reference Documentation

### User Story Templates

`references/user-story-templates.md` contains:

- Standard story formats by type (feature, improvement, bug fix, enabler)
- Acceptance criteria patterns (Given-When-Then, Should/Must/Can)
- INVEST criteria validation checklist
- Story point estimation guide (Fibonacci scale)
- Common story antipatterns and fixes
- Story splitting techniques

### Sprint Planning Guide

`references/sprint-planning-guide.md` contains:

- Sprint planning meeting agenda
- Capacity calculation formulas
- Backlog prioritization framework (WSJF)
- Sprint ceremony guides (standup, review, retro)
- Velocity tracking and burndown patterns
- Definition of Done checklist
- Sprint metrics and targets

---

## Tools

### User Story Generator

```bash
# Generate stories from sample epic
python scripts/user_story_generator.py

# Plan sprint with capacity
python scripts/user_story_generator.py sprint 30
```

Generates:
- INVEST-compliant user stories
- Given-When-Then acceptance criteria
- Story point estimates (Fibonacci scale)
- Priority assignments
- Sprint loading with committed and stretch items

### Sample Output

```
USER STORY: USR-001
========================================
Title: View Key Metrics
Type: story
Priority: HIGH
Points: 5

Story:
As a End User, I want to view key metrics and KPIs
so that I can save time and work more efficiently

Acceptance Criteria:
  1. Given user has access, When they view key metrics, Then the result is displayed
  2. Should validate input before processing
  3. Must show clear error message when action fails
  4. Should complete within 2 seconds
  5. Must be accessible via keyboard navigation

INVEST Checklist:
  ✓ Independent
  ✓ Negotiable
  ✓ Valuable
  ✓ Estimable
  ✓ Small
  ✓ Testable
```

---

## Sprint Metrics

Track sprint health and team performance.

### Key Metrics

| Metric | Formula | Target |
|--------|---------|--------|
| Velocity | Points completed / sprint | Stable ±10% |
| Commitment Reliability | Completed / Committed | >85% |
| Scope Change | Points added or removed mid-sprint | <10% |
| Carryover | Points not completed | <15% |

### Velocity Tracking

```
Sprint 1: 25 points
Sprint 2: 28 points
Sprint 3: 30 points
Sprint 4: 32 points
Sprint 5: 29 points
------------------------
Average Velocity: 28.8 points
Trend: Stable

Planning: Commit to 24-26 points
```

### Definition of Done

Story is complete when:

- [ ] Code complete and peer reviewed
- [ ] Unit tests written and passing
- [ ] Acceptance criteria verified
- [ ] Documentation updated
- [ ] Deployed to staging environment
- [ ] Product Owner accepted
- [ ] No critical bugs remaining

## Related Skills

- **Scrum Master** (`project-management/scrum-master/`) — Velocity data and sprint ceremonies complement backlog management
- **Product Manager Toolkit** (`product-team/product-manager-toolkit/`) — RICE prioritization feeds backlog ordering
