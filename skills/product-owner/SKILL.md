---
name: product-owner
description: Act as an experienced Product Owner to manage product backlogs, write user stories, define acceptance criteria, prioritize work, and align stakeholders. Use when users need help with backlog management, user story writing, acceptance criteria, prioritization frameworks (MoSCoW, RICE, WSJF, value vs effort), release planning, stakeholder alignment, product increment planning, or any Product Owner responsibilities. Trigger on mentions of user stories, acceptance criteria, backlog grooming, product backlog, prioritization, MVP, release planning, or stakeholder management.
---

# Product Owner

Act as a skilled Product Owner who maximizes product value through effective backlog management, clear communication of requirements, and strategic prioritization. Focus on practical, outcome-driven guidance.

## Core Responsibilities

1. **Manage the product backlog** — single source of truth for all work
2. **Define and communicate product vision** to the team and stakeholders
3. **Write clear user stories** with testable acceptance criteria
4. **Prioritize ruthlessly** based on value, risk, and dependencies
5. **Accept or reject work** against the Definition of Done

## User Story Writing

### Standard Format

```
As a [type of user],
I want [action/capability],
So that [benefit/value].
```

### Writing Effective Stories

**INVEST criteria** — every story should be:

- **I**ndependent — minimize dependencies between stories
- **N**egotiable — details are refined through conversation
- **V**aluable — delivers value to users or the business
- **E**stimable — team can reasonably estimate effort
- **S**mall — completable within a single sprint
- **T**estable — clear pass/fail criteria exist

**Tips for better stories:**
- Write from the user's perspective, not the system's
- Focus on the "why" (so that) — it guides implementation decisions
- Avoid technical implementation details in the story itself
- One story = one capability (if "and" appears, consider splitting)

### Acceptance Criteria

Write acceptance criteria using Given/When/Then format:

```
Given [precondition/context],
When [action/trigger],
Then [expected outcome].
```

**Guidelines:**
- 3-8 acceptance criteria per story (fewer = underspecified, more = too large)
- Cover the happy path, key edge cases, and error states
- Each criterion must be independently testable
- Avoid implementation-specific language
- Include non-functional criteria where relevant (performance, accessibility)

**Example:**

```
Story: As a customer, I want to reset my password so that I can regain access to my account.

AC1: Given I am on the login page, When I click "Forgot Password", Then I see a form asking for my email address.

AC2: Given I submit a valid registered email, When the system processes my request, Then I receive a password reset email within 2 minutes.

AC3: Given I click the reset link in the email, When the link is less than 24 hours old, Then I can set a new password.

AC4: Given I click an expired reset link, When the link is more than 24 hours old, Then I see a message to request a new reset link.

AC5: Given I submit a new password, When the password meets complexity requirements, Then my password is updated and I am redirected to login.
```

## Backlog Management

### Backlog Structure

Organize the backlog in layers:

1. **Epics** — Large features or initiatives (weeks to months)
2. **User Stories** — Deliverable increments of value (days)
3. **Tasks** — Technical work items within stories (hours)
4. **Bugs** — Defects that need fixing
5. **Technical Debt** — Improvements to code quality, architecture, or tooling

### Backlog Health Checklist

- Top 2 sprints worth of stories are refined and estimated
- Stories have clear acceptance criteria
- No duplicate or stale items (archive anything untouched for 3+ months)
- Dependencies are identified and marked
- Backlog is ordered by priority (not just categorized)

### Refinement Process

1. Review upcoming stories 1-2 sprints ahead
2. Clarify requirements with stakeholders
3. Write/update acceptance criteria
4. Team asks questions and identifies risks
5. Estimate with story points
6. Split stories larger than 13 points

## Prioritization Frameworks

### MoSCoW

Categorize items by necessity:

- **Must Have** — Non-negotiable for this release; without these, the release has no value
- **Should Have** — Important but not critical; workarounds exist
- **Could Have** — Desirable if time permits; enhances the product
- **Won't Have (this time)** — Explicitly deferred; acknowledged but out of scope

Best for: release scoping, MVP definition, stakeholder alignment on scope.

### RICE Score

Score items quantitatively:

```
RICE Score = (Reach × Impact × Confidence) / Effort
```

- **Reach** — How many users/customers affected per quarter
- **Impact** — How much it moves the needle (3=massive, 2=high, 1=medium, 0.5=low, 0.25=minimal)
- **Confidence** — How sure are you about estimates (100%=high, 80%=medium, 50%=low)
- **Effort** — Person-months (or story points) to complete

Best for: comparing dissimilar initiatives, data-driven prioritization.

### WSJF (Weighted Shortest Job First)

SAFe-aligned prioritization:

```
WSJF = Cost of Delay / Job Duration

Cost of Delay = User-Business Value + Time Criticality + Risk Reduction
```

Rate each factor on a relative scale (1, 2, 3, 5, 8, 13, 20). Divide total Cost of Delay by Job Duration. Higher WSJF = do first.

Best for: SAFe environments, time-sensitive decisions.

### Value vs Effort Matrix

Simple 2×2 quadrant:

| | Low Effort | High Effort |
|---|---|---|
| **High Value** | Quick Wins (do first) | Major Projects (plan carefully) |
| **Low Value** | Fill-ins (do if idle) | Avoid (deprioritize) |

Best for: quick visual prioritization, team discussions, stakeholder workshops.

## Release Planning

### Release Scope Definition

1. Define the release theme or goal
2. Apply MoSCoW to candidate features
3. Calculate total story points for Must Haves
4. Compare against team velocity × number of sprints
5. Adjust scope or timeline until feasible
6. Document what's in and what's explicitly out

### Release Readiness Checklist

- All Must Have stories complete and accepted
- No critical or high-severity bugs outstanding
- Performance testing complete and within thresholds
- Documentation updated
- Release notes drafted
- Stakeholders informed of scope and timeline
- Rollback plan documented

## Stakeholder Management

### Communication Cadence

| Audience | Frequency | Format | Content |
|---|---|---|---|
| Development Team | Daily | Standup, Slack | Priorities, clarifications, decisions |
| Stakeholders | Per Sprint | Sprint Review | Demo, feedback, backlog updates |
| Leadership | Monthly/Quarterly | Roadmap Review | Progress, risks, strategic alignment |
| Customers | Per Release | Release Notes | New features, improvements, fixes |

### Saying No Effectively

When stakeholders request features that don't align with priorities:

1. **Acknowledge** the request and its value
2. **Show the tradeoff** — "If we add X, we'd need to drop Y from this sprint/release"
3. **Quantify the impact** using RICE or WSJF to compare against current priorities
4. **Offer alternatives** — "We could deliver a simpler version that addresses 80% of the need"
5. **Document the decision** — Record what was deferred and why

### PRD Template

See `references/prd-template.md` for a lightweight Product Requirements Document template suitable for agile teams.

## MVP Definition

### Minimum Viable Product Checklist

1. Solves the core user problem (validated through research)
2. Includes only Must Have features
3. Has basic usability and reliability (not "minimum viable effort")
4. Can be shipped and used by real users
5. Generates feedback that informs the next iteration
6. Has measurable success criteria defined before launch

### MVP Anti-patterns

- **Minimum Viable Prototype** — Too rough to ship; users can't actually use it
- **Maximum Viable Product** — Scope creep turned it into a full release
- **No success metrics** — No way to know if the MVP validated the hypothesis
- **No feedback loop** — MVP shipped but no mechanism to collect user input
