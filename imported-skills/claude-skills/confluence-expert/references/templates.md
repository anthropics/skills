# Confluence Page Templates

## Meeting Notes Template

```markdown
# [Meeting Title] - [Date]

**Date:** [YYYY-MM-DD]
**Time:** [HH:MM - HH:MM]
**Location:** [Room/Video link]
**Attendees:** @[Name1], @[Name2], @[Name3]
**Note Taker:** @[Name]

## Agenda
1. [Topic 1]
2. [Topic 2]
3. [Topic 3]

## Discussion

### [Topic 1]
**Summary:**
[Key points discussed]

**Decisions:**
- [Decision 1]
- [Decision 2]

**Action Items:**
- [ ] [Action] - @[Owner] - [Due Date]
- [ ] [Action] - @[Owner] - [Due Date]

### [Topic 2]
**Summary:**
[Key points discussed]

**Decisions:**
- [Decision 1]

**Action Items:**
- [ ] [Action] - @[Owner] - [Due Date]

## Parking Lot
- [Item to discuss later]
- [Future topic]

## Next Meeting
**Date:** [YYYY-MM-DD]
**Agenda Topics:**
- [Topic 1]
- [Topic 2]
```

---

## Decision Log Template

```markdown
# [Decision Title]

| Field | Value |
|-------|-------|
| **Status** | 🟢 Accepted / 🟡 Proposed / 🔴 Deprecated |
| **Date** | [YYYY-MM-DD] |
| **Deciders** | @[Name1], @[Name2] |
| **Stakeholders** | @[Name3], @[Name4] |
| **Related Decisions** | [Link to related decisions] |

## Context and Problem Statement
[Describe the context and problem that requires a decision. 2-3 paragraphs explaining:
- What situation led to this decision?
- What problem are we trying to solve?
- What constraints exist?]

## Decision
[Clearly state the decision made in 1-2 sentences]

### Details
[Provide additional details about the decision:
- What exactly will we do?
- How will it be implemented?
- What timeline?]

## Rationale
[Explain why this decision was made:
- What were the key factors?
- What evidence supports this?
- Why is this the best choice?]

## Consequences

### Positive Consequences
- ✅ [Benefit 1]
- ✅ [Benefit 2]
- ✅ [Benefit 3]

### Negative Consequences / Trade-offs
- ⚠️ [Trade-off 1]
- ⚠️ [Trade-off 2]

### Risks
- 🔴 [Risk 1] - Mitigation: [How we'll handle it]
- 🟡 [Risk 2] - Mitigation: [How we'll handle it]

## Alternatives Considered

### Alternative 1: [Name]
**Description:** [What is this alternative?]

**Pros:**
- [Pro 1]
- [Pro 2]

**Cons:**
- [Con 1]
- [Con 2]

**Why Not Chosen:** [Reason]

### Alternative 2: [Name]
[Same structure as above]

## Implementation Plan
1. [Step 1] - @[Owner] - [Date]
2. [Step 2] - @[Owner] - [Date]
3. [Step 3] - @[Owner] - [Date]

## Success Metrics
- [Metric 1]: [Target]
- [Metric 2]: [Target]

## Review Date
**Next Review:** [YYYY-MM-DD]
**Review Notes:** [Link to review page]

## References
- [Link 1]
- [Link 2]
- [Link 3]

---
*Updated: [Date] by @[Name]*
```

---

## Technical Specification Template

```markdown
# [Feature/Component Name] Technical Specification

| Field | Value |
|-------|-------|
| **Status** | 🟡 Draft / 🟢 Approved / 🔴 Archived |
| **Author** | @[Name] |
| **Reviewers** | @[Name1], @[Name2] |
| **Date Created** | [YYYY-MM-DD] |
| **Last Updated** | [YYYY-MM-DD] |
| **JIRA Epic** | [ABC-123](link) |

## Overview
[1-2 paragraph summary of what this spec covers and why it matters]

## Goals and Non-Goals

### Goals
- [Goal 1]
- [Goal 2]
- [Goal 3]

### Non-Goals (Out of Scope)
- [Non-goal 1]
- [Non-goal 2]

## Background
[Context needed to understand this spec:
- What problem are we solving?
- What's the current state?
- Why now?]

## High-Level Design

### Architecture Diagram
[Insert diagram here]

### System Components
1. **[Component 1 Name]**
   - Purpose: [What it does]
   - Technology: [What it uses]
   - Interfaces: [How it connects]

2. **[Component 2 Name]**
   - Purpose: [What it does]
   - Technology: [What it uses]
   - Interfaces: [How it connects]

### Data Flow
[Describe how data flows through the system]

## Detailed Design

### Component 1: [Name]
**Purpose:** [Detailed purpose]

**Responsibilities:**
- [Responsibility 1]
- [Responsibility 2]

**API/Interface:**
```
[API spec or interface definition]
```

**Data Model:**
```
[Schema or data structure]
```

**Key Algorithms/Logic:**
[Describe any complex logic]

### Component 2: [Name]
[Same structure as Component 1]

## Database Schema

### Table: [table_name]
| Column | Type | Constraints | Description |
|--------|------|-------------|-------------|
| id | UUID | PRIMARY KEY | Unique identifier |
| name | VARCHAR(255) | NOT NULL | Entity name |
| created_at | TIMESTAMP | NOT NULL | Creation timestamp |

### Indexes
- `idx_name` on `name` - For fast lookups
- `idx_created` on `created_at` - For temporal queries

## API Specification

### Endpoint: [Method] /api/path
**Purpose:** [What this endpoint does]

**Request:**
```json
{
  "param1": "value",
  "param2": 123
}
```

**Response:**
```json
{
  "result": "success",
  "data": {}
}
```

**Error Handling:**
- 400: [Reason]
- 404: [Reason]
- 500: [Reason]

## Security Considerations
- [Security consideration 1]
- [Security consideration 2]
- [Authentication/Authorization approach]
- [Data encryption requirements]

## Performance Considerations
- [Expected load/throughput]
- [Scalability approach]
- [Caching strategy]
- [Performance targets]

## Testing Strategy

### Unit Tests
- [Test area 1]
- [Test area 2]

### Integration Tests
- [Test scenario 1]
- [Test scenario 2]

### Performance Tests
- [Load test plan]
- [Performance benchmarks]

## Deployment Plan
1. [Deployment step 1]
2. [Deployment step 2]
3. [Deployment step 3]

### Rollback Plan
[How to revert if issues occur]

## Monitoring and Alerting
- [Metric 1] - Alert threshold: [Value]
- [Metric 2] - Alert threshold: [Value]
- [Log tracking]

## Migration Plan (if applicable)
[How to migrate from current system]

## Dependencies
- [Dependency 1] - Why needed
- [Dependency 2] - Why needed

## Open Questions
- [ ] [Question 1] - @[Owner]
- [ ] [Question 2] - @[Owner]

## Future Considerations
- [Future enhancement 1]
- [Future enhancement 2]

## References
- [Link to related specs]
- [Link to design docs]
- [Link to JIRA epics]

---
*For questions, contact @[Author]*
```

---

## How-To Guide Template

```markdown
# How to [Task Name]

## Overview
[1-2 sentences explaining what this guide covers and who it's for]

**Estimated Time:** [X minutes]
**Difficulty:** [Beginner/Intermediate/Advanced]

## Prerequisites
Before you begin, ensure you have:
- [ ] [Prerequisite 1]
- [ ] [Prerequisite 2]
- [ ] [Prerequisite 3]

## Quick Summary (TL;DR)
[One paragraph with the essence of the guide for those who just need a reminder]

## Step-by-Step Instructions

### Step 1: [Action]
[Detailed description of what to do]

**Commands/Code:**
```bash
command here
```

**Expected Result:**
[What you should see if it worked]

**Screenshot:**
[Add screenshot if helpful]

### Step 2: [Action]
[Detailed description]

**Tips:**
- 💡 [Helpful tip]
- ⚠️ [Warning about common mistake]

### Step 3: [Action]
[Continue pattern...]

## Verification
To verify everything worked:
1. [Check 1]
2. [Check 2]

## Troubleshooting

### Problem: [Common issue]
**Symptoms:** [What you see]
**Cause:** [Why it happens]
**Solution:**
1. [Fix step 1]
2. [Fix step 2]

### Problem: [Another issue]
[Same structure as above]

## Best Practices
- [Best practice 1]
- [Best practice 2]
- [Best practice 3]

## Related Guides
- [Link to related guide 1]
- [Link to related guide 2]

## Need Help?
- Questions? Ask in #[channel]
- Issues? Create ticket in [JIRA project]
- Contact: @[Expert name]

---
*Last updated: [Date] by @[Name]*
```

---

## Requirements Document Template

```markdown
# [Feature/Project Name] Requirements

| Field | Value |
|-------|-------|
| **Status** | 🟡 Draft / 🟢 Approved / 🔵 In Progress / ✅ Complete |
| **Product Owner** | @[Name] |
| **Stakeholders** | @[Name1], @[Name2] |
| **Target Release** | [Release version] |
| **JIRA Epic** | [ABC-123](link) |
| **Created** | [YYYY-MM-DD] |
| **Last Updated** | [YYYY-MM-DD] |

## Executive Summary
[2-3 sentences describing the feature and its business value]

## Business Goals
- [Goal 1]: [Metric]
- [Goal 2]: [Metric]
- [Goal 3]: [Metric]

## User Stories

### Story 1: [Title]
**As a** [user type]
**I want** [goal]
**So that** [benefit]

**Acceptance Criteria:**
- [ ] [Criterion 1]
- [ ] [Criterion 2]
- [ ] [Criterion 3]

**Priority:** [High/Medium/Low]
**Effort:** [Story points]

### Story 2: [Title]
[Same structure as Story 1]

## Functional Requirements

### FR-001: [Requirement Title]
**Description:** [What the system must do]

**Rationale:** [Why this is needed]

**Acceptance Criteria:**
- [Criterion 1]
- [Criterion 2]

**Priority:** [Must Have / Should Have / Could Have / Won't Have]

### FR-002: [Requirement Title]
[Same structure as FR-001]

## Non-Functional Requirements

### Performance
- [Requirement 1]
- [Requirement 2]

### Security
- [Requirement 1]
- [Requirement 2]

### Scalability
- [Requirement 1]
- [Requirement 2]

### Accessibility
- [Requirement 1]
- [Requirement 2]

## User Experience

### Wireframes
[Insert wireframes or link to Figma]

### User Flow
[Diagram showing user journey]

### UI Requirements
- [UI requirement 1]
- [UI requirement 2]

## Technical Constraints
- [Constraint 1]
- [Constraint 2]
- [Constraint 3]

## Dependencies
| Dependency | Owner | Status | Impact if Blocked |
|------------|-------|--------|-------------------|
| [Dep 1] | @[Name] | 🟢 Ready | [Impact] |
| [Dep 2] | @[Name] | 🟡 In Progress | [Impact] |

## Success Metrics
| Metric | Baseline | Target | How Measured |
|--------|----------|--------|--------------|
| [Metric 1] | [Current] | [Goal] | [Method] |
| [Metric 2] | [Current] | [Goal] | [Method] |

## Risks and Mitigations
| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| [Risk 1] | High | Medium | [Strategy] |
| [Risk 2] | Medium | Low | [Strategy] |

## Out of Scope
- [Explicitly excluded 1]
- [Explicitly excluded 2]

## Open Questions
- [ ] [Question 1] - @[Owner] - [Due date]
- [ ] [Question 2] - @[Owner] - [Due date]

## Timeline
| Phase | Start Date | End Date | Deliverables |
|-------|-----------|----------|--------------|
| Design | [Date] | [Date] | [Deliverable] |
| Development | [Date] | [Date] | [Deliverable] |
| Testing | [Date] | [Date] | [Deliverable] |
| Launch | [Date] | [Date] | [Deliverable] |

## Approval

### Reviewers
- [ ] Product Owner: @[Name]
- [ ] Engineering Lead: @[Name]
- [ ] Design Lead: @[Name]
- [ ] Stakeholder: @[Name]

**Approved Date:** [YYYY-MM-DD]

## References
- [Market research]
- [User feedback]
- [Technical specs]
- [Related features]

---
*For questions, contact @[Product Owner]*
```

---

## Retrospective Template

```markdown
# Sprint [N] Retrospective - [Team Name]

**Date:** [YYYY-MM-DD]
**Sprint:** [Sprint N]
**Sprint Dates:** [Start Date] - [End Date]
**Facilitator:** @[Name]
**Participants:** @[Name1], @[Name2], @[Name3]

## Sprint Metrics
- **Velocity:** [X points] (Average: [Y points])
- **Committed:** [X points / N issues]
- **Completed:** [Y points / M issues]
- **Sprint Goal Met:** ✅ Yes / ❌ No

## What Went Well 😊
- [Positive 1]
- [Positive 2]
- [Positive 3]

## What Didn't Go Well 😞
- [Challenge 1]
- [Challenge 2]
- [Challenge 3]

## Action Items from Last Retro
- [✅ / ❌] [Action item 1] - @[Owner]
  - Status: [Done / In Progress / Not Done]
  - Notes: [Update]
- [✅ / ❌] [Action item 2] - @[Owner]
  - Status: [Done / In Progress / Not Done]
  - Notes: [Update]

## Discussion Themes

### Theme 1: [Topic]
**What we discussed:**
[Summary of discussion]

**Root cause:**
[What's really causing this issue?]

**Ideas for improvement:**
- [Idea 1]
- [Idea 2]

### Theme 2: [Topic]
[Same structure as Theme 1]

## Action Items for Next Sprint
| Action | Owner | Due Date | Success Criteria |
|--------|-------|----------|------------------|
| [Action 1] | @[Name] | [Date] | [How we know it's done] |
| [Action 2] | @[Name] | [Date] | [How we know it's done] |
| [Action 3] | @[Name] | [Date] | [How we know it's done] |

## Shout-Outs 🎉
- @[Name] for [what they did]
- @[Name] for [what they did]

## Notes
[Any additional notes or observations]

---
*Next Retrospective: [Date]*
```

---

## Status Report Template

```markdown
# [Project Name] Status Report - [Week of Date]

**Report Date:** [YYYY-MM-DD]
**Reporting Period:** [Start Date] - [End Date]
**Project Manager:** @[Name]
**Overall Status:** 🟢 On Track / 🟡 At Risk / 🔴 Off Track

## Executive Summary
[2-3 sentences: What's the current state? What are the key achievements? What needs attention?]

## Project Health

| Metric | Status | Details |
|--------|--------|---------|
| **Scope** | 🟢 / 🟡 / 🔴 | [Comment] |
| **Schedule** | 🟢 / 🟡 / 🔴 | [Comment] |
| **Budget** | 🟢 / 🟡 / 🔴 | [Comment] |
| **Quality** | 🟢 / 🟡 / 🔴 | [Comment] |
| **Team Morale** | 🟢 / 🟡 / 🔴 | [Comment] |

## Key Accomplishments
- ✅ [Accomplishment 1]
- ✅ [Accomplishment 2]
- ✅ [Accomplishment 3]

## Milestones Status

| Milestone | Target Date | Status | Actual/Forecast | Notes |
|-----------|-------------|--------|-----------------|-------|
| [Milestone 1] | [Date] | ✅ Complete | [Date] | [Notes] |
| [Milestone 2] | [Date] | 🔄 In Progress | On track | [Notes] |
| [Milestone 3] | [Date] | ⏳ Not Started | [Forecast] | [Notes] |

## Active Risks

### 🔴 Critical Risks
| Risk | Impact | Mitigation | Owner | Status |
|------|--------|------------|-------|--------|
| [Risk 1] | High | [Strategy] | @[Name] | [Update] |

### 🟡 Medium Risks
| Risk | Impact | Mitigation | Owner | Status |
|------|--------|------------|-------|--------|
| [Risk 2] | Medium | [Strategy] | @[Name] | [Update] |

## Issues & Blockers

### 🚨 Blockers
- [Blocker 1] - @[Owner] - **Escalated to:** [Person]
  - Impact: [What's blocked]
  - ETA to resolve: [Date]

### ⚠️ Issues
- [Issue 1] - @[Owner]
  - Status: [Update]

## Upcoming in Next Period
- [Activity 1]
- [Activity 2]
- [Activity 3]

## Budget Update (if applicable)
- **Total Budget:** [Amount]
- **Spent to Date:** [Amount] ([%])
- **Forecast to Complete:** [Amount]
- **Variance:** [Amount] ([%])

## Decisions Needed
| Decision | Why Needed | Deadline | Stakeholder |
|----------|-----------|----------|-------------|
| [Decision 1] | [Reason] | [Date] | @[Name] |

## Team Update
- **Current Team Size:** [N people]
- **Open Positions:** [N] ([Roles])
- **Recent Additions:** @[Name] - [Role]
- **Upcoming Departures:** [Names/Dates]

## Metrics (if applicable)
| Metric | This Period | Last Period | Trend | Target |
|--------|-------------|-------------|-------|--------|
| [Metric 1] | [Value] | [Value] | ↗️ / ↘️ / → | [Target] |
| [Metric 2] | [Value] | [Value] | ↗️ / ↘️ / → | [Target] |

## Links
- [Jira Project](link)
- [Roadmap](link)
- [Technical Docs](link)

---
*Next Status Report: [Date]*
```
