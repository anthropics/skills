# Progress Tracking

## Update Frequency

### Daily Updates

For active implementation work:

**What to update**:
- Task status if changed
- Add progress note to task
- Update blockers

**When**:
- End of work day
- After completing significant work
- When encountering blockers

### Milestone Updates

For phase/milestone completion:

**What to update**:
- Mark phase complete in plan
- Add milestone summary
- Update timeline if needed
- Report to stakeholders

**When**:
- Phase completion
- Major deliverable ready
- Sprint end
- Release

### Status Change Updates

For task state transitions:

**What to update**:
- Task status property
- Add transition note
- Notify relevant people

**When**:
- Start work (To Do → In Progress)
- Ready for review (In Progress → In Review)
- Complete (In Review → Done)
- Block (Any → Blocked)

## Progress Note Format

### Daily Progress Note

```markdown
## Progress: [Date]

### Completed
- [Specific accomplishment with details]
- [Specific accomplishment with details]

### In Progress
- [Current work item]
- Current status: [Percentage or description]

### Next Steps
1. [Next planned action]
2. [Next planned action]

### Blockers
- [Blocker description and who/what needed to unblock]
- Or: None

### Decisions Made
- [Any technical/product decisions]

### Notes
[Additional context, learnings, issues encountered]
```

Example:

```markdown
## Progress: Oct 14, 2025

### Completed
- Implemented user authentication API endpoints (login, logout, refresh)
- Added JWT token generation and validation
- Wrote unit tests for auth service (95% coverage)

### In Progress
- Frontend login form integration
- Currently: Form submits but need to handle error states

### Next Steps
1. Complete error handling in login form
2. Add loading states
3. Implement "remember me" functionality

### Blockers
None

### Decisions Made
- Using HttpOnly cookies for refresh tokens (more secure than localStorage)
- Session timeout set to 24 hours based on security review

### Notes
- Found edge case with concurrent login attempts, added to backlog
- Performance of auth check is good (<10ms)
```

### Milestone Summary

```markdown
## Phase [N] Complete: [Date]

### Overview
[Brief description of what was accomplished in this phase]

### Completed Tasks
- <mention-page url="...">Task 1</mention-page> ✅
- <mention-page url="...">Task 2</mention-page> ✅
- <mention-page url="...">Task 3</mention-page> ✅

### Deliverables
- [Deliverable 1]: [Link/description]
- [Deliverable 2]: [Link/description]

### Key Accomplishments
- [Major achievement]
- [Major achievement]

### Metrics
- [Relevant metric]: [Value]
- [Relevant metric]: [Value]

### Challenges Overcome
- [Challenge and how it was solved]

### Learnings
**What went well**:
- [Success factor]

**What to improve**:
- [Area for improvement]

### Impact on Timeline
- On schedule / [X days ahead/behind]
- Reason: [If deviation, explain why]

### Next Phase
- **Starting**: [Next phase name]
- **Target start date**: [Date]
- **Focus**: [Main objectives]
```

## Updating Implementation Plan

### Progress Indicators

Update plan page regularly:

```markdown
## Status Overview

**Overall Progress**: 45% complete

### Phase Status
- ✅ Phase 1: Foundation - Complete
- 🔄 Phase 2: Core Features - In Progress (60%)
- ⏳ Phase 3: Integration - Not Started

### Task Summary
- ✅ Completed: 12 tasks
- 🔄 In Progress: 5 tasks
- 🚧 Blocked: 1 task
- ⏳ Not Started: 8 tasks

**Last Updated**: [Date]
```

### Task Checklist Updates

Mark completed tasks:

```markdown
## Implementation Phases

### Phase 1: Foundation
- [x] <mention-page url="...">Database schema</mention-page>
- [x] <mention-page url="...">API scaffolding</mention-page>
- [x] <mention-page url="...">Auth setup</mention-page>

### Phase 2: Core Features
- [x] <mention-page url="...">User management</mention-page>
- [ ] <mention-page url="...">Dashboard</mention-page>
- [ ] <mention-page url="...">Reporting</mention-page>
```

### Timeline Updates

Update milestone dates:

```markdown
## Timeline

| Milestone | Original | Current | Status |
|-----------|----------|---------|--------|
| Phase 1 | Oct 15 | Oct 14 | ✅ Complete (1 day early) |
| Phase 2 | Oct 30 | Nov 2 | 🔄 In Progress (3 days delay) |
| Phase 3 | Nov 15 | Nov 18 | ⏳ Planned (adjusted) |
| Launch | Nov 20 | Nov 22 | ⏳ Planned (adjusted) |

**Timeline Status**: Slightly behind due to [reason]
```

## Task Status Tracking

### Status Definitions

**To Do**: Not started
- Task is ready to begin
- Dependencies met
- Assigned (or available)

**In Progress**: Actively being worked
- Work has started
- Assigned to someone
- Regular updates expected

**Blocked**: Cannot proceed
- Dependency not met
- External blocker
- Waiting on decision/resource

**In Review**: Awaiting review
- Work complete from implementer perspective
- Needs code review, QA, or approval
- Reviewers identified

**Done**: Complete
- All acceptance criteria met
- Reviewed and approved
- Deployed/delivered

### Updating Task Status

When updating:

```
1. Update Status property
2. Add progress note explaining change
3. Update related tasks if needed
4. Notify relevant people via comment

Example:
properties: { "Status": "In Progress" }

Content update:
## Progress: Oct 14, 2025
Started implementation. Set up basic structure and wrote initial tests.
```

## Blocker Tracking

### Recording Blockers

When encountering a blocker:

```markdown
## Blockers

### [Date]: [Blocker Description]
**Status**: 🚧 Active
**Impact**: [What's blocked]
**Needed to unblock**: [Action/person/decision needed]
**Owner**: [Who's responsible for unblocking]
**Target resolution**: [Date or timeframe]
```

### Resolving Blockers

When unblocked:

```markdown
## Blockers

### [Date]: [Blocker Description]
**Status**: ✅ Resolved on [Date]
**Resolution**: [How it was resolved]
**Impact**: [Any timeline/scope impact]
```

### Escalating Blockers

If blocker needs escalation:

```
1. Update blocker status in task
2. Add comment tagging stakeholder
3. Update plan with blocker impact
4. Propose mitigation if possible
```

## Metrics Tracking

### Velocity Tracking

Track completion rate:

```markdown
## Velocity

### Week 1
- Tasks completed: 8
- Story points: 21
- Velocity: Strong

### Week 2
- Tasks completed: 6
- Story points: 18
- Velocity: Moderate (1 blocker)

### Week 3
- Tasks completed: 9
- Story points: 24
- Velocity: Strong (blocker resolved)
```

### Quality Metrics

Track quality indicators:

```markdown
## Quality Metrics

- Test coverage: 87%
- Code review approval rate: 95%
- Bug count: 3 (2 minor, 1 cosmetic)
- Performance: All targets met
- Security: No issues found
```

### Progress Metrics

Quantitative progress:

```markdown
## Progress Metrics

- Requirements implemented: 15/20 (75%)
- Acceptance criteria met: 42/56 (75%)
- Test cases passing: 128/135 (95%)
- Code complete: 80%
- Documentation: 60%
```

## Stakeholder Communication

### Weekly Status Report

```markdown
## Weekly Status: [Week of Date]

### Summary
[One paragraph overview of progress and status]

### This Week's Accomplishments
- [Key accomplishment]
- [Key accomplishment]
- [Key accomplishment]

### Next Week's Plan
- [Planned work]
- [Planned work]

### Status
- On track / At risk / Behind schedule
- [If at risk or behind, explain and provide mitigation plan]

### Blockers & Needs
- [Active blocker or need for help]
- Or: None

### Risks
- [New or evolving risk]
- Or: None currently identified
```

### Executive Summary

For leadership updates:

```markdown
## Implementation Status: [Feature Name]

**Overall Status**: 🟢 On Track / 🟡 At Risk / 🔴 Behind

**Progress**: [X]% complete

**Key Updates**:
- [Most important update]
- [Most important update]

**Timeline**: [Status vs original plan]

**Risks**: [Top 1-2 risks]

**Next Milestone**: [Upcoming milestone and date]
```

## Automated Progress Tracking

### Query-Based Status

Generate status from task database:

```
Query task database:
SELECT 
  "Status",
  COUNT(*) as count
FROM "collection://tasks-uuid"
WHERE "Related Tasks" CONTAINS 'plan-page-id'
GROUP BY "Status"

Generate summary:
- To Do: 8
- In Progress: 5
- Blocked: 1
- In Review: 2
- Done: 12

Overall: 44% complete (12/28 tasks)
```

### Timeline Calculation

Calculate projected completion:

```
Average velocity: 6 tasks/week
Remaining tasks: 14
Projected completion: 2.3 weeks from now

Compares to target: [On schedule/Behind/Ahead]
```

## Best Practices

1. **Update regularly**: Don't let updates pile up
2. **Be specific**: "Completed login" vs "Made progress"
3. **Quantify progress**: Use percentages, counts, metrics
4. **Note blockers immediately**: Don't wait to report blockers
5. **Link to work**: Reference PRs, deployments, demos
6. **Track decisions**: Document why, not just what
7. **Be honest**: Report actual status, not optimistic status
8. **Update in one place**: Keep implementation plan as source of truth

