# Task Creation from Specs

## Finding the Task Database

Before creating tasks, locate the task database:

```
1. Search for task database:
   Notion:notion-search
   query: "Tasks" or "Task Management" or "[Project] Tasks"
   
2. Fetch database schema:
   Notion:notion-fetch
   id: "database-id-from-search"
   
3. Identify data source:
   - Look for <data-source url="collection://..."> tags
   - Extract collection ID for parent parameter
   
4. Note schema:
   - Required properties
   - Property types and options
   - Relation properties for linking

Example:
Notion:notion-search
query: "Engineering Tasks"
query_type: "internal"

Notion:notion-fetch
id: "tasks-database-id"
```

Result: `collection://abc-123-def` for use as parent

## Task Breakdown Strategy

### Size Guidelines

**Good task size**:
- Completable in 1-2 days
- Single clear deliverable
- Independently testable
- Minimal dependencies

**Too large**:
- Takes > 3 days
- Multiple deliverables
- Many dependencies
- Break down further

**Too small**:
- Takes < 2 hours
- Too granular
- Group with related work

### Granularity by Phase

**Early phases**: Larger tasks acceptable
- "Design database schema"
- "Set up API structure"

**Middle phases**: Medium-sized tasks
- "Implement user authentication"
- "Build dashboard UI"

**Late phases**: Smaller, precise tasks
- "Fix validation bug in form"
- "Add loading state to button"

## Task Creation Pattern

For each requirement or work item:

```
1. Identify the work
2. Determine task size
3. Create task in database
4. Set properties
5. Write task description
6. Link to spec/plan
```

### Creating Task

```
Use Notion:notion-create-pages:

parent: {
  type: "data_source_id",
  data_source_id: "collection://tasks-db-uuid"
}

properties: {
  "[Title Property]": "Task: [Clear task name]",
  "Status": "To Do",
  "Priority": "[High/Medium/Low]",
  "[Project/Related]": ["spec-page-id", "plan-page-id"],
  "Assignee": "[Person]" (if known),
  "date:Due Date:start": "[Date]" (if applicable),
  "date:Due Date:is_datetime": 0
}

content: "[Task description using template]"
```

## Task Description Template

```markdown
# [Task Name]

## Context
Implementation task for <mention-page url="...">Feature Spec</mention-page>

Part of <mention-page url="...">Implementation Plan</mention-page> - Phase [N]

## Objective
[What this task accomplishes]

## Requirements
Based on spec requirements:
- [Relevant requirement 1]
- [Relevant requirement 2]

## Acceptance Criteria
- [ ] [Specific, testable criterion]
- [ ] [Specific, testable criterion]
- [ ] [Specific, testable criterion]

## Technical Approach
[Suggested implementation approach]

### Components Affected
- [Component 1]
- [Component 2]

### Key Decisions
- [Decision point 1]
- [Decision point 2]

## Dependencies

### Blocked By
- <mention-page url="...">Prerequisite Task</mention-page> or None

### Blocks
- <mention-page url="...">Dependent Task</mention-page> or None

## Resources
- [Link to design mockup]
- [Link to API spec]
- [Link to relevant code]

## Estimated Effort
[Time estimate]

## Progress
[To be updated during implementation]
```

## Task Types

### Infrastructure/Setup Tasks

```
Title: "Setup: [What's being set up]"
Examples:
- "Setup: Configure database connection pool"
- "Setup: Initialize authentication middleware"
- "Setup: Create CI/CD pipeline"

Focus: Getting environment/tooling ready
```

### Feature Implementation Tasks

```
Title: "Implement: [Feature name]"
Examples:
- "Implement: User login flow"
- "Implement: File upload functionality"
- "Implement: Dashboard widget"

Focus: Building specific functionality
```

### Integration Tasks

```
Title: "Integrate: [What's being integrated]"
Examples:
- "Integrate: Connect frontend to API"
- "Integrate: Add payment provider"
- "Integrate: Link user profile to dashboard"

Focus: Connecting components
```

### Testing Tasks

```
Title: "Test: [What's being tested]"
Examples:
- "Test: Write unit tests for auth service"
- "Test: E2E testing for checkout flow"
- "Test: Performance testing for API"

Focus: Validation and quality assurance
```

### Documentation Tasks

```
Title: "Document: [What's being documented]"
Examples:
- "Document: API endpoints"
- "Document: Setup instructions"
- "Document: Architecture decisions"

Focus: Creating documentation
```

### Bug Fix Tasks

```
Title: "Fix: [Bug description]"
Examples:
- "Fix: Login error on Safari"
- "Fix: Memory leak in image processing"
- "Fix: Race condition in payment flow"

Focus: Resolving issues
```

### Refactoring Tasks

```
Title: "Refactor: [What's being refactored]"
Examples:
- "Refactor: Extract auth logic to service"
- "Refactor: Optimize database queries"
- "Refactor: Simplify component hierarchy"

Focus: Code quality improvement
```

## Sequencing Tasks

### Critical Path

Identify must-happen-first tasks:

```
1. Database schema
2. API foundation
3. Core business logic
4. Frontend integration
5. Testing
6. Deployment
```

### Parallel Tracks

Tasks that can happen simultaneously:

```
Track A: Backend development
- API endpoints
- Business logic
- Database operations

Track B: Frontend development
- UI components
- State management
- Routing

Track C: Infrastructure
- CI/CD setup
- Monitoring
- Documentation
```

### Phase-Based Sequencing

Group by implementation phase:

```
Phase 1 (Foundation):
- Setup tasks
- Infrastructure tasks

Phase 2 (Core):
- Feature implementation tasks
- Integration tasks

Phase 3 (Polish):
- Testing tasks
- Documentation tasks
- Optimization tasks
```

## Priority Assignment

### P0/Critical
- Blocks everything else
- Core functionality
- Security requirements
- Data integrity

### P1/High
- Important features
- User-facing functionality
- Performance requirements

### P2/Medium
- Nice-to-have features
- Optimizations
- Minor improvements

### P3/Low
- Future enhancements
- Edge case handling
- Cosmetic improvements

## Estimation

### Story Points

If using story points:
- 1 point: Few hours
- 2 points: Half day
- 3 points: Full day
- 5 points: 2 days
- 8 points: 3-4 days (consider breaking down)

### Time Estimates

Direct time estimates:
- 2-4 hours: Small task
- 1 day: Medium task
- 2 days: Large task
- 3+ days: Break down further

### Estimation Factors

Consider:
- Complexity
- Unknowns
- Dependencies
- Testing requirements
- Documentation needs

## Task Relationships

### Parent Task Pattern

For large features:

```
Parent: "Feature: User Authentication"
Children:
- "Setup: Configure auth library"
- "Implement: Login flow"
- "Implement: Password reset"
- "Test: Auth functionality"
```

### Dependency Chain Pattern

For sequential work:

```
Task A: "Design database schema"
↓ (blocks)
Task B: "Implement data models"
↓ (blocks)
Task C: "Create API endpoints"
↓ (blocks)
Task D: "Integrate with frontend"
```

### Related Tasks Pattern

For parallel work:

```
Central: "Feature: Dashboard"
Related:
- "Backend API for dashboard data"
- "Frontend dashboard component"
- "Dashboard data caching"
```

## Bulk Task Creation

When creating many tasks:

```
For each work item in breakdown:
  1. Determine task properties
  2. Create task page
  3. Link to spec/plan
  4. Set relationships

Then:
  1. Update plan with task links
  2. Review sequencing
  3. Assign tasks (if known)
```

## Task Naming Conventions

**Be specific**:
✓ "Implement user login with email/password"
✗ "Add login"

**Include context**:
✓ "Dashboard: Add revenue chart widget"
✗ "Add chart"

**Use action verbs**:
- Implement, Build, Create
- Integrate, Connect, Link
- Fix, Resolve, Debug
- Test, Validate, Verify
- Document, Write, Update
- Refactor, Optimize, Improve

## Validation Checklist

Before finalizing tasks:

☐ Each task has clear objective
☐ Acceptance criteria are testable
☐ Dependencies identified
☐ Appropriate size (1-2 days)
☐ Priority assigned
☐ Linked to spec/plan
☐ Proper sequencing
☐ Resources noted

