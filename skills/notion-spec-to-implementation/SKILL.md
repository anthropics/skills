---
name: notion-spec-to-implementation
description: Turns product or tech specs into concrete Notion tasks that Claude code can implement. Breaks down spec pages into detailed implementation plans with clear tasks, acceptance criteria, and progress tracking to guide development from requirements to completion.
---

# Spec to Implementation

Transforms specifications into actionable implementation plans with progress tracking. Fetches spec documents, extracts requirements, breaks down into tasks, and manages implementation workflow.

## Quick Start

When asked to implement a specification:

1. **Find spec**: Use `Notion:notion-search` to locate specification page
2. **Fetch spec**: Use `Notion:notion-fetch` to read specification content
3. **Extract requirements**: Parse and structure requirements from spec
4. **Create plan**: Use `Notion:notion-create-pages` for implementation plan
5. **Find task database**: Use `Notion:notion-search` to locate tasks database
6. **Create tasks**: Use `Notion:notion-create-pages` for individual tasks in task database
7. **Track progress**: Use `Notion:notion-update-page` to log progress and update status

## Implementation Workflow

### Step 1: Find the specification

```
1. Search for spec:
   - Use Notion:notion-search with spec name or topic
   - Apply filters if needed (e.g., created_date_range, teamspace_id)
   - Look for spec title or keyword matches
   - If not found or ambiguous, ask user for spec URL/ID

Example searches:
- "User Authentication spec"
- "Payment Integration specification"
- "Mobile App Redesign PRD"
```

### Step 2: Fetch and analyze specification

```
1. Fetch spec page:
   - Use Notion:notion-fetch with spec URL/ID from search results
   - Read full content including requirements, design, constraints

2. Parse specification:
   - Identify functional requirements
   - Note non-functional requirements (performance, security, etc.)
   - Extract acceptance criteria
   - Identify dependencies and blockers
```

See [reference/spec-parsing.md](reference/spec-parsing.md) for parsing patterns.

### Step 3: Create implementation plan

```
1. Break down into phases/milestones
2. Identify technical approach
3. List required tasks
4. Estimate effort
5. Identify risks

Use implementation plan template (see [reference/standard-implementation-plan.md](reference/standard-implementation-plan.md) or [reference/quick-implementation-plan.md](reference/quick-implementation-plan.md))
```

### Step 4: Create implementation plan page

```
Use Notion:notion-create-pages:
- Title: "Implementation Plan: [Feature Name]"
- Content: Structured plan with phases, tasks, timeline
- Link back to original spec
- Add to appropriate location (project page, database)
```

### Step 5: Find task database

```
1. Search for task database:
   - Use Notion:notion-search to find "Tasks" or "Task Management" database
   - Look for engineering/project task tracking system
   - If not found or ambiguous, ask user for database location

2. Fetch database schema:
   - Use Notion:notion-fetch with database URL/ID
   - Get property names, types, and options
   - Identify correct data source from <data-source> tags
   - Note required properties for new tasks
```

### Step 6: Create implementation tasks

```
For each task in plan:
1. Create task in task database using Notion:notion-create-pages
2. Use parent: { data_source_id: 'collection://...' }
3. Set properties from schema:
   - Name/Title: Task description
   - Status: To Do
   - Priority: Based on criticality
   - Related Tasks: Link to spec and plan
4. Add implementation details in content
```

See [reference/task-creation.md](reference/task-creation.md) for task patterns.

### Step 7: Begin implementation

```
1. Update task status to "In Progress"
2. Add initial progress note
3. Document approach and decisions
4. Link relevant resources
```

### Step 8: Track progress

```
Regular updates:
1. Update task properties (status, progress)
2. Add progress notes with:
   - What's completed
   - Current focus
   - Blockers/issues
3. Update implementation plan with milestone completion
4. Link to related work (PRs, designs, etc.)
```

See [reference/progress-tracking.md](reference/progress-tracking.md) for tracking patterns.

## Spec Analysis Patterns

**Functional Requirements**: User stories, feature descriptions, workflows, data requirements, integration points

**Non-Functional Requirements**: Performance targets, security requirements, scalability needs, availability, compliance

**Acceptance Criteria**: Testable conditions, user validation points, performance benchmarks, completion definitions

See [reference/spec-parsing.md](reference/spec-parsing.md) for detailed parsing techniques.

## Implementation Plan Structure

**Plan includes**: Overview → Linked Spec → Requirements Summary → Technical Approach → Implementation Phases (Goal, Tasks checklist, Estimated effort) → Dependencies → Risks & Mitigation → Timeline → Success Criteria

See [reference/standard-implementation-plan.md](reference/standard-implementation-plan.md) for full plan template.

## Task Breakdown Patterns

**By Component**: Database, API endpoints, frontend components, integration, testing
**By Feature Slice**: Vertical slices (auth flow, data entry, report generation)
**By Priority**: P0 (must have), P1 (important), P2 (nice to have)


## Progress Logging

**Daily Updates** (active work): Add progress note with completed items, current focus, blockers
**Milestone Updates** (major progress): Update plan checkboxes, add milestone summary, adjust timeline
**Status Changes** (task transitions): Update properties (In Progress → In Review → Done), add completion notes, link deliverables

**Progress Format**: Date heading → Completed → In Progress → Next Steps → Blockers → Notes

See [reference/progress-tracking.md](reference/progress-tracking.md) for detailed patterns.

## Linking Spec to Implementation

**Forward Links**: Update spec page with "Implementation" section linking to plan and tasks
**Backward Links**: Reference spec in plan and tasks with "Specification" section
**Bidirectional Traceability**: Maintain both directions for easy tracking

## Implementation Status Tracking

**Plan Status**: Update with phase completion (✅ Complete, 🔄 In Progress %, ⏳ Not Started) and overall percentage
**Task Aggregation**: Query task database by plan ID to generate summary (complete, in progress, blocked, not started)

## Handling Spec Changes

**Detection**: Fetch updated spec → compare with plan → identify new requirements → assess impact
**Propagation**: Update plan → create new tasks → update affected tasks → add change note → notify via comments
**Change Log**: Track spec evolution with date, what changed, and impact

## Common Patterns

**Feature Flag**: Backend (behind flag) → Testing → Frontend (flagged) → Internal rollout → External rollout
**Database Migration**: Schema design → Migration script → Staging test → Production migration → Validation
**API Development**: API design → Backend implementation → Testing & docs → Client integration → Deployment


## Best Practices

1. **Always link spec and implementation**: Maintain bidirectional references
2. **Break down into small tasks**: Each task should be completable in 1-2 days
3. **Extract clear acceptance criteria**: Know when "done" is done
4. **Identify dependencies early**: Note blockers in plan
5. **Update progress regularly**: Daily notes for active work
6. **Track changes**: Document spec updates and their impact
7. **Use checklists**: Visual progress indicators help everyone
8. **Link deliverables**: PRs, designs, docs should link back to tasks

## Advanced Features

For additional implementation patterns and techniques, see the reference files in [reference/](reference/).

## Common Issues

**"Can't find spec"**: Use Notion:notion-search with spec name/topic, try broader terms, or ask user for URL
**"Multiple specs found"**: Ask user which spec to implement or show options
**"Can't find task database"**: Search for "Tasks" or "Task Management", or ask user for database location
**"Spec unclear"**: Note ambiguities in plan, create clarification tasks
**"Requirements conflicting"**: Document conflicts, create decision task
**"Scope too large"**: Break into smaller specs/phases

## Examples

See [examples/](examples/) for complete workflows:
- [examples/api-feature.md](examples/api-feature.md) - API feature implementation
- [examples/ui-component.md](examples/ui-component.md) - Frontend component
- [examples/database-migration.md](examples/database-migration.md) - Schema changes

