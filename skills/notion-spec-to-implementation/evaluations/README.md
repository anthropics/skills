# Spec to Implementation Skill Evaluations

Evaluation scenarios for testing the Spec to Implementation skill across different Claude models.

## Purpose

These evaluations ensure the Spec to Implementation skill:
- Finds and parses specification pages accurately
- Breaks down specs into actionable implementation plans
- Creates tasks that Claude can implement with clear acceptance criteria
- Tracks progress and updates implementation status
- Works consistently across Haiku, Sonnet, and Opus

## Evaluation Files

### basic-spec-implementation.json
Tests basic workflow of turning a spec into an implementation plan.

**Scenario**: Implement user authentication feature from spec  
**Key Behaviors**:
- Searches for and finds the authentication spec page
- Fetches spec and extracts requirements
- Parses requirements into phases (setup, core features, polish)
- Creates implementation plan page linked to original spec
- Breaks down into clear phases with deliverables
- Includes timeline and dependencies

### spec-to-tasks.json
Tests creating concrete tasks from a specification in a task database.

**Scenario**: Create tasks from API redesign spec  
**Key Behaviors**:
- Finds spec page in Notion
- Extracts specific requirements and acceptance criteria
- Searches for or creates task database
- Fetches task database schema
- Creates multiple tasks with proper properties (Status, Priority, Sprint, etc.)
- Each task has clear title, description, and acceptance criteria
- Tasks have dependencies where appropriate
- Links all tasks back to original spec

## Running Evaluations

1. Enable the `spec-to-implementation` skill
2. Submit the query from the evaluation file
3. Verify the skill finds the spec page via search
4. Check that requirements are accurately parsed
5. Confirm implementation plan is created with phases
6. Verify tasks have clear, implementable acceptance criteria
7. Check that tasks link back to spec
8. Test with Haiku, Sonnet, and Opus

## Expected Skill Behaviors

Spec to Implementation evaluations should verify:

### Spec Discovery & Parsing
- Searches Notion for specification pages
- Fetches complete spec content
- Extracts all requirements accurately
- Identifies technical dependencies
- Understands acceptance criteria
- Notes any ambiguities or missing details

### Implementation Planning
- Creates implementation plan page
- Breaks work into logical phases:
  - Phase 1: Foundation/Setup
  - Phase 2: Core Implementation
  - Phase 3: Testing & Polish
- Includes timeline estimates
- Identifies dependencies between phases
- Links back to original spec

### Task Creation
- Finds or identifies task database
- Fetches database schema for property names
- Creates tasks with correct properties
- Each task has:
  - Clear, specific title
  - Context and description
  - Acceptance criteria (checklist format)
  - Appropriate priority and status
  - Link to spec page
- Tasks are right-sized (not too big, not too small)
- Dependencies between tasks are noted

### Progress Tracking
- Implementation plan includes progress markers
- Tasks can be updated as work progresses
- Status updates link to completed work
- Blockers or changes are noted

## Creating New Evaluations

When adding Spec to Implementation evaluations:

1. **Test different spec types** - Features, migrations, refactors, API changes, UI components
2. **Vary complexity** - Simple 1-phase vs. complex multi-phase implementations
3. **Test task granularity** - Does it create appropriately-sized tasks?
4. **Include edge cases** - Vague specs, conflicting requirements, missing details
5. **Test database integration** - Creating tasks in existing task databases with various schemas
6. **Progress tracking** - Updating implementation plans as tasks complete

## Example Success Criteria

**Good** (specific, testable):
- "Searches Notion for spec page using feature name"
- "Creates implementation plan with 3 phases: Setup → Core → Polish"
- "Creates 5-8 tasks in task database with properties: Task (title), Status, Priority, Sprint"
- "Each task has acceptance criteria in checklist format (- [ ] ...)"
- "Tasks link back to spec using mention-page tag"
- "Task titles are specific and actionable (e.g., 'Create login API endpoint' not 'Authentication')"

**Bad** (vague, untestable):
- "Creates good implementation plan"
- "Tasks are well-structured"
- "Breaks down spec appropriately"
- "Links to spec"

