# Spec-Driven Development Workflow

This document provides detailed guidance on the four-phase SDD workflow.

## Why Spec-Driven Development?

Research shows that structured specifications significantly improve AI-assisted development:

> "1 iteration with structure was of similar accuracy to 8 iterations with unstructured prompts"
> — AI Native Dev

### Benefits

1. **Clarity**: Forces upfront thinking before coding
2. **Alignment**: Ensures shared understanding across team/AI
3. **Traceability**: Links requirements → design → implementation
4. **Documentation**: Creates living documentation as a byproduct
5. **Quality**: Reduces rework through early validation

## Four Phases Overview

```
┌─────────────┐    ┌──────────────┐    ┌──────────┐    ┌─────────┐
│  PROPOSAL   │ → │ REQUIREMENTS │ → │  DESIGN  │ → │  TASKS  │
│   (Why?)    │    │   (What?)    │    │  (How?)  │    │ (Steps) │
└─────────────┘    └──────────────┘    └──────────┘    └─────────┘
```

## Phase 1: Proposal

### Purpose

Define **why** this change is needed and establish scope boundaries.

### Key Activities

1. **Identify the Problem**: What pain point or opportunity exists?
2. **Define Goals**: What measurable outcomes do we want?
3. **Set Boundaries**: What's in scope vs. out of scope?
4. **Assess Risks**: What could go wrong? How do we mitigate?

### Exit Criteria

- [ ] Background clearly explained
- [ ] Goals are specific and measurable
- [ ] Non-goals explicitly stated
- [ ] Risks identified with mitigations
- [ ] Open questions resolved
- [ ] Stakeholder approval obtained

### Common Mistakes

- ❌ Starting with solution instead of problem
- ❌ Vague goals ("make it better")
- ❌ Missing non-goals (leads to scope creep)
- ❌ Ignoring risks

## Phase 2: Requirements

### Purpose

Define **what** the system should do using structured requirements.

### EARS Format

EARS (Easy Approach to Requirements Syntax) provides templates for different requirement types:

| Type | Template | Example |
|------|----------|---------|
| Ubiquitous | The system shall... | The system shall log all API requests |
| Event-Driven | When X, the system shall... | When user clicks submit, the system shall validate inputs |
| State-Driven | While X, the system shall... | While user is authenticated, the system shall refresh tokens |
| Unwanted | If X, the system shall NOT... | If payment fails, the system shall NOT create order |
| Optional | Where X, the system shall... | Where dark mode is enabled, the system shall use dark theme |

### Requirement Categories

1. **Functional Requirements (FR)**: What the system does
2. **Non-Functional Requirements (NFR)**: How the system behaves
   - Performance
   - Security
   - Reliability
   - Scalability
   - Usability
   - Maintainability

### Exit Criteria

- [ ] All requirements use EARS format
- [ ] Each requirement is testable
- [ ] Acceptance criteria defined
- [ ] No ambiguous language
- [ ] Traceability matrix complete

### Common Mistakes

- ❌ Ambiguous requirements ("fast", "user-friendly")
- ❌ Missing non-functional requirements
- ❌ Requirements without acceptance criteria
- ❌ Too many requirements per item (combine into one)

## Phase 3: Design

### Purpose

Define **how** to implement the requirements.

### Key Artifacts

1. **Architecture Diagram**: High-level component view
2. **API Specifications**: Endpoints, request/response schemas
3. **Data Models**: Entity relationships
4. **Sequence Diagrams**: Interaction flows
5. **Error Handling**: Error codes and resolutions

### Design Considerations

- **Simplicity**: Favor simple solutions over complex ones
- **Extensibility**: Design for future needs, but don't over-engineer
- **Consistency**: Follow existing patterns in the codebase
- **Testability**: Design for easy testing

### Exit Criteria

- [ ] Architecture addresses all requirements
- [ ] APIs fully specified
- [ ] Data models defined
- [ ] Error handling documented
- [ ] Migration plan (if needed)
- [ ] Design approved by reviewers

### Common Mistakes

- ❌ Over-engineering for hypothetical future needs
- ❌ Ignoring existing patterns in codebase
- ❌ Missing error handling design
- ❌ No migration plan for schema changes

## Phase 4: Tasks

### Purpose

Break down the design into **executable steps**.

### Task Decomposition Principles

1. **Atomic**: Each task completable in 1-2 tool calls
2. **Independent**: Minimize dependencies when possible
3. **Testable**: Each task has verifiable outcome
4. **Estimated**: Include complexity (Low/Medium/High)

### Task Organization

```
Phase 1: Setup
  T-001: Create directory structure
  T-002: Add dependencies

Phase 2: Core Implementation
  T-010: Implement data model
  T-011: Implement service layer
  T-012: Implement API endpoints

Phase 3: Integration
  T-020: Wire components together
  T-021: Add error handling

Phase 4: Testing
  T-030: Unit tests
  T-031: Integration tests
  T-032: E2E tests

Phase 5: Documentation
  T-040: API documentation
  T-041: Update README
```

### Progress Tracking

| Status | Symbol | Meaning |
|--------|--------|---------|
| Pending | ⏳ | Not started |
| In Progress | 🔄 | Currently working |
| Done | ✅ | Completed |
| Blocked | ❌ | Waiting on dependency |
| On Hold | ⏸️ | Paused intentionally |

### Exit Criteria

- [ ] All tasks completed
- [ ] All tests passing
- [ ] Code reviewed
- [ ] Documentation updated
- [ ] Spec archived

## Phase Transitions

### Skip Conditions

| Phase | Can Skip When |
|-------|---------------|
| Proposal | Never (always clarify intent) |
| Requirements | Never for new features |
| Design | Simple feature, architecture obvious |
| Tasks | Never (always break down work) |

### Rollback Conditions

| Situation | Action |
|-----------|--------|
| New requirements discovered | Return to Requirements phase |
| Design flaw found | Return to Design phase |
| Scope change requested | Return to Proposal phase |

## Best Practices

### During Development

1. **Update status regularly**: Keep tasks.md current
2. **Link to code**: Reference commits, PRs, file paths
3. **Document decisions**: Note why alternatives were rejected
4. **Raise blockers early**: Don't wait until deadline

### After Completion

1. **Archive spec**: Move to `.spec-flow/archive/`
2. **Retrospective**: What worked? What didn't?
3. **Update templates**: Improve based on learnings
4. **Update steering docs**: If project patterns changed

## Integration with AI Agents

### Providing Context

When working with AI agents, provide:

1. The full spec (proposal + requirements + design)
2. Current task being worked on
3. Relevant steering documents
4. Any blockers or constraints

### Effective Prompts

```
I'm implementing [feature] based on the spec in .spec-flow/active/[feature]/.
Currently working on task T-010: [task description].
The design specifies [relevant design detail].
Please help me implement [specific request].
```

### Validation

After AI generates code:

1. Verify against acceptance criteria
2. Run tests
3. Update task status
4. Move to next task
