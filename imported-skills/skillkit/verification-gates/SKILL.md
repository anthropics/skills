---
name: verification-gates
description: Creates explicit validation checkpoints (verification gates) between project phases to catch errors early and ensure quality before proceeding. Use when the user asks about quality gates, milestone checks, phase transitions, approval steps, go/no-go decision points, or preventing cascading errors across a multi-step workflow. Produces acceptance criteria checklists, automated CI gate configurations, manual sign-off requirements, and conditional review rules for scenarios such as security changes, API changes, or database migrations.
version: 1.0.0
triggers:
  - verify before
  - checkpoint
  - quality gate
  - make sure before
  - validation
tags:
  - planning
  - verification
  - quality
  - gates
difficulty: beginner
estimatedTime: 10
relatedSkills:
  - planning/design-first
  - planning/task-decomposition
  - testing/red-green-refactor
---

# Verification Gates

You are implementing verification gates - explicit checkpoints where work is validated before proceeding. This prevents cascading errors and ensures quality at each phase.

## Core Principle

**Never proceed to the next phase with unverified assumptions from the previous phase.**

A verification gate is a deliberate pause to confirm that prerequisites are met before continuing.

## Standard Verification Gates

### Gate 1: Requirements Verification

Before starting design:

- [ ] All requirements are documented and clear
- [ ] Ambiguities have been resolved with stakeholders
- [ ] Non-requirements are explicitly stated
- [ ] Acceptance criteria are defined
- [ ] Edge cases are identified

**Actions:**
1. Review requirements document
2. Identify any unclear items
3. Get explicit confirmation on ambiguous points
4. Document answers

### Gate 2: Design Verification

Before starting implementation:

- [ ] Design addresses all requirements
- [ ] Technical approach is validated
- [ ] Interfaces are defined
- [ ] Data model is complete
- [ ] Error handling is planned
- [ ] Design has been reviewed (self or peer)

**Actions:**
1. Walk through design against requirements
2. Review with rubber duck or teammate
3. Check for missing pieces
4. Get approval to proceed

### Gate 3: Implementation Verification

Before calling task complete:

- [ ] Code compiles/runs without errors
- [ ] All tests pass
- [ ] New code has test coverage
- [ ] Code follows project conventions
- [ ] No obvious bugs or issues
- [ ] Dependencies are appropriate

**Actions:**
1. Run full test suite
2. Self-review the diff
3. Check for code smells
4. Verify against acceptance criteria

### Gate 4: Integration Verification

Before merging:

- [ ] Feature works end-to-end
- [ ] Integration tests pass
- [ ] No regression in existing functionality
- [ ] Performance is acceptable
- [ ] Documentation is updated

**Actions:**
1. Test the full user flow
2. Run integration test suite
3. Compare performance metrics
4. Review documentation changes

### Gate 5: Deployment Verification

Before marking complete:

- [ ] Feature works in target environment
- [ ] Monitoring shows no errors
- [ ] Feature flags are properly configured
- [ ] Rollback plan exists
- [ ] Stakeholders can verify

**Actions:**
1. Smoke test in environment
2. Check error logs and metrics
3. Get stakeholder sign-off
4. Document deployment

## Gate Types

### Automated Gates

Gates that can be enforced automatically:

```yaml
# CI Pipeline Gates
gates:
  - name: lint
    command: npm run lint
    required: true

  - name: type-check
    command: npm run typecheck
    required: true

  - name: unit-tests
    command: npm test
    required: true
    coverage: 80%

  - name: build
    command: npm run build
    required: true
```

### Manual Gates

Gates requiring human judgment:

```markdown
## Manual Verification Checklist

Before Code Review:
- [ ] I've tested my changes locally
- [ ] I've written/updated tests
- [ ] I've read my own diff
- [ ] I've checked for security issues
- [ ] I've updated documentation

Before Deployment:
- [ ] Code review approved
- [ ] QA verified (if applicable)
- [ ] Stakeholder approved (if required)
- [ ] Deployment plan reviewed
```

### Conditional Gates

Gates that apply in specific situations:

| Condition | Required Gates |
|-----------|---------------|
| Security-related | Security review |
| Public API change | API review + migration plan |
| Database change | DBA review + backup plan |
| Performance-sensitive | Performance test |
| Breaking change | Deprecation notice + migration |

## Implementing Gates

### In Your Workflow

```
Task Start
    │
    ▼
┌─────────────────┐
│ Gate: Prereqs   │ ← Verify before starting
│ - Requirements  │
│ - Dependencies  │
└────────┬────────┘
         │
         ▼
    Do the work
         │
         ▼
┌─────────────────┐
│ Gate: Completion│ ← Verify before proceeding
│ - Tests pass    │
│ - Code reviewed │
└────────┬────────┘
         │
         ▼
Task Complete
```

### Gate Documentation Template

```markdown
## Gate: [Name]

**When:** [Before what action]

**Purpose:** [What this gate ensures]

**Checklist:**
- [ ] Item 1
- [ ] Item 2
- [ ] Item 3

**Verification Method:**
- [How to verify each item]

**Failure Actions:**
- [What to do if gate fails]

**Approver:** [Who can approve passage]
```

## Gate Metrics

Good gates have high effectiveness (catch most issues), low overhead (quick to pass), and high value (prevent expensive downstream fixes). Track which gate caught an issue and how much time was spent at each gate to tune your process over time.

## Integration with CI/CD

```yaml
# GitHub Actions example
jobs:
  gate-lint:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - run: npm ci
      - run: npm run lint

  gate-test:
    needs: gate-lint
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - run: npm ci
      - run: npm test

  gate-build:
    needs: gate-test
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - run: npm ci
      - run: npm run build

  deploy:
    needs: gate-build
    # Only deploys if all gates pass
```

## Quick Reference

| Phase | Gate Before | Key Checks |
|-------|-------------|------------|
| Design | Requirements | Clear, complete, approved |
| Implementation | Design | Reviewed, feasible |
| Review | Implementation | Tests, conventions, working |
| Merge | Review | Approved, conflicts resolved |
| Deploy | Merge | Environment ready, plan exists |

## Integration with Other Skills

- **design-first**: Gates validate design before implementation
- **task-decomposition**: Gates between task phases
- **testing/red-green-refactor**: Tests are key gate criteria
- **collaboration/structured-review**: Review is a gate
