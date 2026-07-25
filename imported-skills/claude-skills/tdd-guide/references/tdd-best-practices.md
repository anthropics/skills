# TDD Best Practices

Guidelines for effective test-driven development workflows.

---

## Table of Contents

- [Red-Green-Refactor Cycle](#red-green-refactor-cycle)
- [Test Generation Guidelines](#test-generation-guidelines)
- [Test Quality Principles](#test-quality-principles)
- [Coverage Goals](#coverage-goals)

---

## Red-Green-Refactor Cycle

### RED Phase
1. Write a failing test before any implementation
2. Test should fail for the right reason (not compilation errors)
3. Name tests as specifications describing expected behavior
4. Keep tests small and focused on single behaviors

### GREEN Phase
1. Write minimal code to make the test pass
2. Avoid over-engineering at this stage
3. Duplicate code is acceptable temporarily
4. Focus on correctness, not elegance

### REFACTOR Phase
1. Improve code structure while keeping tests green
2. Remove duplication introduced in GREEN phase
3. Apply design patterns where appropriate
4. Run tests after each small refactoring

### Cycle Discipline
- Complete one cycle before starting the next
- Commit after each successful GREEN phase
- Small iterations lead to better designs
- Resist temptation to write implementation first

---

## Test Generation Guidelines

### Behavior Focus
- Test what code does, not how it does it
- Avoid coupling tests to implementation details
- Tests should survive internal refactoring
- Focus on observable outcomes

### Naming Conventions
- Use descriptive names that read as specifications
- Format: `should_<expected>_when_<condition>`
- Examples:
  - `should_return_zero_when_cart_is_empty`
  - `should_reject_negative_amounts`
  - `should_apply_discount_for_members`

### Test Structure
- Follow Arrange-Act-Assert (AAA) pattern
- Keep setup minimal and relevant
- One logical assertion per test
- Extract shared setup to fixtures

### Coverage Scope
- Happy path: Normal expected usage
- Error cases: Invalid inputs, failures
- Edge cases: Boundaries, empty states
- Exceptional cases: Timeouts, nulls

---

## Test Quality Principles

### Independence
- Each test runs in isolation
- No shared mutable state between tests
- Tests can run in any order
- Parallel execution should work

### Speed
- Unit tests under 100ms each
- Avoid I/O in unit tests
- Mock external dependencies
- Use in-memory databases for integration

### Determinism
- Same inputs produce same results
- No dependency on system time or random values
- Controlled test data
- No flaky tests allowed

### Clarity
- Failure messages explain what went wrong
- Test code is as clean as production code
- Avoid clever tricks that obscure intent
- Comments explain non-obvious setup

---

## Coverage Goals

### Thresholds by Type
| Type | Target | Rationale |
|------|--------|-----------|
| Line coverage | 80%+ | Baseline for most projects |
| Branch coverage | 70%+ | More meaningful than line |
| Function coverage | 90%+ | Public APIs should be tested |

### Critical Path Rules
- Authentication: 100% coverage required
- Payment processing: 100% coverage required
- Data validation: 100% coverage required
- Error handlers: Must test all paths

### Avoiding Coverage Theater
- High coverage != good tests
- Focus on meaningful assertions
- Test behaviors, not lines
- Code review test quality, not just metrics

### Coverage Analysis Workflow
1. Generate coverage report after test run
2. Identify uncovered critical paths (P0)
3. Review medium-priority gaps (P1)
4. Document accepted low-priority gaps (P2)
5. Set threshold gates in CI pipeline
