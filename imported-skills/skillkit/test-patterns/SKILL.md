---
name: test-patterns
description: Applies proven testing patterns — Arrange-Act-Assert (AAA), Given-When-Then, Test Data Builders, Object Mother, parameterized tests, fixtures, spies, and test doubles — to help write maintainable, reliable, and readable test suites. Use when the user asks about writing unit tests, integration tests, or end-to-end tests; structuring test cases or test suites; applying TDD or BDD practices; working with mocks, stubs, spies, or fakes; improving test coverage or reducing flakiness; or needs guidance on test organization, naming conventions, or assertions in frameworks like Jest, Vitest, pytest, or similar.
version: 1.0.0
triggers:
  - test patterns
  - testing best practices
  - how to write tests
  - test structure
  - arrange act assert
tags:
  - testing
  - patterns
  - quality
  - best-practices
difficulty: intermediate
estimatedTime: 10
relatedSkills:
  - testing/red-green-refactor
  - testing/anti-patterns
---

# Test Patterns

You are applying proven testing patterns to write maintainable, reliable tests. These patterns help ensure tests are readable, focused, and trustworthy.

## Pattern Selection Guide

Use this to choose the right pattern for your situation:

- **Structuring a single test?** → Arrange-Act-Assert (AAA) or Given-When-Then
- **Writing behavior/feature specs?** → Given-When-Then (BDD style)
- **Repeating test setup data?** → Test Data Builders
- **Many variations of complex objects?** → Object Mother
- **Testing same logic with many inputs?** → Parameterized Tests
- **Shared setup/teardown across tests?** → Test Fixtures
- **Verifying a dependency was called?** → Spy
- **Replacing an external dependency?** → Test Doubles (Stub / Mock / Fake)

---

## Pattern Combination Workflows

Patterns rarely stand alone — here's how to combine them for common scenarios:

**Unit tests (isolated logic):**
Fixtures for setup → AAA structure → Stubs/Mocks for dependencies → Parameterized Tests for multiple input cases

**Integration tests (service + external dependencies):**
Fixtures for setup → AAA structure → Fakes for external services (e.g. in-memory DB) → Spies to verify interaction points

**BDD / feature specs:**
Given-When-Then → Object Mother or Test Data Builders for scenario data → Fakes for infrastructure

**High-variation logic (validators, calculators, formatters):**
Parameterized Tests → Test Data Builders to construct each case → AAA structure within each case

---

## Core Pattern: Arrange-Act-Assert (AAA)

Structure every test with three distinct phases:

```
// Arrange - Set up test data and dependencies
const user = createTestUser({ role: 'admin' });
const service = new UserService(mockRepository);

// Act - Execute the code under test
const result = await service.updateRole(user.id, 'member');

// Assert - Verify the expected outcome
expect(result.role).toBe('member');
expect(mockRepository.save).toHaveBeenCalledWith(user);
```

Guidelines:
- Keep sections visually separated (blank lines or comments)
- Arrange should be minimal - only what's needed for this test
- Act should be a single operation
- Assert should verify one logical concept

## Pattern: Given-When-Then (BDD Style)

For behavior-focused tests:

```
describe('Shopping Cart', () => {
  describe('when adding an item', () => {
    it('should increase the item count', () => {
      // Given
      const cart = new Cart();

      // When
      cart.add({ id: '1', quantity: 2 });

      // Then
      expect(cart.itemCount).toBe(2);
    });
  });
});
```

## Pattern: Test Data Builders

Create flexible test data without repetition:

```
// Builder function
function createTestOrder(overrides = {}) {
  return {
    id: 'order-123',
    status: 'pending',
    items: [],
    total: 0,
    ...overrides
  };
}

// Usage
const completedOrder = createTestOrder({ status: 'completed', total: 99.99 });
const emptyOrder = createTestOrder({ items: [] });
```

## Pattern: Object Mother

Factory for complex test objects:

```
class TestUserFactory {
  static admin() {
    return new User({ role: 'admin', permissions: ALL_PERMISSIONS });
  }

  static guest() {
    return new User({ role: 'guest', permissions: [] });
  }

  static withSubscription(tier) {
    return new User({ subscription: { tier, active: true } });
  }
}
```

## Pattern: Parameterized Tests

Test multiple cases efficiently:

```
describe('isValidEmail', () => {
  const validCases = [
    'user@example.com',
    'user.name@domain.co.uk',
    'user+tag@example.org'
  ];

  const invalidCases = [
    '',
    'not-an-email',
    '@no-local.com',
    'no-domain@'
  ];

  test.each(validCases)('should accept valid email: %s', (email) => {
    expect(isValidEmail(email)).toBe(true);
  });

  test.each(invalidCases)('should reject invalid email: %s', (email) => {
    expect(isValidEmail(email)).toBe(false);
  });
});
```

## Pattern: Test Fixtures

Reusable test setup:

```
describe('OrderService', () => {
  let service;
  let mockPaymentGateway;
  let mockInventory;

  beforeEach(() => {
    mockPaymentGateway = createMockPaymentGateway();
    mockInventory = createMockInventory();
    service = new OrderService(mockPaymentGateway, mockInventory);
  });

  afterEach(() => {
    jest.clearAllMocks();
  });
});
```

## Pattern: Spy on Dependencies

Verify interactions without implementation:

```
it('should send notification on order completion', async () => {
  const notifySpy = jest.spyOn(notificationService, 'send');

  await orderService.complete(orderId);

  expect(notifySpy).toHaveBeenCalledWith({
    type: 'order_completed',
    orderId: orderId
  });
});
```

## Pattern: Test Doubles

Choose the right type:

| Type | When to Use |
|------|-------------|
| **Stub** | Need predictable, canned return values |
| **Mock** | Need to assert a dependency was called correctly |
| **Spy** | Partial mocking — observe calls on a real object |
| **Fake** | Need a working lightweight substitute (e.g. in-memory DB) |

## Pattern: Test Isolation

Ensure tests don't affect each other:

1. **Fresh instances** - Create new objects in each test
2. **Reset mocks** - Clear mock state between tests
3. **Clean up** - Remove side effects (files, database rows)
4. **No shared mutable state** - Avoid global variables

## Naming Conventions

Test names should describe:
- What is being tested
- Under what conditions
- What the expected outcome is

Good examples:
- `shouldReturnEmptyArrayWhenNoItemsExist`
- `throwsErrorWhenUserNotAuthenticated`
- `calculatesDiscountForPremiumMembers`

## Test Organization

```
src/
  services/
    UserService.ts
    UserService.test.ts    # Co-located tests

tests/
  integration/
    api.test.ts            # Integration tests
  e2e/
    checkout.spec.ts       # End-to-end tests
```

## Verification Checklist

For each test:
- [ ] Single responsibility (tests one thing)
- [ ] Clear AAA or GWT structure
- [ ] Descriptive name
- [ ] Fast execution (< 100ms for unit tests)
- [ ] Deterministic (no flakiness)
- [ ] Independent (runs in any order)
