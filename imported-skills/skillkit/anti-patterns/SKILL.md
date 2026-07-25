---
name: testing-anti-patterns
description: Reviews test code to identify and fix common testing anti-patterns including flaky tests, over-mocking, brittle assertions, test interdependency, and hidden test logic. Flags bad patterns, explains the specific defect, and provides corrected implementations. Use when reviewing test code, debugging intermittent or unreliable test failures, or when the user mentions flaky tests, test smells, brittle tests, test isolation issues, mock overuse, slow tests, or test maintenance problems.
version: 1.0.0
triggers:
  - test anti-patterns
  - testing mistakes
  - bad tests
  - flaky tests
  - test smells
tags:
  - testing
  - anti-patterns
  - quality
  - code-smells
difficulty: intermediate
estimatedTime: 10
relatedSkills:
  - testing/red-green-refactor
  - testing/test-patterns
---

# Testing Anti-Patterns

You are identifying and avoiding common testing anti-patterns.

## Review Workflow

Follow these steps when reviewing test code:

1. **Run tests in isolation** — Verify each test passes independently (no shared state, no ordering dependency).
2. **Check for patterns below** — Scan for each anti-pattern in the checklist; flag every match with the specific defect.
3. **Apply refactoring strategy** — Use the refactoring strategies section to select and apply the appropriate fix.
4. **Verify the test still fails when code breaks** — After fixing, confirm the corrected test catches real regressions (remove or stub the implementation to confirm a failure occurs).

## Critical Anti-Patterns

### 1. The Liar - Tests That Always Pass

**Problem:** Test passes even when the code is broken.

```typescript
// BAD - Always passes because it tests nothing meaningful
it('should process data', () => {
  const result = processData(input);
  expect(result).toBeDefined(); // Too weak
});

// GOOD - Actually verifies behavior
it('should transform input to uppercase', () => {
  const result = processData({ text: 'hello' });
  expect(result.text).toBe('HELLO');
});
```

**Detection:** Remove or break the implementation - test should fail.

### 2. The Giant - Tests Too Large

**Problem:** Single test covers too many behaviors.

```typescript
// BAD - Tests multiple things
it('should handle user registration', async () => {
  const user = await register(userData);
  expect(user.id).toBeDefined();
  expect(user.email).toBe(userData.email);
  expect(user.password).toBeUndefined();
  expect(sendEmail).toHaveBeenCalled();
  expect(createProfile).toHaveBeenCalled();
  // ... 20 more assertions
});

// GOOD - Focused tests
it('should create user with provided email', async () => {
  const user = await register(userData);
  expect(user.email).toBe(userData.email);
});

it('should send welcome email on registration', async () => {
  await register(userData);
  expect(sendEmail).toHaveBeenCalledWith(
    expect.objectContaining({ type: 'welcome' })
  );
});
```

**Fix:** One test, one logical assertion concept.

### 3. The Inspector - Testing Implementation Details

**Problem:** Test breaks when implementation changes, even if behavior is correct.

```typescript
// BAD - Tests internal implementation
it('should use QuickSort for sorting', () => {
  const sorter = new Sorter();
  const spy = jest.spyOn(sorter, '_quickSort');
  sorter.sort([3, 1, 2]);
  expect(spy).toHaveBeenCalled();
});

// GOOD - Tests behavior/output
it('should return sorted array', () => {
  const sorter = new Sorter();
  expect(sorter.sort([3, 1, 2])).toEqual([1, 2, 3]);
});
```

**Fix:** Test what the code does, not how it does it.

### 4. The Mockery - Over-Mocking

**Problem:** Too many mocks make tests meaningless.

```typescript
// BAD - Everything is mocked, test proves nothing
it('should calculate price', () => {
  const mockProduct = { getPrice: jest.fn().mockReturnValue(100) };
  const mockDiscount = { apply: jest.fn().mockReturnValue(80) };
  const mockTax = { calculate: jest.fn().mockReturnValue(8) };

  const total = calculateTotal(mockProduct, mockDiscount, mockTax);
  expect(total).toBe(88); // Just testing mock arithmetic
});

// GOOD - Use real objects where feasible
it('should apply 20% discount to price', () => {
  const product = new Product({ price: 100 });
  const discount = new PercentageDiscount(20);

  const total = calculateTotal(product, discount);
  expect(total).toBe(80);
});
```

**Fix:** Only mock external dependencies and side effects.

### 5. The Flaky Test - Random Failures

**Problem:** Test sometimes passes, sometimes fails.

Common causes:
- **Time-dependent logic**
- **Race conditions in async code**
- **Shared mutable state**
- **External dependencies**

```typescript
// BAD - Depends on current time
it('should show recent items', () => {
  const item = { createdAt: new Date() };
  expect(isRecent(item)).toBe(true);
});

// GOOD - Control the time
it('should show items from last 24 hours', () => {
  const now = new Date('2024-01-15T12:00:00Z');
  jest.setSystemTime(now);

  const recent = { createdAt: new Date('2024-01-15T00:00:00Z') };
  const old = { createdAt: new Date('2024-01-13T00:00:00Z') };

  expect(isRecent(recent)).toBe(true);
  expect(isRecent(old)).toBe(false);
});
```

### 6. The Slow Poke - Unnecessarily Slow Tests

**Problem:** Tests take too long to run.

```typescript
// BAD - Real network call
it('should fetch user data', async () => {
  const response = await fetch('https://api.example.com/users/1');
  const user = await response.json();
  expect(user.name).toBeDefined();
});

// GOOD - Mocked network
it('should parse user response', async () => {
  mockFetch.mockResolvedValue({
    json: () => Promise.resolve({ id: 1, name: 'Test User' })
  });

  const user = await fetchUser(1);
  expect(user.name).toBe('Test User');
});
```

**Target:** Unit tests < 100ms, Integration tests < 1s.

### 7. The Chain Gang - Test Dependency

**Problem:** Tests depend on other tests running first.

```typescript
// BAD - Tests must run in order
describe('User operations', () => {
  let userId;

  it('should create user', () => {
    userId = createUser(); // Sets state for next test
    expect(userId).toBeDefined();
  });

  it('should update user', () => {
    updateUser(userId, newData); // Depends on previous test
    expect(getUser(userId).name).toBe(newData.name);
  });
});

// GOOD - Each test is independent
describe('User operations', () => {
  it('should create user', () => {
    const userId = createUser();
    expect(userId).toBeDefined();
  });

  it('should update user', () => {
    const userId = createUser(); // Creates its own user
    updateUser(userId, newData);
    expect(getUser(userId).name).toBe(newData.name);
  });
});
```

### 8. The Secret Catcher - Hidden Test Logic

**Problem:** Test logic is hidden in helpers or setup.

```typescript
// BAD - Assertions hidden in helper
function assertValidUser(user) {
  expect(user.id).toBeDefined();
  expect(user.email).toMatch(/@/);
  expect(user.createdAt).toBeInstanceOf(Date);
  // Many more hidden assertions
}

it('should create valid user', () => {
  const user = createUser(data);
  assertValidUser(user); // What is actually being tested?
});

// GOOD - Explicit assertions
it('should create user with email', () => {
  const user = createUser(data);
  expect(user.email).toBe(data.email);
});
```

## Anti-Pattern Detection Checklist

When reviewing tests, watch for:

- [ ] Tests without meaningful assertions
- [ ] Tests with more than 5-7 assertions
- [ ] Tests that mock everything
- [ ] Tests that access private methods/properties
- [ ] Tests with sleep/wait calls
- [ ] Tests that depend on test execution order
- [ ] Tests with complex setup that obscures intent

## Refactoring Strategies

1. **Too many assertions** → Split into multiple tests
2. **Over-mocking** → Use real implementations or fakes
3. **Flaky tests** → Control time, mock external calls
4. **Slow tests** → Mock I/O, parallelize independent tests
5. **Hidden logic** → Inline or clearly name helpers

## When to Delete Tests

Tests that:
- Always pass regardless of implementation
- Test third-party library behavior
- Are permanently flaky without fix
- Duplicate other tests exactly
- Test deprecated code
