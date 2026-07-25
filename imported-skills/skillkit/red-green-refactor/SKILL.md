---
name: red-green-refactor
description: "Guides the red-green-refactor TDD workflow: write a failing test first, implement the minimum code to make it pass, then refactor while keeping tests green. Use when a user asks to practice TDD, write tests first, follow red-green-refactor, do test-driven development, write failing tests before code, or phrases like 'make the test pass', 'test coverage', or 'unit tests before implementation'."
version: 1.0.0
triggers:
  - tdd
  - test driven
  - write tests first
  - red green refactor
  - failing test
tags:
  - tdd
  - testing
  - quality
  - methodology
difficulty: intermediate
estimatedTime: 15
relatedSkills:
  - testing/test-patterns
  - testing/anti-patterns
---

# Red-Green-Refactor Methodology

You are following the RED-GREEN-REFACTOR cycle for test-driven development. Every new feature, bug fix, or behavior change starts with a failing test.

## The Cycle

### 1. RED Phase — Write a Failing Test

1. **Understand the requirement** — what specific behavior must exist?
2. **Write one test** asserting that behavior
3. **Run the test** — it MUST fail (red)
4. **Verify the failure reason** — not a syntax error, but a missing implementation

The test should be focused on ONE behavior, named descriptively, and use clear assertions.

**Executable example (Jest):**
```js
// calculateTotal.test.js
const { calculateTotal } = require('./calculateTotal');

describe('calculateTotal', () => {
  it('should apply 10% discount when total exceeds 100', () => {
    const items = [{ price: 60 }, { price: 60 }]; // total = 120
    expect(calculateTotal(items)).toBe(108); // 120 * 0.90
  });
});
```
Running this now produces: `Cannot find module './calculateTotal'` — correct RED state.

---

### 2. GREEN Phase — Make the Test Pass

Write the **minimum code** needed to pass the test. Don't add anything extra.

```js
// calculateTotal.js
function calculateTotal(items) {
  const total = items.reduce((sum, item) => sum + item.price, 0);
  return total > 100 ? total * 0.9 : total;
}
module.exports = { calculateTotal };
```
Run the test — it passes. GREEN achieved. Stop here; resist adding more logic.

---

### 3. REFACTOR Phase — Improve the Code

With a passing test as your safety net, clean up the implementation. Run tests after every change.

```js
// calculateTotal.js — refactored for clarity
const DISCOUNT_THRESHOLD = 100;
const DISCOUNT_RATE = 0.9;

function calculateTotal(items) {
  const subtotal = items.reduce((sum, { price }) => sum + price, 0);
  return subtotal > DISCOUNT_THRESHOLD ? subtotal * DISCOUNT_RATE : subtotal;
}
module.exports = { calculateTotal };
```
Test still passes — GREEN maintained. Constants now communicate intent.

---

## End-to-End Example: Adding a New Behavior

**Next requirement:** apply a 15% discount when total exceeds 200.

**RED** — write the failing test first:
```js
it('should apply 15% discount when total exceeds 200', () => {
  const items = [{ price: 110 }, { price: 110 }]; // total = 220
  expect(calculateTotal(items)).toBe(187); // 220 * 0.85
});
```

**GREEN** — extend the implementation minimally:
```js
function calculateTotal(items) {
  const subtotal = items.reduce((sum, { price }) => sum + price, 0);
  if (subtotal > 200) return subtotal * 0.85;
  if (subtotal > 100) return subtotal * 0.9;
  return subtotal;
}
```

**REFACTOR** — remove duplication with a tiered structure:
```js
const DISCOUNT_TIERS = [
  { threshold: 200, rate: 0.85 },
  { threshold: 100, rate: 0.9 },
];

function calculateTotal(items) {
  const subtotal = items.reduce((sum, { price }) => sum + price, 0);
  const tier = DISCOUNT_TIERS.find(({ threshold }) => subtotal > threshold);
  return tier ? subtotal * tier.rate : subtotal;
}
```
Both tests pass — ready for the next cycle.

---

## Workflow Steps

1. **Create or open the test file first**
2. **Write ONE failing test** for the smallest testable unit
3. **Implement minimally** — just enough to pass
4. **Refactor if needed** — while tests stay green
5. **Repeat** for the next behavior

## Decision Points

### Write a new test when:
- Adding a new feature or behavior
- Fixing a bug (test the bug first, then fix it)
- Handling an edge case discovered during implementation

### Don't write a test when:
- Pure refactoring (existing tests already cover the behavior)
- Non-functional changes (formatting, comments)
- Third-party library internals

## Verification Checklist

- [ ] All new code has corresponding tests
- [ ] Tests fail when the feature is removed
- [ ] Tests pass consistently (not flaky)
- [ ] Code has been refactored for clarity
- [ ] No unnecessary code was added

## Common Mistakes to Avoid

1. **Writing tests after code** — defeats the design benefit of TDD
2. **Writing multiple tests at once** — one test drives one change
3. **Passing tests with hacks** — the test should drive good design
4. **Skipping the refactor phase** — technical debt accumulates
5. **Testing implementation details** — test behavior, not internals

## Integration with Other Skills

- **test-patterns**: Patterns for structuring tests
- **anti-patterns**: Common testing mistakes to avoid
- **debugging/root-cause-analysis**: When tests reveal unexpected failures
