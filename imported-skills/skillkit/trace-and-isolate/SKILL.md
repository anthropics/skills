---
name: trace-and-isolate
description: Applies systematic tracing and isolation techniques to pinpoint exactly where a bug originates in code. Use when a bug is hard to locate, code is not working as expected, an error or crash appears with unclear cause, a regression was introduced between recent commits, or you need to narrow down which component, function, or line is faulty. Covers binary search debugging, git bisect for regressions, strategic logging with [TRACE] patterns, data and control flow tracing, component isolation, minimal reproduction cases, conditional breakpoints, and watch expressions across TypeScript, SQL, and bash.
version: 1.0.0
triggers:
  - trace execution
  - isolate bug
  - narrow down
  - binary search debugging
  - find where
tags:
  - debugging
  - tracing
  - isolation
  - bisect
difficulty: intermediate
estimatedTime: 15
relatedSkills:
  - debugging/root-cause-analysis
  - debugging/hypothesis-testing
---

# Trace and Isolate

You are using systematic tracing and isolation techniques to narrow down where a bug originates. The goal is to find the exact location in code where behavior diverges from expectation.

## Quick Reference

| Scenario | Technique |
|---|---|
| Large codebase / complex flow | Binary search debugging |
| Bug appeared between commits | `git bisect` |
| Unclear data transformation | Strategic `[TRACE]` logging |
| Which component is faulty? | Component isolation + mocks |
| Bug hard to reproduce | Minimal reproduction case |
| Conditional or intermittent bug | Conditional breakpoints / watch expressions |

## Binary Search Debugging

When you have a large codebase or complex flow:

1. **Identify the start** - Last known good state
2. **Identify the end** - First observed bad state
3. **Test the middle** - Check if behavior is good or bad
4. **Repeat** - Binary search on the half with the bug

### Code Path Binary Search

```
Start: User clicks submit button
End: Error shown to user

Midpoint 1: Form validation
→ Data looks correct here? Continue to later code
→ Data already wrong? Focus on earlier code

Midpoint 2: API request construction
→ Request payload correct? Focus on server side
→ Payload already malformed? Focus on form handling

...Continue until exact line is found
```

### Git Bisect for Regressions

When a bug appeared between two commits:

```bash
# Start bisect
git bisect start

# Mark current (broken) state as bad
git bisect bad

# Mark last known good state
git bisect good v2.3.0

# Git checks out middle commit, test and mark
git bisect good  # or git bisect bad

# Repeat until found
# Git will report: "abc123 is the first bad commit"

# Clean up
git bisect reset
```

Automated bisect with test script:
```bash
git bisect start HEAD v2.3.0
git bisect run npm test -- --grep "failing test"
```

## Tracing Techniques

### Strategic Logging

Add temporary logging at key points:

```typescript
function processOrder(order) {
  console.log('[TRACE] processOrder input:', JSON.stringify(order));

  const validated = validateOrder(order);
  console.log('[TRACE] after validation:', JSON.stringify(validated));

  const priced = calculatePrice(validated);
  console.log('[TRACE] after pricing:', JSON.stringify(priced));

  const result = submitOrder(priced);
  console.log('[TRACE] final result:', JSON.stringify(result));

  return result;
}
```

Log template: `[TRACE] <location>: <what> = <value>`

### Data Flow Tracing

Track how data transforms through the system:

```
Input: { userId: "123", items: [...] }
    ↓
validateUser() → { userId: "123", verified: true }
    ↓
enrichItems() → { userId: "123", verified: true, items: [...enriched] }
    ↓
calculateTotals() → { ..., subtotal: 100, tax: 8, total: 108 }
    ↓
Output: { orderId: "456", total: 108 }
```

At each step, verify:
- Is the input what you expected?
- Is the output what you expected?
- Where does expected diverge from actual?

### Control Flow Tracing

Track which code paths execute:

```typescript
function handleRequest(req) {
  console.log('[TRACE] handleRequest entered');

  if (req.authenticated) {
    console.log('[TRACE] authenticated path');
    if (req.isAdmin) {
      console.log('[TRACE] admin path');
      return handleAdminRequest(req);
    } else {
      console.log('[TRACE] user path');
      return handleUserRequest(req);
    }
  } else {
    console.log('[TRACE] unauthenticated path');
    return handlePublicRequest(req);
  }
}
```

## Isolation Techniques

### Component Isolation

Test components in isolation to determine which is faulty:

```
Full System: Frontend → API → Database
              ↓
Test 1: Frontend → Mock API
        → Works? Problem is in API or Database

Test 2: Real API → Mock Database
        → Works? Problem is in Database

Test 3: API with minimal data
        → Works? Problem is data-dependent
```

### Minimal Reproduction

Strip away everything non-essential:

1. **Remove unrelated code** - Comment out or delete
2. **Simplify data** - Use minimal test data
3. **Remove dependencies** - Mock external services
4. **Reduce scope** - Single function/component

Goal: Smallest possible code that still shows the bug

### Environment Isolation

Eliminate environmental factors:

- [ ] Same behavior in different browsers?
- [ ] Same behavior on different machines?
- [ ] Same behavior with fresh data?
- [ ] Same behavior after clearing cache?
- [ ] Same behavior with default config?

## Breakpoint Strategies

### Strategic Breakpoint Placement

```typescript
function complexFunction(input) {
  // BREAKPOINT 1: Entry - check input
  const step1 = transform(input);
  // BREAKPOINT 2: After first transformation

  for (const item of step1.items) {
    // BREAKPOINT 3: Inside loop - conditional on item
    process(item);
  }

  // BREAKPOINT 4: Exit - check output
  return finalize(step1);
}
```

### Conditional Breakpoints

Only break when condition is met:
- `item.id === "problematic-id"`
- `count > 100`
- `response.status !== 200`

### Watch Expressions

Monitor values without stopping:
- `this.state.items.length`
- `performance.now() - startTime`
- `Object.keys(cache).length`

## Isolation Checklist

Before declaring a component faulty:

- [ ] Tested in complete isolation?
- [ ] All inputs verified correct?
- [ ] All dependencies mocked/verified?
- [ ] Tested with known-good data?
- [ ] Reproduced on clean environment?

## Common Isolation Patterns

### Database Isolation
```sql
-- Create isolated test data
BEGIN TRANSACTION;
-- Insert test data
-- Run test queries
-- Verify results
ROLLBACK;
```

### Network Isolation
```typescript
// Intercept and log all network requests
const originalFetch = window.fetch;
window.fetch = async (...args) => {
  console.log('[TRACE] fetch:', args[0]);
  const response = await originalFetch(...args);
  console.log('[TRACE] response:', response.status);
  return response;
};
```

### Time Isolation
```typescript
// Control time for debugging
const realNow = Date.now;
Date.now = () => {
  const time = realNow();
  console.log('[TRACE] Date.now():', new Date(time).toISOString());
  return time;
};
```

## When to Move On

Stop isolating when you have:
- Exact file and line number
- Minimal reproduction case
- Clear understanding of trigger conditions
- Evidence for root cause hypothesis
