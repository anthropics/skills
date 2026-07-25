---
name: hypothesis-testing
description: Applies the scientific method to debugging by helping users form specific, testable hypotheses, design targeted experiments, and systematically confirm or reject theories to find root causes. Use when a user says their code isn't working, they're getting an error, something broke, they want to troubleshoot a bug, or they're trying to figure out what's causing an issue. Concrete actions include isolating failing components, forming and testing hypotheses, analyzing error messages, tracing execution paths, and interpreting test results to narrow down root causes.
version: 1.0.0
triggers:
  - hypothesis
  - theory about bug
  - might be caused by
  - test theory
  - prove theory
tags:
  - debugging
  - scientific-method
  - investigation
  - validation
difficulty: intermediate
estimatedTime: 15
relatedSkills:
  - debugging/root-cause-analysis
  - debugging/trace-and-isolate
---

# Hypothesis-Driven Debugging

You are applying the scientific method to debugging. Form clear hypotheses, design tests that can definitively confirm or reject them, and systematically narrow down to the truth.

## Core Principle

**Every debugging action should test a specific hypothesis. Random changes are not debugging.**

## The Scientific Debugging Method

### 1. Observe - Gather Facts

Before forming hypotheses, collect observations:

- What exactly happens? (specific symptoms)
- When does it happen? (timing, frequency)
- Where does it happen? (environment, component)
- What changed recently? (code, config, data)

**Write down observations objectively:**
```
Observations:
- API returns 500 error on POST /orders
- Happens only when cart has > 10 items
- Started after deployment on 2024-01-15
- Works fine in staging environment
- Error logs show "connection refused" to inventory service
```

### 2. Hypothesize - Form Testable Theories

**Examples (bad → good):**
- ~~"Something is wrong with the network"~~ → "The inventory service connection pool is exhausted when processing orders with >10 items"
- ~~"There might be a race condition"~~ → "The order processing timeout (5s) is insufficient for large orders"

### 3. Predict - Define Expected Results

For each hypothesis, define what you expect to observe if it is true versus false:

```
Hypothesis: Connection pool exhausted for large orders

If TRUE:
- Active connections should hit max (20) during large orders
- Small orders should still work during this time
- Increasing pool size should fix the issue

If FALSE:
- Connection count stays well below max
- Small orders also fail during the issue
- Pool size change has no effect
```

### 4. Test - Experiment Systematically

Design tests that definitively confirm or reject:

```
Test Plan for Connection Pool Hypothesis:

1. Add connection pool monitoring
   - Log active connections before/after each request
   - Expected if true: Count reaches 20 during failures

2. Artificial stress test
   - Send 5 large orders simultaneously
   - Expected if true: Failures start when pool exhausted

3. Increase pool size to 50
   - Repeat stress test
   - Expected if true: Failures stop or threshold moves

4. Control test with small orders
   - Send 20 small orders simultaneously
   - Expected if true: No failures (faster processing)
```

### 5. Analyze - Interpret Results

After testing:

- Did results match predictions for TRUE or FALSE?
- Are results conclusive or ambiguous?
- Do results suggest a different hypothesis?

```
Results:
- Connection count reached 20/20 during failures ✓
- Small orders succeeded during same period ✓
- Pool size increase to 50 → failures stopped ✓

Conclusion: Hypothesis CONFIRMED
Connection pool exhaustion is the proximate cause.

New question: Why do large orders exhaust the pool?
New hypothesis: Large orders make multiple inventory calls per item
```

## Hypothesis Tracking Template

```markdown
## Bug: [Description]

### Hypothesis 1: [Theory]
**Status:** Testing | Confirmed | Rejected
**Probability:** High | Medium | Low

**Evidence For:**
- [Evidence 1]
- [Evidence 2]

**Evidence Against:**
- [Evidence 1]

**Test Plan:**
1. [Test 1] - Expected result if true
2. [Test 2] - Expected result if false

**Test Results:**
- [Result 1]: [Supports/Contradicts]
- [Result 2]: [Supports/Contradicts]

**Conclusion:** [Confirmed/Rejected] because [reasoning]

---

### Hypothesis 2: [Next Theory]
...
```

## Testing Techniques by Hypothesis Type

### Testing Timing Hypotheses
```typescript
// Add timing instrumentation
const start = performance.now();
await suspectedSlowOperation();
const duration = performance.now() - start;
console.log(`Operation took ${duration}ms`);
// Hypothesis confirmed if duration > expected
```

### Testing Data Hypotheses
```typescript
// Validate data at key points
function processWithValidation(data) {
  console.assert(data.id != null, 'Missing id');
  console.assert(data.items?.length > 0, 'Empty items');
  console.assert(typeof data.total === 'number', 'Invalid total');
  // If assertions fail, data hypothesis likely true
}
```

### Testing State Hypotheses
```typescript
// Snapshot state before and after
const stateBefore = JSON.stringify(currentState);
suspectedStateMutation();
const stateAfter = JSON.stringify(currentState);
if (stateBefore !== stateAfter) {
  console.log('State changed:', diff(stateBefore, stateAfter));
}
```

## Decision Tree

```
Is the hypothesis testable?
├── NO → Refine it to be more specific
└── YES → Can I test it without side effects?
    ├── NO → Design a safe test (staging, logs-only)
    └── YES → Run the test
        └── Results conclusive?
            ├── NO → Design a better test
            └── YES → Hypothesis confirmed or rejected?
                ├── CONFIRMED → Root cause found?
                │   ├── YES → Fix and verify
                │   └── NO → Form next hypothesis (why?)
                └── REJECTED → Form next hypothesis
```

## Integration with Other Skills

- **root-cause-analysis**: Hypothesis testing is a key technique within RCA
- **trace-and-isolate**: Use tracing to gather evidence for hypotheses
- **testing/red-green-refactor**: Write test that confirms the bug before fixing
