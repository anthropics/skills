---
name: structured-code-review
description: Performs a structured five-stage code review covering requirements compliance, correctness, code quality, testing, and security/performance. Each stage uses targeted checklists and categorized feedback (Blocker/Major/Minor/Nit) with actionable suggestions and rationale. Use when the user asks for code review, PR feedback, pull request review, or wants their code checked for bugs, style issues, or vulnerabilities — triggered by phrases like "review my code", "check this PR", "review my changes", "pull request review", or "code feedback".
version: 1.0.0
triggers:
  - code review
  - review this
  - feedback on code
  - PR review
  - review my changes
tags:
  - collaboration
  - code-review
  - quality
  - feedback
difficulty: intermediate
estimatedTime: 15
relatedSkills:
  - collaboration/parallel-investigation
  - planning/verification-gates
---

# Structured Code Review

You are performing a structured, multi-stage code review. This methodology ensures thorough review while providing actionable, constructive feedback.

## Core Principle

**Review in stages. Each stage has a specific focus. Don't mix concerns.**

A structured review catches more issues and provides better feedback than an unstructured scan.

## Review Stages

### Stage 1: Requirements Compliance

First, verify the code meets its requirements.

**Checklist:**
- [ ] Implements stated requirements
- [ ] Handles specified edge cases
- [ ] No scope creep (unexpected additions)
- [ ] No missing functionality

**Feedback at this stage:**
- "This doesn't appear to handle the case when X is empty"
- "The requirement specified Y, but this implements Z"
- "This adds feature F which wasn't requested - is that intentional?"

### Stage 2: Correctness

Next, verify the code works correctly.

**Checklist:**
- [ ] Logic is sound
- [ ] No obvious bugs
- [ ] Error paths are handled
- [ ] No unfinished code (TODOs without tickets)

**Feedback at this stage:**
- "This will throw if `user` is null"
- "The loop exits early before processing all items"
- "What happens when the API call fails?"

### Stage 3: Code Quality

Then, evaluate code quality and maintainability.

**Checklist:**
- [ ] Clear naming
- [ ] Reasonable function/method length
- [ ] No unnecessary complexity
- [ ] Follows project conventions
- [ ] Appropriate abstractions

**Feedback at this stage:**
- "Could you rename `data` to `userProfile` for clarity?"
- "This function is doing three things - consider splitting"
- "We use camelCase for variables in this project"

### Stage 4: Testing

Evaluate test coverage and quality.

**Checklist:**
- [ ] New code has tests
- [ ] Tests cover main paths and edge cases
- [ ] Tests are readable and maintainable
- [ ] Tests don't test implementation details

**Feedback at this stage:**
- "Please add a test for the error case"
- "This test will break if we change the implementation"
- "Consider using a parameterized test for these cases"

### Stage 5: Security & Performance

Finally, check for security and performance concerns.

**Checklist:**
- [ ] No SQL injection, XSS, etc.
- [ ] Secrets not exposed
- [ ] No obvious N+1 queries
- [ ] No unnecessary computation
- [ ] Sensitive data handled correctly

**Feedback at this stage:**
- "This input should be sanitized before use"
- "Consider adding an index for this query"
- "This API key should come from environment variables"

## Writing Good Feedback

### Feedback Levels

| Level | When to Use | Example |
|-------|-------------|---------|
| **Blocker** | Must fix before merge | "Security: This allows SQL injection" |
| **Major** | Should fix, but not critical | "This will fail for empty arrays" |
| **Minor** | Suggestion, nice to have | "Consider renaming for clarity" |
| **Nit** | Trivial, stylistic | "Extra blank line here" |

### Constructive Feedback Template

```
[Level] [Category]: [Issue]

**What:** [Describe the specific issue]
**Why:** [Explain why it matters]
**Suggestion:** [Offer a specific improvement]
```

Example:
```
[Major] Correctness: Null reference possible

**What:** `user.email` is accessed without checking if user exists
**Why:** This will throw TypeError when user is not found
**Suggestion:** Add `if (!user) return null;` before accessing properties
```

## Review Checklist Summary

```markdown
## Review: [PR Title]

### Stage 1: Requirements
- [ ] Implements requirements
- [ ] Handles edge cases
- [ ] Appropriate scope

### Stage 2: Correctness
- [ ] Logic is sound
- [ ] No bugs
- [ ] Errors handled

### Stage 3: Quality
- [ ] Readable
- [ ] Follows conventions
- [ ] Maintainable

### Stage 4: Testing
- [ ] Has tests
- [ ] Tests are good

### Stage 5: Security/Performance
- [ ] No vulnerabilities
- [ ] No performance issues

### Verdict: [ ] Approve [ ] Request Changes [ ] Comment
```

## Integration with Other Skills

- **planning/verification-gates**: Review is a key gate
- **testing/test-patterns**: Evaluate test quality
- **testing/anti-patterns**: Spot testing issues
