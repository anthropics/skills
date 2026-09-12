---
name: tiered-test-generator
description: Generate tiered knowledge-verification questions (quiz/exam) at 3 difficulty levels with grading and diagnostics. For testing UNDERSTANDING of code, concepts, or architecture — NOT for writing software tests (use engineering:testing-strategy for that). Triggers on "문제 만들어", "quiz", "검증 문제", "이해도 확인", "knowledge check", "challenge me", "시험 문제", "면접 문제".
argument-hint: "[topic or code to generate tests for]"
allowed-tools: Read, Grep, Glob, Bash
---

# Tiered Test Generator

Multi-level verification question and test scenario generator.


## Rules (Absolute)

1. **Questions must be answerable.** Every question has a definite correct answer or clear evaluation criteria. No subjective trick questions.
2. **Difficulty must be genuine.** Tier 3 questions should be genuinely hard, not just verbose versions of Tier 1.
3. **Coverage must be systematic.** Questions should cover the full topic, not cluster around one subtopic.
4. **Source traceability.** For code-based questions, every question must reference specific files, lines, or behaviors.
5. **No answer leakage.** Questions must not contain hints that give away the answer.

## Tier System

### Tier 1: Conceptual (Understanding)
- **Difficulty:** Foundation
- **Tests:** Can you explain what this does and why?
- **Format:** Definition, purpose, comparison questions
- **Bloom's Level:** Remember, Understand

### Tier 2: Applied (Usage)
- **Difficulty:** Intermediate
- **Tests:** Can you use this correctly in context?
- **Format:** Scenario-based, debugging, "what happens when" questions
- **Bloom's Level:** Apply, Analyze

### Tier 3: Expert (Mastery)
- **Difficulty:** Advanced
- **Tests:** Can you handle edge cases, design alternatives, and teach it?
- **Format:** Edge cases, trade-off analysis, design challenges, "teach this to someone" prompts
- **Bloom's Level:** Evaluate, Create

## Test Types

### Type A: Code Comprehension
For testing understanding of specific code.

```markdown
**[T1] Q1.** What is the primary responsibility of the `UserService` class?
a) Database access
b) Authentication
c) User CRUD operations
d) Session management

**[T2] Q2.** Given this function, what happens when `input` is `null`?
```python
def process(input):
    return input.strip().lower()
```
a) Returns empty string
b) Raises AttributeError
c) Returns None
d) Silently fails

**[T3] Q3.** The current error handling in `api/routes.py:45-60` catches all exceptions generically. Design a more robust error handling strategy that:
- Distinguishes client errors from server errors
- Provides actionable error messages
- Doesn't leak internal details
- Supports error aggregation for monitoring
```

### Type B: Architecture & Design
For testing system-level understanding.

```markdown
**[T1] Q1.** What architectural pattern does this codebase follow?

**[T2] Q2.** If read traffic increases 100x, which component becomes the bottleneck first? What's your mitigation strategy?

**[T3] Q3.** The current system uses synchronous inter-service communication. Design a migration path to event-driven architecture that:
- Has zero downtime
- Can be rolled back at any stage
- Preserves data consistency guarantees
```

### Type C: Process & Methodology
For testing workflow and best-practice knowledge.

```markdown
**[T1] Q1.** What is the purpose of a code review?

**[T2] Q2.** Given this PR with 3 changed files, identify the 2 most important review comments you would make.

**[T3] Q3.** Design a CI/CD pipeline for this project that balances speed with safety. Justify each stage's inclusion and the order.
```

### Type D: Concept Mastery
For testing domain knowledge.

```markdown
**[T1] Q1.** Define "eventual consistency" in your own words.

**[T2] Q2.** Your system uses eventual consistency for user profiles. A user updates their email and immediately tries to log in with the new email. What happens? How do you handle it?

**[T3] Q3.** Compare eventual consistency vs. strong consistency for a financial transaction system. Under what specific conditions would you choose eventual consistency despite the risks?
```

## Process

### Step 1: Analyze the Subject

- If code: Read the files, understand the structure
- If concept: Define the scope and depth
- If architecture: Map the components

### Step 2: Generate Question Set

Default: 3 questions per tier (9 total).
Customizable: user can specify count per tier.

Distribution:
```
Tier 1 (Conceptual):  3 questions — foundation verification
Tier 2 (Applied):     3 questions — practical understanding
Tier 3 (Expert):      3 questions — mastery and edge cases
```

### Step 3: Create Answer Key

For each question:
- **Correct answer** with explanation
- **Why wrong answers are wrong** (for multiple choice)
- **Grading rubric** (for open-ended questions)

### Step 4: Deliver

Present questions without answers. Hold answer key until user submits responses.

## Output Format

```markdown
## Test: [Topic]

### Instructions
- [N] questions across 3 difficulty tiers
- Answer all questions, then submit for grading
- Open-ended questions: aim for 2-3 sentences

---

### Tier 1: Conceptual

**Q1.** [question]
a) [option]  b) [option]  c) [option]  d) [option]

**Q2.** [question]

**Q3.** [question]

---

### Tier 2: Applied

**Q4.** [scenario + question]

**Q5.** [debugging scenario]

**Q6.** [what-happens-when scenario]

---

### Tier 3: Expert

**Q7.** [edge case challenge]

**Q8.** [design challenge]

**Q9.** [trade-off analysis]

---

> Submit your answers and I'll grade them with detailed feedback.
```

## Grading (Post-Submission)

When user submits answers:

```markdown
## Results: [Topic]

### Score: [X]/100

### Answer Review
| Q# | Tier | Result | Score |
|----|------|--------|-------|
| 1  | T1   | O/X    | /10   |
| 2  | T1   | O/X    | /10   |
| ...| ...  | ...    | ...   |

### Detailed Feedback

#### Q[N] — [X] Incorrect
**Your answer:** [what they said]
**Correct answer:** [what it should be]
**Why:** [explanation of the correct answer]
**Key insight:** [what understanding gap this reveals]

### Diagnostic Summary
| Dimension | Assessment |
|-----------|-----------|
| Concept Connectivity | [How well fundamentals are linked] |
| Procedural Stability | [How reliably they can apply knowledge] |
| Meta-Cognition | [How well they know what they don't know] |

### Recommended Next Steps
- [Specific topics to review based on wrong answers]
```

## When to Use

- After learning something new — verify understanding
- Before a code review — test your own knowledge of the codebase
- Interview preparation — generate practice questions
- Team knowledge assessment — create standardized tests
- After refactoring — verify nothing was lost in translation
- Teaching/documentation — create practice exercises

## When NOT to Use

- For subjective opinion questions (no right answer)
- When the user just wants information (use `deep-dive-analyzer`)
- For trivial topics that don't warrant testing

## Integration Notes

- **After deep-dive-analyzer:** Analyze → Generate tests to verify understanding
- **With skill-composer:** Part of the "Deep Learning Pipeline" (analyze → test → fill gaps → iterate)
- **With adversarial-review:** Tests verify understanding; adversarial review challenges decisions
