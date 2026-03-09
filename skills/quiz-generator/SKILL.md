---
name: quiz-generator
description: Generate quizzes, assessments, and decision-tree evaluations from content. Use when users need to create knowledge checks, certification tests, learning assessments, diagnostic decision trees, or interactive evaluations. Triggers on requests like "create a quiz", "make assessment questions", "build a knowledge check", "generate test questions", "create a decision tree", or "diagnostic flowchart".
---

# Quiz Generator

Transform content into effective assessments using varied question types and decision-tree logic.

## Assessment Types

### Knowledge Checks
Quick verification of understanding after learning content.

### Certification Tests
Formal assessments with scoring thresholds and documented outcomes.

### Diagnostic Decision Trees
Branching logic that guides users to conclusions based on responses.

### Self-Assessments
Reflective evaluations for personal development.

## Question Types

### Multiple Choice

```markdown
**Q1. [Question stem - clear, single concept]**

A) [Plausible distractor]
B) [Correct answer]
C) [Common misconception]
D) [Plausible distractor]

*Correct: B*
*Explanation: [Why B is correct and why others are wrong]*
```

Design principles:
- Stem contains the full question; options complete it
- All options grammatically consistent
- Avoid "all of the above" / "none of the above"
- Distractors based on real misconceptions

### True/False with Justification

```markdown
**Q2. [Statement]**

- [ ] True
- [ ] False

*Correct: [True/False]*
*Justification required: Explain your reasoning in 1-2 sentences.*
```

### Matching

```markdown
**Q3. Match each [item type] with its [property]:**

| Item | Property |
|------|----------|
| 1. [Item A] | A) [Property X] |
| 2. [Item B] | B) [Property Y] |
| 3. [Item C] | C) [Property Z] |

*Answers: 1-B, 2-C, 3-A*
```

### Ordering/Sequencing

```markdown
**Q4. Arrange these steps in the correct order:**

- [ ] Step C
- [ ] Step A
- [ ] Step D
- [ ] Step B

*Correct order: A, B, C, D*
```

### Scenario-Based

```markdown
**Q5. Scenario:**
[Realistic situation with relevant details]

**Question:** [What action/decision/analysis is needed?]

A) [Option addressing scenario]
B) [Option addressing scenario]
C) [Option addressing scenario]
D) [Option addressing scenario]

*Correct: [Letter]*
*Rationale: [Why this is the best response given the scenario]*
```

## Decision Tree Structure

### Basic Flow

```markdown
# [Diagnostic Title]

## Start

**Question 1: [Initial assessment question]**

→ If YES: Go to Question 2A
→ If NO: Go to Question 2B
→ If UNSURE: [Clarification or default path]

---

## Question 2A: [Follow-up for YES path]

→ If [Condition]: **Result A** - [Conclusion/recommendation]
→ If [Other condition]: Go to Question 3A

---

## Question 2B: [Follow-up for NO path]

→ If [Condition]: **Result B** - [Conclusion/recommendation]
→ If [Other condition]: Go to Question 3B
```

### Decision Tree with Scoring

```markdown
# [Assessment Title]

Track your score as you proceed.

## Q1: [Question]
- Yes (+2 points) → Q2
- Somewhat (+1 point) → Q2
- No (0 points) → Q3

## Q2: [Question]
...

## Results

**Score 8-10**: [Category A outcome]
**Score 5-7**: [Category B outcome]
**Score 0-4**: [Category C outcome]
```

### Diagnostic Flowchart Format

```
┌─────────────────────────┐
│    START: [Symptom]     │
└───────────┬─────────────┘
            │
            ▼
    ┌───────────────┐
    │ [Question 1]? │
    └───────┬───────┘
       YES/ \NO
         /   \
        ▼     ▼
   [Path A] [Path B]
        │     │
        ▼     ▼
   [Result] [Next Q]
```

## Content-to-Quiz Workflow

### 1. Analyze Source Material

Extract:
- Key concepts (definitions, principles)
- Procedures (sequences, steps)
- Relationships (cause-effect, compare-contrast)
- Common errors/misconceptions

### 2. Define Learning Objectives

Map questions to objectives:

| Objective | Bloom's Level | Question Type |
|-----------|---------------|---------------|
| Define terms | Remember | Multiple choice, matching |
| Explain process | Understand | Ordering, short answer |
| Apply procedure | Apply | Scenario-based |
| Diagnose issues | Analyze | Decision tree |
| Evaluate options | Evaluate | Case study |

### 3. Generate Questions

For each objective, create questions that:
- Test ONE concept per question
- Use vocabulary from source material
- Include realistic distractors
- Provide explanatory feedback

### 4. Build Decision Logic

For diagnostic assessments:
- Identify the possible outcomes first
- Work backward to discriminating questions
- Ensure all paths lead to defined outcomes
- Add escape routes for edge cases

## Quality Standards

### Question Quality
- [ ] Clear, unambiguous stem
- [ ] Single correct answer (or clearly defined criteria)
- [ ] Distractors are plausible but clearly wrong
- [ ] No trick questions or gotchas
- [ ] Appropriate difficulty for audience

### Assessment Quality
- [ ] Covers all learning objectives
- [ ] Balanced difficulty distribution
- [ ] Clear instructions and scoring
- [ ] Feedback explains correct answers
- [ ] Time estimate provided

### Decision Tree Quality
- [ ] All paths lead to defined outcomes
- [ ] No dead ends or loops
- [ ] Clear, binary decision points
- [ ] Edge cases handled
- [ ] Can be followed without expert knowledge

## Output Formats

### Interactive HTML Quiz

```html
<!-- Quiz container with JavaScript for scoring -->
<div class="quiz" data-passing-score="80">
  <div class="question" data-correct="b">
    <p>Question text</p>
    <label><input type="radio" name="q1" value="a"> Option A</label>
    <label><input type="radio" name="q1" value="b"> Option B</label>
  </div>
</div>
```

### Printable Assessment

```markdown
# [Assessment Title]
**Time allowed**: [X minutes]
**Passing score**: [X]%

## Instructions
[How to complete and submit]

## Questions
[Numbered questions with answer spaces]

---
## Answer Key (Instructor Copy)
[Answers with point values and explanations]
```

### Decision Tree Document

```markdown
# [Diagnostic Name]

## How to Use
Start at Question 1. Follow the arrows based on your answers.

## Flowchart
[Visual or text-based decision tree]

## Outcome Definitions
[Detailed explanation of each possible result]
```
