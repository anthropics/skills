# Skill Creator - Quick Reference Guide

## The Skill Creation Workflow at a Glance

```
1. Capture Intent     → What should the skill do? When should it trigger?
2. Write Draft        → Create SKILL.md with metadata and instructions
3. Create Tests       → Write 2-3 realistic test prompts
4. Run Evals          → Execute tests and measure performance
5. Analyze Results    → Review both qualitative and quantitative feedback
6. Iterate & Refine   → Rewrite skill based on results
7. Expand Test Set    → Scale up testing with more prompts
8. Optimize Trigger   → Improve skill description for better triggering
```

## Step 1: Capture Intent

**Goal:** Understand what you're trying to build.

**Key Questions to Answer:**
- What specific task or workflow does this skill handle?
- When should Claude automatically use this skill? (Describe trigger phrases and contexts)
- What are the inputs and outputs?
- Are there edge cases or special scenarios?

**Where to Look for Intent:**
- Existing conversation history (user's workflow so far)
- Tasks the user keeps repeating
- Patterns in how they describe what they want

**Output:** Clear 1-2 sentence description of skill purpose + list of trigger contexts

---

## Step 2: Write Draft SKILL.md

**Minimal Structure:**
```yaml
---
name: skill-identifier
description: What this skill does and when to use it
license: Apache 2.0
---

# Skill Name

## Overview
Brief explanation of the skill's purpose.

## When to Use This Skill
Trigger contexts and scenarios.

## Core Workflow
Step-by-step instructions for Claude using this skill.

## Tips & Best Practices
Helpful patterns and anti-patterns.
```

**Guidelines:**
- Keep under 500 lines if possible (move long sections to references/)
- Use clear hierarchy (## for sections, ### for subsections)
- Include concrete examples for complex instructions
- Explain the "why" behind guidelines, not just the "what"
- Write in imperative form ("Do X" not "You should do X")

**Common Mistakes to Avoid:**
- Vague descriptions that don't explain when to trigger
- Instructions too broad or too narrow
- Missing edge cases or failure modes
- Assuming users know domain-specific jargon

---

## Step 3: Create Test Prompts

**What to Test:**
- **Happy path:** Standard use case where everything works as expected
- **Edge cases:** Unusual but valid inputs (empty data, extreme values, conflicting requirements)
- **Failure modes:** Cases where the skill should gracefully degrade or ask for clarification

**Test Format:**
Save to `evals/evals.json`:
```json
{
  "skill_name": "your-skill-name",
  "evals": [
    {
      "prompt": "A realistic user request that should trigger this skill",
      "expected_contains": ["output fragment 1", "output fragment 2"],
      "expected_exact": null
    }
  ]
}
```

**Writing Good Tests:**
- Use realistic language, not overly formal or simplified
- Test the skill's actual trigger conditions
- For objective outputs (code, transformations), include specific expected results
- For subjective outputs (writing, design), include quality criteria

---

## Step 4: Run Evals & Analyze Results

**Qualitative Evaluation:**
- Does the skill understand the intent correctly?
- Is the output in the expected format?
- Does it handle edge cases gracefully?
- Would a real user find this helpful?

**Quantitative Metrics:**
- **Accuracy:** % of outputs matching expected content
- **Coverage:** % of test cases passing
- **Variance:** Consistency of quality across different inputs
- **Latency:** Time to complete (if applicable)

**Interpreting Results:**
- >90% pass rate: Ready for expansion testing
- 70-89% pass rate: Refine skill logic and retry
- <70% pass rate: Major rework needed

---

## Step 5: Iterate Based on Feedback

**Common Improvements:**
1. **Trigger description too vague** → Add specific trigger phrases and contexts
2. **Output format unexpected** → Add explicit format requirements
3. **Missing edge cases** → Add specific instructions for boundary conditions
4. **Instructions unclear** → Add examples or break into smaller steps
5. **Triggering too often/rarely** → Refine description to be more precise

**Rewrite Process:**
- Keep what works, change what doesn't
- Test new version against same prompts
- Track which changes improved which metrics
- Don't over-optimize for a single test case

---

## Step 6: Expand Test Set

Once core tests pass (>80%), create 5-10 additional tests:
- More variations of the happy path
- Additional edge cases specific to your domain
- Tests from real user requests if available
- Stress tests (very large inputs, complex scenarios)

**Scaling Tips:**
- Batch similar tests together
- Prioritize tests that surfaced problems before
- Add 2-3 tests per iteration, not all at once

---

## Step 7: Optimize Skill Description

**Goal:** Make the skill trigger at the right time with the right frequency.

**Description Structure:**
```
[What it does] [When to use it] [Key triggers] [What it outputs]
```

**Example:**
❌ Bad: "Helps with writing"
✅ Good: "Structured workflow for co-authoring documentation — use when writing proposals, specs, design docs, or decision documents. Guides through context gathering, iterative refinement, and reader testing."

**Trigger Optimization Checklist:**
- [ ] Skill name clearly describes function
- [ ] Description includes specific use cases (2-3 concrete examples)
- [ ] Common trigger phrases appear in description
- [ ] Description explains when NOT to use (if relevant)
- [ ] Length is 2-4 sentences (not too terse, not too long)

**A/B Testing Descriptions:**
- Write 2-3 version variants
- Test with prompts that should/shouldn't trigger
- Measure false positives (triggering incorrectly) and false negatives (not triggering when should)

---

## Troubleshooting Common Issues

| Problem | Possible Cause | Solution |
|---------|---|---|
| Skill never triggers | Description too vague or trigger phrases missing | Add specific trigger contexts and examples to description |
| Skill triggers too often | Too broad description or overlapping scope | Narrow description; clarify when NOT to use |
| Outputs inconsistent quality | Instructions ambiguous or incomplete | Add more examples; break complex steps into smaller ones |
| Tests pass but real users confused | Tests aren't realistic | Add tests based on actual user prompts and confusion |
| Performance slow | Skill doing too much | Break into multiple smaller skills or optimize core logic |

---

## Tips for Different Skill Types

### Decision/Planning Skills
- Test with ambiguous inputs (user doesn't know exactly what they want)
- Include failure cases ("this won't work, here's why")
- Add examples of final output format

### Code Generation Skills
- Test syntax correctness (actually run generated code)
- Include tests for different languages/frameworks
- Test error handling and edge cases

### Writing/Content Skills
- Define quality criteria (tone, length, style)
- Test with diverse input quality levels
- Include tests for different formats/audiences

### Reference/Knowledge Skills
- Test with "find X" queries
- Verify accuracy and freshness of information
- Test with follow-up/clarification questions

---

## Best Practices Summary

**Do:**
- ✅ Start small (3 tests, not 30)
- ✅ Test real-world scenarios
- ✅ Iterate quickly between test and refine
- ✅ Include both happy path and edge cases
- ✅ Document why you made each change
- ✅ Optimize description for human readers, not search engines

**Don't:**
- ❌ Over-test before first draft is solid
- ❌ Use artificial test data that doesn't reflect reality
- ❌ Skip qualitative feedback (numbers alone won't tell the whole story)
- ❌ Optimize for a single test case at the expense of others
- ❌ Make the description so specific it doesn't trigger when it should

---

## Quick Links

- **Skill Template:** `/home/user/Senior-Manager/template/SKILL.md`
- **YAML Syntax:** Check frontmatter in existing skills
- **Full Guide:** See `SKILL.md` for comprehensive workflow details
- **Eval Examples:** Check `TESTING_EXAMPLES.md` in repository root
