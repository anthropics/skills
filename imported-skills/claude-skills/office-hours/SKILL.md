---
name: "office-hours"
description: "/cs:office-hours <topic> — YC-style 6-question founder interrogation before any advice. Forces clarity on problem, customer, distribution, defensibility, capital, and founder fit. Use when a founder question is too vague to route — e.g. 'should we grow faster?' — or before drafting a strategy brief."
---

# /cs:office-hours — Six-Question Founder Interrogation

**Command:** `/cs:office-hours <topic>`

Before any advice, the founder must answer six questions. Modeled on YC office hours: no analysis until the founder has done the thinking. This is the cognitive forcing function that prevents drift into solutionism.

## When to Run

- Before starting any major initiative
- Before fundraising
- Before a strategic pivot
- When the founder is excited (excitement is a tell — pressure-test)
- When the answer is "obvious" (the obvious answer is usually wrong)

## The Six Questions

The founder must answer **all six** in writing before any C-role weighs in.

### 1. Problem
**Whose problem is this, and how do they describe it in their own words?**
- Not your framing. Their words.
- If you can't quote a customer, you don't have a problem worth solving.

### 2. Customer
**Who is the ICP? Name one real person who would buy this today.**
- Real human. Real company. Real seat.
- If you can't name one, the ICP isn't ready.

### 3. Distribution
**How does the customer first hear your name?**
- Channel, intent, search query, friend, conference — name it.
- If the answer is "we'll figure out marketing later," the answer is no.

### 4. Defensibility
**If this works, what stops a competitor from copying it in 6 months?**
- Network effects, switching costs, data moat, regulatory moat, brand — pick one.
- "We'll execute better" is not a defense.

### 5. Capital
**What does this cost, when does it pay back, and what's the alternative use of the money?**
- Total spend, payback months, opportunity cost.
- If you don't know, don't approve it.

### 6. Founder Fit
**Why are you the right person to do this — and why does this matter enough to spend the next 3 years on it?**
- Founder-market fit is the strongest predictor of survival.
- If the answer is mercenary, the company will be too.

## Output Format

After the founder answers all six, this command produces a one-page brief:

```markdown
# Office Hours Brief: <topic>
**Date:** YYYY-MM-DD
**Founder:** <name>

## 1. Problem
> [founder's verbatim answer]

## 2. Customer
> [founder's verbatim answer]

## 3. Distribution
> [founder's verbatim answer]

## 4. Defensibility
> [founder's verbatim answer]

## 5. Capital
> [founder's verbatim answer]

## 6. Founder Fit
> [founder's verbatim answer]

---

**Assessment** (one of):
- 🟢 GREEN — ship the brief to /cs:boardroom
- 🟡 YELLOW — sharpen Q[N] before proceeding
- 🔴 RED — kill or redefine; do not proceed
```

## Routing

After the brief is GREEN, route to:
- Single-role question → corresponding `/cs:{role}-review`
- Multi-role question → `/cs:brief` then `/cs:boardroom`

## Why This Works

Most bad decisions don't fail at execution — they fail at framing. Forcing six concrete answers surfaces the framing weaknesses before anyone burns time on analysis. The founder either fills the gaps or recognizes the question wasn't ready.

This is the YC `office hours` pattern adapted for Claude Code: the interrogation is the value.

## Related Commands

- `/cs:brief` — turn the answers into a one-page strategy brief
- `/cs:boardroom` — multi-role deliberation
- `/cs:founder-mode` — let the system pick the next step

## Related Agents

- All cs-* advisors consume the brief output
- `cs-chief-of-staff` triggers `/cs:office-hours` when intake is unclear

---

**Version:** 1.0.0
