---
name: "postmortem"
description: "/em:postmortem — Honest analysis of what went wrong. Use after a failed launch, missed quarter, or bad hire to run a blameless 5-Whys retrospective with a change register — e.g. dissecting why the Q3 release slipped six weeks."
---

# /em:postmortem — Honest Analysis of What Went Wrong

**Command:** `/em:postmortem <event>`

Not blame. Understanding. The failed deal, the missed quarter, the feature that flopped, the hire that didn't work out. What actually happened, why, and what changes as a result.

---

## Why Most Post-Mortems Fail

They become one of two things:

**The blame session** — someone gets scapegoated, defensive walls go up, actual causes don't get examined, and the same problem happens again in a different form.

**The whitewash** — "We learned a lot, we're going to do better, here are 12 vague action items." Nothing changes. Same problem, different quarter.

A real post-mortem is neither. It's a rigorous investigation into a system failure. Not "whose fault was it" but "what conditions made this outcome predictable in hindsight?"

**The purpose:** extract the maximum learning value from a failure so you can prevent recurrence and improve the system.

---

## The Framework

### Step 1: Define the Event Precisely

Before analysis: describe exactly what happened.

- What was the expected outcome?
- What was the actual outcome?
- When was the gap first visible?
- What was the impact (financial, operational, reputational)?

Precision matters. "We missed Q3 revenue" is not precise enough. "We closed $420K in new ARR vs $680K target — a $260K miss driven primarily by three deals that slipped to Q4 and one deal that was lost to a competitor" is precise.

### Step 2: The 5 Whys — Done Properly

The goal: get from **what happened** (the symptom) to **why it happened** (the root cause).

Standard bad 5 Whys:
- Why did we miss revenue? Because deals slipped.
- Why did deals slip? Because the sales cycle was longer than expected.
- Why? Because the customer buying process is complex.
- Why? Because we're selling to enterprise.
- Why? That's just how enterprise sales works.

→ Conclusion: Nothing to do. It's just enterprise.

Real 5 Whys:
- Why did we miss revenue? Three deals slipped out of quarter.
- Why did those deals slip? None of them had identified a champion with budget authority.
- Why did we progress deals without a champion? Our qualification criteria didn't require it.
- Why didn't our qualification criteria require it? When we built the criteria 8 months ago, we were in SMB, not enterprise.
- Why haven't we updated qualification criteria as ICP shifted? No owner, no process for criteria review.

→ Root cause: Qualification criteria outdated, no owner, no review process.
→ Fix: Update criteria, assign owner, add quarterly review.

**The test for a good root cause:** Could you prevent recurrence with a specific, concrete change? If yes, you've found something real.

### Step 3: Distinguish Contributing Factors from Root Cause

Most events have multiple contributing factors. Not all are root causes.

**Contributing factor:** Made it worse, but isn't the core reason. If removed, the outcome might have been different — but the same class of problem would recur.

**Root cause:** The fundamental condition that made the outcome probable. Fix this, and this class of problem doesn't recur.

Example — failed hire:
- Contributing factors: rushed process, reference checks skipped, team under pressure to staff up
- Root cause: No defined competency framework, so interview process varied by who happened to conduct interviews

**The distinction matters.** If you address only contributing factors, you'll have a different-looking but structurally identical failure next time.

### Step 4: Identify the Warning Signs That Were Ignored

Every failure has precursors. In hindsight, they're obvious. The value of this step is making them obvious prospectively.

Ask:
- At what point was the negative outcome predictable?
- What signals were visible at that point?
- Who saw them? What happened when they raised them?
- Why weren't they acted on?

**Common patterns:**
- Signal was raised but dismissed by a senior person
- Signal wasn't raised because nobody felt safe saying it
- Signal was seen but no one had clear ownership to act on it
- Data was available but nobody was looking at it
- The team was too optimistic to take negative signals seriously

This step is particularly important for systemic issues — "we didn't feel safe raising the concern" is a much deeper root cause than "the deal qualification was off."

### Step 5: Distinguish What Was in Control vs. Out of Control

Some failures happen despite correct decisions. Some happen because of incorrect decisions. Knowing the difference prevents both overcorrection and undercorrection.

- **In control:** Process, criteria, team capability, resource allocation, decisions made
- **Out of control:** Market conditions, customer decisions, competitor actions, macro events

For things out of control: what can be done to be more resilient to similar events?
For things in control: what specifically needs to change?

**Warning:** "It was outside our control" is sometimes used to avoid accountability. Be rigorous.

### Step 6: Build the Change Register

Every post-mortem ends with a change register — specific commitments, owned and dated.

**Bad action items:**
- "We'll improve our qualification process"
- "Communication will be better"
- "We'll be more rigorous about forecasting"

**Good action items:**
- "Ravi owns rewriting qualification criteria by March 15 to include champion identification as hard requirement. New criteria reviewed in weekly sales standup starting March 22."
- "By March 10, Elena adds deal-slippage risk flag to CRM for any open opportunity >60 days without a product demo"
- "Maria runs a 30-min retrospective with enterprise sales team every 6 weeks starting April 1, reviews win/loss data"

**For each action:**
- What exactly is changing?
- Who owns it?
- By when?
- How will you verify it worked?

### Step 7: Verification Date

The most commonly skipped step. Post-mortems are useless if nobody checks whether the changes actually happened and actually worked.

Set a verification date: "We'll review whether qualification criteria have been updated and whether deal slippage rate has improved at the June board meeting."

Without this, post-mortems are theater.

---

## Post-Mortem Output Format

```
EVENT: [Name and date]
EXPECTED: [What was supposed to happen]
ACTUAL: [What happened]
IMPACT: [Quantified]

TIMELINE
[Date]: [What happened or was visible]
[Date]: ...

5 WHYS
1. [Why did X happen?] → Because [Y]
2. [Why did Y happen?] → Because [Z]
3. [Why did Z happen?] → Because [A]
4. [Why did A happen?] → Because [B]
5. [Why did B happen?] → Because [ROOT CAUSE]

ROOT CAUSE: [One clear sentence]

CONTRIBUTING FACTORS
• [Factor] — how it contributed
• [Factor] — how it contributed

WARNING SIGNS MISSED
• [Signal visible at what date] — why it wasn't acted on

WHAT WAS IN CONTROL: [List]
WHAT WASN'T: [List]

CHANGE REGISTER
| Action | Owner | Due Date | Verification |
|--------|-------|----------|-------------|
| [Specific change] | [Name] | [Date] | [How to verify] |

VERIFICATION DATE: [Date of check-in]
```

---

## The Tone of Good Post-Mortems

Blame is cheap. Understanding is hard.

The goal isn't to establish that someone made a mistake. The goal is to understand why the system produced that outcome — so the system can be improved.

"The salesperson didn't qualify the deal properly" is blame.
"Our qualification framework hadn't been updated when we moved upmarket, and no one owned keeping it current" is understanding.

The first version fires or shames someone. The second version builds a more resilient organization.

Both might be true simultaneously. The distinction is: which one actually prevents recurrence?
