# When to Stop Grilling

This reference answers exactly one decision: **when is "shared understanding" actually reached, and how do we know to stop the interrogation?**

Pair with `scripts/grill_session_tracker.py` — the session tracker shows progress and surfaces unanswered branches.

## Matt Pocock's Stopping Condition (Implicit)

> "Interview me relentlessly about every aspect of this plan until we reach a shared understanding."
>
> — Matt Pocock, grill-me SKILL.md

"Shared understanding" is the stopping condition. But what does that mean operationally?

## Three Conditions That Mean "Stop"

### Condition 1: Every decision branch has an answer

Track via `grill_session_tracker.py status`. When `percent_complete = 100%`, every detected branch has a recorded answer. Stop grilling.

**Risk:** The extractor missed branches. Run `decision_tree_extractor.py` once more after answers are in — sometimes answers reveal new branches.

### Condition 2: No new questions arise from the last 3 answers

If the last 3 answers all triggered follow-up questions, grilling continues. If 3 answers in a row resolve cleanly with no new questions, the tree is exhausted.

**Pattern:** count the rate of new-question generation per turn. When it drops to zero for 3+ turns, stop.

### Condition 3: The interrogator can predict the answerer's response

If the interrogator can predict, with high confidence, what the answerer will say to the next question — that question doesn't add information. Skip it or stop entirely.

**Test:** before asking the next question, write down your guess at the answer. If the guess matches, you don't need to ask. Move on.

## Three Conditions That Mean "Keep Going"

### Condition A: The answerer is dodging

Signs:
- "We'll figure that out later" (without a date)
- "It depends" (without naming the dependency)
- Answers a different question than was asked
- Hedges every answer with "probably" / "likely" / "maybe"

Action: re-ask the same question with the same words. If dodged twice, name the dodge: "You said 'we'll figure it out later' — what's the latest moment you can decide and still ship?"

### Condition B: Answers contradict each other

If Q3 answer contradicts Q1 answer, stop the forward progress and reconcile:

> "You said X in Q1 but now Y in Q3. Which is it?"

Reconciliation is a separate grill phase — don't continue forward until resolved.

### Condition C: A new branch surfaces

If the answerer says "but if we do X, then we also need to decide Y" — Y is a new branch. Add to the question queue. Don't stop until Y is resolved.

## The "Recommended Answer Match" Heuristic

When generating questions with `question_generator.py`, each question has a recommended answer. Track:

| Answer matches recommendation? | What it means |
|---|---|
| Yes, with same rationale | Strong signal — both interrogator + answerer converged on the same logic |
| Yes, different rationale | Worth probing — same conclusion via different reasoning could mean one is wrong |
| No, with strong rationale | Healthy disagreement — record the rationale; this is the value of the grill |
| No, weak rationale | Push back — "the recommendation was X because Y; your answer rejects Y — why?" |

When 80%+ of answers match the recommendations cleanly, the grill is over-engineered for this plan — stop.

## The "Diminishing Returns" Test

Each grill question costs ~1 turn. After 10-15 questions on a single plan, returns diminish:
- First 3-5: high value (catches major missing decisions)
- Questions 6-10: medium value (refines edge cases)
- Questions 11-15: lower value (catches rare edge cases)
- Questions 16+: noise (usually the interrogator over-conditioning)

If a plan has 20+ branches, consider splitting into multiple plans rather than one mega-grill.

## When to Stop Even Before Conditions Met

### When the user signals fatigue

> "Can we move on?" / "Let's just decide and revisit if needed" / "Skip ahead"

Stop. Note unresolved branches in the session for later. Don't push through fatigue — answers under fatigue are often wrong.

### When the cost of deciding exceeds the cost of being wrong

For reversible decisions, grilling is overhead. Ship and revisit. For irreversible decisions, grill thoroughly.

Test: "If we're wrong about this, what does it cost to fix?" If the answer is "trivial" or "we just change a flag", stop grilling early.

### When the plan is exploratory

If the plan is "let's try X for a week and see" — don't grill the details. Grill the decision criteria for after the week.

## The Locking-In Pattern

When the grill ends, the session should produce a "decisions locked" summary:

```
Session: my-plan
Started: 2026-05-13
Closed: 2026-05-13
Status: Complete (8/8 branches resolved)

Decisions locked:
  1. [L4] Schema-per-tenant chosen for cost reasons; isolation risk accepted.
  2. [L8] Okta for SSO. Auth0 rejected (less Workday integration).
  3. ...
```

The summary becomes the reference document. The grill session is throwaway; the summary is the artifact.

## Anti-Patterns

1. **Grilling forever** — every plan has 100 decideable details; grill stops at "shared understanding", not "complete certainty"
2. **Grilling reversible decisions** — wasteful; ship + revise
3. **Grilling without producing a summary** — wastes the answers; lock them in
4. **Grilling without exploring codebase first** — wastes turns asking questions the code answers
5. **Re-grilling the same plan** — if the plan was already grilled, don't re-grill the same branches; only grill new branches

## When This Reference Doesn't Help

- **Live-decision grilling in a meeting** — different mode; meetings have time pressure
- **Code review** — different scope; review is post-decision
- **Brainstorming** — wrong tool; grilling is for committed plans, not exploration

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — grill-me** (https://github.com/mattpocock/skills/, MIT) — the "shared understanding" stopping condition
- **Galef, J. — "The Scout Mindset"** (2021) — when to stop seeking more evidence
- **Kahneman, D. — "Thinking, Fast and Slow"** (2011) — decision fatigue + diminishing returns
- **Bezos, J. — Type 1 vs Type 2 decisions** (Amazon shareholder letter, 2015) — reversible vs irreversible decisions
- **YC Founder School — "Decide and move on"** — when grilling becomes procrastination
- **Larson, W. — "An Elegant Puzzle"** (2019) — engineering decision-making sequencing
- **Cynefin framework (Snowden)** — different decision domains require different evidence thresholds
