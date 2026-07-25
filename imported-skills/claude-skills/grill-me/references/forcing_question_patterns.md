# Forcing-Question Patterns for Plan Interrogation

This reference answers exactly one decision: **what makes a question "forcing" vs "soft", and how do we ask forcing questions that resolve decisions?**

Pair with `scripts/question_generator.py` for templated forcing questions.

## What Makes a Question "Forcing"

A forcing question:

1. **Cannot be answered with "yes"/"no"** without follow-up
2. **Names the alternative** — "X or Y" not "is X right?"
3. **Demands evidence** — "what's the kill criterion?" not "what do you think?"
4. **Removes the escape hatch** — asks the trade-off explicitly

Soft questions let the answerer evade. Forcing questions don't.

## Six Forcing-Question Patterns

### Pattern 1: "Why X and not Y?"

When user says "We'll use Postgres" — forcing question: "Why Postgres and not MySQL?"

The forcing element: requires the answerer to articulate the alternative + the rejection reason. Reveals whether the choice was deliberate or default.

**Soft variant (bad):** "Are you sure about Postgres?"

### Pattern 2: "What's the kill criterion?"

When user says "We'll try approach X" — forcing question: "What would convince you X is wrong?"

The forcing element: requires the answerer to commit to falsifiability ahead of time. Prevents motivated reasoning later.

**Soft variant (bad):** "What if it doesn't work?"

### Pattern 3: "What's blocking the decision?"

When user says "TBD" or "open question" — forcing question: "What input is missing, and when does it arrive?"

The forcing element: separates "haven't decided" from "can't decide yet". Most TBDs are decideable now under uncertainty.

**Soft variant (bad):** "Have you thought about that?"

### Pattern 4: "Which side of the trade-off?"

When user says "trade-off between A and B" — forcing question: "Which side are you optimizing for, and what's the deciding constraint?"

The forcing element: requires picking. "Both" is not an option for actual trade-offs.

**Soft variant (bad):** "Have you considered the trade-offs?"

### Pattern 5: "What's the dependency?"

When user says "depends on X" — forcing question: "Is X locked in? If not, that decision comes first."

The forcing element: surfaces dependency chains. Forces depth-first walk of the decision tree.

**Soft variant (bad):** "Have you thought about dependencies?"

### Pattern 6: "Even at 60% confidence — what's your best guess?"

When user hedges — forcing question: "Even uncertain, what would you decide today?"

The forcing element: prevents indefinite deferral. Most decisions can be made under uncertainty + revised later.

**Soft variant (bad):** "When will you decide?"

## The "Recommended Answer" Rule (per Matt)

Every question should carry a recommended answer with rationale. Why:

1. **Models the depth of analysis expected** — answerer sees what "good" looks like
2. **Accelerates the interview** — answerer can agree/disagree faster than constructing from scratch
3. **Surfaces interrogator bias** — if the recommendation is wrong, answerer can correct it explicitly
4. **Prevents "what do you think?" loops** — both sides commit to a position

Format:

> Q: [forcing question]
> Recommended: [position] because [1-sentence reason].

## One-at-a-Time Discipline (per Matt)

> "Ask the questions one at a time."

Why this matters:

1. **Bundled questions get partial answers** — answerer addresses the easiest one; hard ones get skipped
2. **Each answer constrains the next** — the second question often changes after hearing the first answer
3. **Cognitive load** — answerer can focus + give a complete response
4. **Visible progress** — each Q→A pair locks one decision; bundle masks progress

**Anti-pattern:** "Here are 8 questions: [list]". This is a survey, not an interrogation.

## Codebase Exploration > Speculation (per Matt)

> "If a question can be answered by exploring the codebase, explore the codebase instead."

When to explore instead of asking:

| Question | Action |
|---|---|
| "What auth library are we using?" | `grep -r "auth" package.json` — don't ask |
| "Does X already exist?" | `find . -name "X*"` — don't ask |
| "What's the current schema?" | `Read path/to/migrations/latest.sql` — don't ask |
| "Are tests passing?" | Run the test suite — don't ask |

When to ask anyway:
- Intent: "Why this approach?" can't be grepped
- Trade-offs: only the human knows which they value
- Future state: codebase shows current, not desired

## Anti-Patterns

1. **"Are you sure?"** — invites defensive answer; no information value
2. **"Have you thought about ...?"** — implies "no" is acceptable; doesn't force a decision
3. **"What if it fails?"** — speculative; better: "what's the kill criterion?"
4. **"Could you elaborate?"** — passive; better: name the specific gap
5. **Yes/no questions** without follow-up — wastes the turn
6. **Stacking questions** — bundles violate one-at-a-time rule

## How `question_generator.py` Implements This

The tool's question templates map each detected branch kind to a forcing-question pattern:

- `intent` → "Why this approach and not the obvious alternative?" (Pattern 1)
- `choice` → "Which side of the choice, and what's the deciding criterion?" (Pattern 4)
- `open` → "What's blocking this decision?" (Pattern 3)
- `tradeoff` → "Which side of the trade-off are you optimizing for?" (Pattern 4)
- `dependency` → "Is the dependency locked in?" (Pattern 5)
- `question` → "What's your current best answer, even if uncertain?" (Pattern 6)

Each generated question carries a recommended-answer template per Matt's rule.

## When This Reference Doesn't Help

- **Open-ended exploration** — early-stage ideation needs soft questions; grill-me is for plans not yet committed
- **Therapeutic/coaching contexts** — forcing questions can feel adversarial; tone matters
- **Hiring interviews** — different mode; behavioral questions follow different patterns

---

**Source authorities (non-exhaustive):**

- **Matt Pocock — grill-me** (https://github.com/mattpocock/skills/, MIT) — the one-at-a-time + recommended-answer rules
- **Socratic Method** (5th-century BC) — Plato's dialogues — sequential questioning toward truth
- **Y Combinator office-hour format** (Garry Tan + Michael Seibel) — founder interrogation pattern
- **Toyota Production System — 5 Whys** (Sakichi Toyoda) — sequential causal questioning
- **Cockburn, A. — "Writing Effective Use Cases"** (2000) — decision-branch enumeration
- **Popper, K. — "Conjectures and Refutations"** (1963) — falsifiability + kill criteria
- **Galef, J. — "The Scout Mindset"** (2021) — calibrating beliefs under uncertainty
- **Larson, W. — "An Elegant Puzzle"** (2019) — eng decision-making in practice
