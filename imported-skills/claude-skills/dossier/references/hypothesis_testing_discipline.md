# Hypothesis-Testing Discipline — Why ≥30% Disconfirming

This reference answers exactly one decision: **why does the dossier skill demand a hypothesis upfront and allocate ≥30% of search budget to disconfirming evidence?**

## The Core Claim

A dossier that confirms what the user already thinks is **worthless for decision-making**. Decisions hinge on the evidence that might falsify your model — that's where new information lives. A confirmation-biased dossier feels reassuring but doesn't move the user closer to a good decision.

The ≥30% disconfirming rule is the operational implementation of Karl Popper's falsifiability principle adapted to research workflows.

## Why the User Must State a Hypothesis (Q4 Mandatory)

Without a stated hypothesis, the skill can't:

1. Classify searches as supporting or disconfirming
2. Allocate budget to disconfirming queries
3. Produce a verdict (SUPPORTED / PARTIALLY / DISPROVEN / INCONCLUSIVE)
4. Test anything — by definition, you can only test a specific claim

The skill **refuses** to proceed without Q4 because the alternative is producing a Wikipedia summary marketed as decision-grade research.

### What "I don't have a hypothesis" really means

Usually one of:
- "I haven't thought about it yet" → push back once: "Then guess. Commit to a position you can update."
- "I want to be neutral" → false neutrality. Everyone has a prior; surfacing it is healthier than pretending not to.
- "I'm just curious" → use a different tool (web search, ChatGPT). Dossier is for decisions.

### Implicit-hypothesis fallback

If user STILL refuses after the push-back, fall back to:

> Implicit hypothesis: "What's the most surprising thing I could find about this entity that would change someone's prior?"

**Flag the fallback in audit log.** Users should know they got a less-rigorous version of the workflow.

## The ≥30% Rule

For every Phase 4 search, classify it:

- **Supporting** — would confirm the hypothesis if results favorable
- **Disconfirming** — would refute the hypothesis if results favorable

Then verify (via `scripts/disconfirming_evidence_balance.py`):

```
disconfirming_ratio = disconfirming_queries / total_queries
require: disconfirming_ratio >= 0.30
```

### Why 30%, not 50%?

50% (balanced supporting + disconfirming) is the textbook ideal but impractical:

- Many hypotheses have asymmetric search space (more supporting angles obvious; disconfirming requires creativity)
- Hypothesis statements are usually slightly true — pure 50/50 over-rotates to false-balance

30% is the empirical floor: enough disconfirming to surface real surprises, not so much that the dossier feels like a hatchet job.

### Why not 0% (skip the rule)?

LLMs are particularly prone to confirmation bias because:
- Plausible-sounding supporting evidence is easier to generate
- Users tend to accept confirmation more readily (less friction)
- The "feels right" signal is the same for confirmation and truth

Without the explicit ≥30% rule, dossiers drift to ~10% disconfirming. The rule forces the discipline.

## Constructing Disconfirming Queries

For each supporting query, construct a disconfirming counterpart:

| Hypothesis | Supporting | Disconfirming |
|---|---|---|
| "Microsoft consolidating AI on Foundry" | "Microsoft Foundry adoption" | "Microsoft AI vendor diversification" |
| "CEO is over their head" | "CEO Smith strategy failures" | "CEO Smith wins / traction" |
| "Nonprofit overhead is sketchy" | "Nonprofit X high overhead complaints" | "Nonprofit X program spending" |
| "This person is technical enough" | "Skills gaps in [person]" | "Technical accomplishments of [person]" |

The disconfirming queries seek **evidence that would refute the hypothesis**. They are NOT softer versions of the supporting query.

### Common construction patterns

- **Antonym pivot:** "consolidating" → "diversifying"
- **Counter-example search:** "failures" → "wins"
- **Negation:** "true" → "false claims about"
- **Comparison:** "X is best" → "X vs alternatives weakness"
- **Time-shift:** "now" → "5 years ago context"
- **Counter-stakeholder:** "investors say" → "critics say"

## The Verdict Categories

After Phase 4 search completes, classify the evidence weight:

| Verdict | Criterion |
|---|---|
| **SUPPORTED** | ≥2x more supporting evidence than disconfirming, both well-tiered |
| **PARTIALLY SUPPORTED** | More supporting than disconfirming but real disconfirming evidence exists |
| **DISPROVEN** | More disconfirming than supporting |
| **INCONCLUSIVE** | Roughly balanced OR insufficient evidence overall |

**Critical:** the verdict is determined by the **weight of evidence**, not by the count of queries. If 5 supporting queries each found weak tertiary blog posts and 2 disconfirming queries found SEC filings, the disconfirming evidence wins on tier.

`citation_tracker.py` tracks both quantity and tier per classification.

## Anti-Patterns

### "I'll just ask balanced questions"

Generic balanced questions ("what does the public say about Microsoft?") don't test the hypothesis. They produce a balanced profile, not a decision-grade dossier. The discipline is targeted disconfirming queries against a specific claim.

### "I found 10 supporting, 0 disconfirming — must be true"

Almost never. Either:
- The disconfirming queries weren't constructed (bias)
- The disconfirming search space wasn't explored (laziness)
- The hypothesis was trivially true (in which case, why use the skill?)

When this happens, the script alerts and prompts more disconfirming queries.

### "Disconfirming evidence found, but it's tertiary"

Tier matters more than quantity. 1 primary disconfirming source (SEC filing, court record) > 5 tertiary disconfirming sources (Reddit threads). The verdict weights tier explicitly.

### "Confirmation-biased verdict"

The most common failure: the dossier finds disconfirming evidence in Phase 4 but the Executive Summary says SUPPORTED anyway. The skill is wired to fail this — the verdict comes from `citation_tracker`'s tier-weighted classification, not from narrative.

### "Hypothesis vague enough that anything supports it"

"This person is competent" is too vague — almost everything supports it. The push-back: "Competent at what specifically? At managing a team of 50? At raising Series B? At public speaking?" Specificity in the hypothesis enables sharp disconfirming queries.

## Operational Checklist

- [ ] Q4 hypothesis stated (or implicit-hypothesis fallback flagged)
- [ ] Each Phase 4 query classified at issue time (supporting / disconfirming)
- [ ] Pre-flight check: ≥30% queries planned to be disconfirming
- [ ] Mid-flight check: after every 3 queries, run `disconfirming_evidence_balance.py`
- [ ] Post-flight check: final ratio ≥30%; halt + alert if not
- [ ] Verdict reflects tier-weighted balance, not raw quantity
- [ ] Section 3 of DOCX explicitly lists BOTH supporting + disconfirming evidence
- [ ] Audit log records classification per query

## Citations (7 sources)

1. **Karl Popper, *The Logic of Scientific Discovery* (1934, English 1959).** Foundational source for falsifiability. "A theory which is not refutable by any conceivable event is non-scientific." The dossier skill's hypothesis-testing discipline is Popper applied to research workflows.

2. **Daniel Kahneman, *Thinking, Fast and Slow* (FSG, 2011), Chapters 12-22.** Source for confirmation bias mechanics. The ≥30% rule exists specifically because System 1 thinking under-weights disconfirming evidence by default.

3. **Philip Tetlock, *Superforecasting* (Crown, 2015).** Empirical evidence that "active open-mindedness" (Tetlock's term for hypothesis-testing) is the #1 predictor of forecasting accuracy. Source for the "weight of evidence, not count" verdict rule.

4. **Robyn Dawes, *Rational Choice in an Uncertain World* (2001 2nd ed.).** Source for the decision-grade framing. "A decision is grade-A when it uses the available evidence to maximally update from prior." Without disconfirming evidence, no update is possible.

5. **Nassim Nicholas Taleb, *The Black Swan* (Random House, 2007).** Source for the "black swan" rationale — disconfirming evidence is often where the high-information surprises live. Confirmation-biased search systematically misses tail risks.

6. **Karl Popper, *Conjectures and Refutations* (1963).** Companion to *Logic of Scientific Discovery*. Source for the conjecture-and-refutation cycle that the skill implements: state hypothesis → seek refutation → revise.

7. **Daniel Levitin, *A Field Guide to Lies* (Dutton, 2016).** Practical applications of statistical and inferential reasoning. Source for the source-tier framework — primary sources (SEC, court records) outweigh tertiary sources (blogs, forums) for verdict determination.
