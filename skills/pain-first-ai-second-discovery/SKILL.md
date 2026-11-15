---
name: pain-first-ai-second-discovery
description: Stop a team building the wrong AI product by proving the pain before discussing any model. Use when an AI feature is proposed, a discovery interview is planned, or a roadmap is full of AI features with no named pain. Asks three questions about current behaviour, cost of failure, and prior attempts, then gives a go or no-go on the model conversation.
license: Complete terms in LICENSE.txt
---

# pain-first-ai-second-discovery

## What this skill does

Most discovery interviews for AI products ask some version of "what AI feature do you want?" That question gets a wish list, not the truth. This skill reverses the order: prove there is a pain worth solving, price it, and learn what has already failed, and only then discuss the model.

It is a gate, not a brainstorm. If the pain cannot be named in the user's words, the AI conversation does not start.

## When to use this skill

- An AI feature, agent, or copilot is proposed and no one can state the pain it removes in the user's words.
- A discovery interview is being planned for an AI product.
- A roadmap has many AI features and none names the pain it removes.
- A team is debating models, prompts, or vendors before agreeing on the problem.

## When not to use this skill

- The pain is already proven and priced, and the work is now model selection, evaluation, or launch.
- The product is not AI. The three questions still work, but the model gate adds nothing.

## The rule

Pain first. AI second. Then the model.

No model, vendor, prompt, or demo may be discussed until Steps 1-3 are documented. If a participant jumps to a solution, note it and return to the question.

## How to use this skill

### Step 1 - Name the pain in the user's words

Ask: **What do you do today when this problem shows up?**

Record the answer as a concrete workflow, not a category. "I re-check every invoice by hand against the contract" is a pain. "Inefficiency" is not.

- Ask for the last time it happened, not the typical time.
- Ask who does it, how often, and what they stop doing to handle it.
- If the answer is a feature request ("I want an AI summary"), ask what they do today instead, and repeat until a workflow appears.

Output: one paragraph, in the user's words, describing the current behaviour.

### Step 2 - Price the pain

Ask: **What does it cost you when it goes wrong?**

Cost is time, money, trust, or risk, whichever the user names first. Do not supply a number for them.

- Time: how long does the workaround take, and how often?
- Money: what is lost, reworked, refunded, or delayed?
- Trust: who loses confidence, and what do they do instead?
- Risk: what happens if the wrong answer is acted on?

Output: the cost in the user's own terms, with a frequency. A pain with no cost and no frequency is a preference, not a problem worth building for.

### Step 3 - Learn what already failed

Ask: **What have you already tried, and why did it not stick?**

This is the question teams skip most often, and the one that saves the most wasted building.

- List every prior attempt: spreadsheet, checklist, rule, tool, vendor, or earlier AI feature.
- For each, record why it did not stick: too slow, too wrong, too hard to trust, too hard to maintain, or never adopted.
- The new product has to beat the best prior attempt, not an imaginary blank slate. Name that bar explicitly.

Output: a short list of prior attempts with the reason each failed, and the bar the new solution must clear.

### Step 4 - Decide: go or no-go

Only now may the model conversation start, and only if all three hold:

1. The pain is named in the user's words (Step 1).
2. The cost is real and frequent enough to matter (Step 2).
3. The bar set by prior attempts is clear (Step 3).

If any one is missing, the decision is **no-go**: do more discovery, or drop the idea. Record which step failed and what evidence would change the decision. Do not proceed to model selection to "see what the AI can do", that is the wish-list trap again.

If all three hold, write the one-sentence brief: "For [user], when [situation], the pain is [workflow], costing [cost] [frequency]. The new solution must beat [prior attempt], which failed because [reason]."

## Output template

```markdown
## Pain-First Discovery - [product / idea]

**Pain (user's words):** ...
**Current workflow:** ...
**Cost when it goes wrong:** ... (frequency: ...)
**Already tried:** ...
  - ... - failed because ...
**Bar to beat:** ...
**Decision:** GO / NO-GO
**If NO-GO, missing evidence:** ...
**One-sentence brief:** ...
```

## Examples

- A team proposes an AI invoice summariser. Step 1 finds the real workflow is re-checking every invoice by hand against the contract, twice a week, because a wrong payment erodes trust with a supplier. That is a go-worthy pain; "I want an AI summary" on its own is not.
- A team proposes an AI triage copilot for support tickets. Step 3 finds a rule-based router was tried and abandoned because it was too wrong on edge cases. The new solution must beat that router on those edge cases, or it is a no-go until that bar is defined.

## What good looks like

- The pain is quoted in the user's words, not paraphrased into a category.
- The cost has a number or a named consequence and a frequency.
- At least one prior attempt is named, with a reason it did not stick.
- The go / no-go decision names the step that failed, if it failed.
- No model, vendor, or prompt appears before Step 4.

## Common mistakes

- **Asking what AI feature they want.** That is the trap this skill exists to avoid.
- **Accepting a category as a pain.** "Inefficiency", "poor visibility", and "manual work" are not pains until a workflow and a cost are attached.
- **Skipping Step 3.** A team that does not know what already failed will rebuild it with a model attached.
- **Letting a good demo override a missing pain.** A demo that gets applause and changes no workflow is a costume, not a product.

## Keywords

AI discovery, discovery interview, pain-first, product discovery, go no-go, AI feature validation, user pain, JTBD

## Source

Adapted from the Pain-First AI-Second Discovery framework in *AI Product Management Frameworks in Practice* (Nilesh Dhage, Packt Publishing, 2026), and from the author's discovery-interview practice. The three questions and the pain to cost to history to model order are the framework's core; the wording here is original to this skill file.
