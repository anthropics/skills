---
name: "cmo-review"
description: "/cs:cmo-review <plan> — Narrative-first interrogation of positioning, ICP, message house, and channel mix. Use when launching a campaign or repositioning, or when CAC is rising and the one-sentence positioning test fails."
---

# /cs:cmo-review — CMO Forcing Questions

**Command:** `/cs:cmo-review <plan>`

The narrative-first strategist pressure-tests positioning before debating tactics.

## When to Run

- Before launching any new campaign
- Before changing positioning, tagline, or category
- Before allocating > 10% of marketing budget to a new channel
- Before a major PR moment (funding announcement, product launch)
- When pipeline contribution is declining

## The Six CMO Questions

### 1. ICP (One Real Person)
**Name one real person in your ICP. Company, title, what they do daily, what they hate.**
- Persona ≠ ICP. ICP is real.
- If you can't name one, the ICP isn't sharp enough.

### 2. JTBD
**What job is the customer hiring this product to do, and what's the alternative they use today?**
- One sentence the customer would say out loud.
- "We use spreadsheets" is a valid alternative. So is "we don't."

### 3. Positioning Statement
**One sentence: For [ICP], who needs [job], we are [category] that [differentiator] unlike [alternative].**
- This is the headline. Everything cascades.
- If it doesn't fit in one sentence, it's not positioning yet.

### 4. Distribution Channel
**Where does the customer first hear your name — and is it inbound or outbound at this stage?**
- Name the channel, intent, and the path to first contact.
- PLG, sales-led, content-led, partnership-led — pick a primary.

### 5. CAC Payback
**Per channel: what's CAC, what's payback in months, and is it improving?**
- If a channel's payback is > 18 months, it isn't a channel — it's a hobby.

### 6. Defensibility of Brand
**If a well-funded competitor copies your messaging tomorrow, what's still yours?**
- Category position, founder-market fit, customer love, distribution lock — name one.

## Workflow

1. **Run the models:**
   ```bash
   python ../../../skills/cmo-advisor/scripts/marketing_budget_modeler.py
   python ../../../skills/cmo-advisor/scripts/growth_model_simulator.py
   ```
2. **Answer the six questions** in writing.
3. **Apply the verdict:**
   - 🟢 GREEN — story is sharp, channel mix sound
   - 🟡 YELLOW — sharpen positioning before scaling
   - 🔴 RED — positioning broken; do not spend

## Output Format

```markdown
# CMO Review: <plan>
**Date:** YYYY-MM-DD

## Positioning
One-sentence statement: <here>

## ICP
- Named persona: <name, title, company>
- JTBD: <one sentence in their words>

## Channel Mix
- Primary: <channel> | CAC $X | Payback Ym
- Secondary: <channel> | CAC $X | Payback Ym

## Verdict
🟢 / 🟡 / 🔴

## Next Steps
[3 concrete actions]
```

## Routing

- `/cs:cro-review` — pipeline contribution check
- `/cs:cpo-review` — product ↔ positioning alignment
- `/cs:decide` — log the verdict

## Related

- Agent: [`cs-cmo-advisor`](../../agents/cs-cmo-advisor.md)
- Skill: [`cmo-advisor`](../../../skills/cmo-advisor/SKILL.md)
- Execution domain: `../../../../marketing-skill/`

---

**Version:** 1.0.0
