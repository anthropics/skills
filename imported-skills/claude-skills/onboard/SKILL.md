---
name: "onboard"
description: "/cs:onboard — Founder interview that populates ~/.claude/company-context.md using the canonical 7-dimension cs-onboard schema. The first command to run when starting with c-level-agents. Use when setting up the virtual C-suite for a new company, or when advisors lack company context — e.g. before a first /cs:boardroom or after a fundraise changes the numbers."
---

# /cs:onboard — Founder Interview

**Command:** `/cs:onboard`

The first command to run when adopting c-level-agents. A structured founder interview that produces `~/.claude/company-context.md` — the file every cs-* advisor reads before responding. Without this, the advisors are guessing.

## What This Produces

`~/.claude/company-context.md` — a single file with the durable facts about the company. Read by:
- `cs-chief-of-staff` (routing decisions)
- Every cs-* advisor (context for any question)
- `/cs:brief` (assumptions in any new decision)

## The Interview (12 Questions)

### Company Basics
1. **Company name and one-sentence pitch.**
2. **Stage:** pre-seed / seed / Series A / Series B / Series C+ / public
3. **Headcount:** total, by function (eng / product / GTM / ops / G&A)
4. **Geographic distribution:** HQ + remote split, key countries

### Business Model
5. **Revenue model:** SaaS subscription / usage / transaction / marketplace / hardware / services
6. **ICP:** name one real customer and describe what they have in common with others
7. **ACV:** median and range; deal count last 12 months
8. **Growth rate:** ARR YoY; if pre-revenue, leading metric (users, MAU, etc.)

### Financial Posture
9. **Runway:** months of cash at current burn; bear-case months
10. **Last raise:** amount, valuation, lead investor, date

### Strategic Context
11. **Top 3 priorities for the current quarter** (in plain language)
12. **Top 3 risks the founder loses sleep over** (be specific)

## Output Format

**Canonical schema:** `~/.claude/company-context.md` is owned by the [`cs-onboard`](../../../skills/cs-onboard/SKILL.md) skill and follows its 7-dimension schema (`../../../skills/cs-onboard/templates/company-context-template.md`): Company Identity, Stage & Scale, Founder Profile, Team & Culture, Market & Competition, Current Challenges, Goals & Ambition. The 12 questions above are a faster structured intake that populates that same file — Identity/Business/Financial → Stage & Scale, Team → Team & Culture, Quarter priorities/risks → Current Challenges + Goals & Ambition. Write `[not captured]` for dimensions the quick intake doesn't reach (Founder Profile, Market & Competition); run the full `cs-onboard` interview to fill them. Never create a second context file or a divergent layout.

The intake summary captured by the 12 questions:

```markdown
# Company Context
**Generated:** YYYY-MM-DD
**Last updated:** YYYY-MM-DD

## Identity
- **Company:** <name>
- **Pitch:** <one sentence>
- **Stage:** <stage>
- **HQ + remote:** <distribution>

## Business
- **Model:** <type>
- **ICP:** <description + named customer>
- **ACV:** $<median> (range $<low> - $<high>)
- **Deal count (LTM):** N
- **ARR growth (YoY):** X%

## Financial
- **Cash on hand:** $<amount>
- **Net burn (monthly):** $<amount>
- **Runway base:** N months
- **Runway bear:** N months
- **Last raise:** $<amount> at $<post> in <month YYYY>, led by <investor>

## Team
- **Total headcount:** N
- **Eng:** N | Product: N | GTM: N | Ops: N | G&A: N

## Quarter
- **Top priorities (Q<X> YYYY):**
  1. <priority>
  2. <priority>
  3. <priority>

- **Top risks:**
  1. <risk>
  2. <risk>
  3. <risk>

## Routing Hints
[Optional: any role the founder wants to use sparingly or rely on heavily]
```

## Workflow

1. Walk the founder through all 12 questions
2. Quote founder's own words wherever possible (don't paraphrase the ICP)
3. Save to `~/.claude/company-context.md`
4. (Optional) If llm-wiki bridge is configured: symlink to vault
   ```bash
   ln -sf ~/company-vault/00-meta/company-context.md ~/.claude/company-context.md
   ```
5. Confirm with founder: read the file back, ask "anything missing?"

## When to Re-Run

- After a fundraise (numbers change)
- After a major pivot or product launch
- After 6+ months (most facts have drifted)
- After a major hire (team distribution changes)
- Always before a `/cs:boardroom` for a high-stakes decision

## Persistence

By default, `~/.claude/company-context.md` is local to the founder's machine. To make it persistent across machines / shareable:

- **Markdown vault (recommended):** see [`../../references/llm-wiki-bridge.md`](../../references/llm-wiki-bridge.md)
- **Encrypted dotfile sync:** age + git
- **Shared team:** keep in a private repo, symlink from `~/.claude/`

## Related

- Skill: [`cs-onboard`](../../../skills/cs-onboard/SKILL.md) — the underlying interview protocol
- Skill: [`context-engine`](../../../skills/context-engine/SKILL.md) — reads this file
- Reference: [`../../references/llm-wiki-bridge.md`](../../references/llm-wiki-bridge.md)

---

**Version:** 1.0.0
