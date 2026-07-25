---
name: "competitive-intel"
description: "Systematic competitor tracking that feeds CMO positioning, CRO battlecards, and CPO roadmap decisions. Use when analyzing competitors, building sales battlecards, tracking market moves, positioning against alternatives, or when user mentions competitive intelligence, competitive analysis, competitor research, battlecards, win/loss, or market positioning."
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: c-level
  domain: competitive-strategy
  updated: 2026-03-05
  frameworks: ci-playbook, battlecard-template
---

# Competitive Intelligence

Systematic competitor tracking. Not obsession — intelligence that drives real decisions.

## Keywords
competitive intelligence, competitor analysis, battlecard, win/loss analysis, competitive positioning, competitive tracking, market intelligence, competitor research, SWOT, competitive map, feature gap analysis, competitive strategy

## Quick Start

Ask in natural language for the deliverable you need:

> "Map our competitive landscape" — direct, indirect, and future competitors
> "Build a battlecard for [competitor]" — sales-ready battlecard
> "Run a win/loss analysis" — recent wins and losses by reason
> "What did [competitor] do recently?" — competitor update tracking
> "Build a competitive positioning map" — 2x2 positioning map

## Framework: 5-Layer Intelligence System

### Layer 1: Competitor Identification

**Direct competitors:** Same ICP, same problem, comparable solution, similar price point.
**Indirect competitors:** Same budget, different solution (including "do nothing" and "build in-house").
**Future competitors:** Well-funded startups in adjacent space; large incumbents with stated roadmap overlap.

**The 2x2 Threat Matrix:**

| | Same ICP | Different ICP |
|---|---|---|
| **Same problem** | Direct threat | Adjacent (watch) |
| **Different problem** | Displacement risk | Ignore for now |

Update this quarterly. Who's moved quadrants?

### Layer 2: Tracking Dimensions

Track these 8 dimensions per competitor:

| Dimension | Sources | Cadence |
|-----------|---------|---------|
| **Product moves** | Changelog, G2/Capterra reviews, Twitter/LinkedIn | Monthly |
| **Pricing changes** | Pricing page, sales call intel, customer feedback | Triggered |
| **Funding** | Crunchbase, TechCrunch, LinkedIn | Triggered |
| **Hiring signals** | LinkedIn job postings, Indeed | Monthly |
| **Partnerships** | Press releases, co-marketing | Triggered |
| **Customer wins** | Case studies, review sites, LinkedIn | Monthly |
| **Customer losses** | Win/loss interviews, churned accounts | Ongoing |
| **Messaging shifts** | Homepage, ads (Facebook/Google Ad Library) | Quarterly |

### Layer 3: Analysis Frameworks

**SWOT per Competitor:**
- Strengths: What do they do well? Where do they win?
- Weaknesses: Where do they lose? What do customers complain about?
- Opportunities: What could they do that would threaten you?
- Threats: What's their existential risk?

**Competitive Positioning Map (2 axis):**
Choose axes that matter for your buyers:
- Common: Price vs Feature Depth; Enterprise-ready vs SMB-ready; Easy to implement vs Configurable
- Pick axes that show YOUR differentiation clearly

**Feature Gap Analysis:**
| Feature | You | Competitor A | Competitor B | Gap status |
|---------|-----|-------------|-------------|------------|
| [Feature] | ✅ | ✅ | ❌ | Your advantage |
| [Feature] | ❌ | ✅ | ✅ | Gap — roadmap? |
| [Feature] | ✅ | ❌ | ❌ | Moat |
| [Feature] | ❌ | ❌ | ✅ | Competitor B only |

### Layer 4: Output Formats

**For Sales (CRO):** Battlecards — one page per competitor, designed for pre-call prep.
See `templates/battlecard-template.md`

**For Marketing (CMO):** Positioning update — message shifts, new differentiators, claims to stop or start making.

**For Product (CPO):** Feature gap summary — what customers ask for that we don't have, what competitors ship, what to reprioritize.

**For CEO/Board:** Monthly competitive summary — 1-page: who moved, what it means, recommended responses.

### Layer 5: Intelligence Cadence

**Monthly (scheduled):**
- Review all tier-1 competitors (direct threats, top 3)
- Update battlecards with new intel
- Publish 1-page summary to leadership

**Triggered (event-based):**
- Competitor raises funding → assess implications within 48 hours
- Competitor launches major feature → product + sales response within 1 week
- Competitor poaches key customer → win/loss interview within 2 weeks
- Competitor changes pricing → analyze and respond within 1 week

**Quarterly:**
- Full competitive landscape review
- Update positioning map
- Refresh ICP competitive threat assessment
- Add/remove companies from tracking list

---

## Win/Loss Analysis

This is the highest-signal competitive data you have. Most companies do it too rarely.

**When to interview:**
- Every lost deal >$50K ACV
- Every churn >6 months tenure
- Every competitive win (learn why — it may not be what you think)

**Who conducts it:**
- NOT the AE who worked the deal (too close, prospect won't be candid)
- Customer success, product team, or external researcher

**Question structure:**
1. "Walk me through your evaluation process"
2. "Who else were you considering?"
3. "What were the top 3 criteria in your decision?"
4. "Where did [our product] fall short?"
5. "What was the deciding factor?"
6. "What would have changed your decision?"

**Aggregate findings monthly:**
- Win reasons (rank by frequency)
- Loss reasons (rank by frequency)
- Competitor win rates (by competitor, by segment)
- Patterns over time

---

## The Balance: Intelligence Without Obsession

**Signs you're over-tracking competitors:**
- Roadmap decisions are primarily driven by "they just shipped X"
- Team morale drops when competitors fundraise
- You're shipping features you don't believe in to match their checklist
- Pricing discussions always start with "well, they charge X"

**Signs you're under-tracking:**
- Your AEs get blindsided on calls
- Prospects know more about competitors than your team does
- You missed a major product launch until customers told you
- Your positioning hasn't changed in 12+ months despite market moves

**The right posture:**
- Know competitors well enough to win against them
- Don't let them set your agenda
- Your roadmap is led by customer problems, informed by competitive gaps

---

## Distributing Intelligence

| Audience | Format | Cadence | Owner |
|----------|--------|---------|-------|
| AEs + SDRs | Updated battlecards in CRM | Monthly + triggered | CRO |
| Product | Feature gap analysis | Quarterly | CPO |
| Marketing | Positioning brief | Quarterly | CMO |
| Leadership | 1-page competitive summary | Monthly | CEO/COO |
| Board | Competitive landscape slide | Quarterly | CEO |

**One source of truth:** All competitive intel lives in one place (Notion, Confluence, Salesforce). Avoid Slack-only distribution — it disappears.

---

## Red Flags in Competitive Intelligence

| Signal | What it means |
|--------|---------------|
| Competitor's win rate >50% in your core segment | Fundamental positioning problem, not sales problem |
| Same objection from 5+ deals: "competitor has X" | Feature gap that's real, not just optics |
| Competitor hired 10 engineers in your domain | Major product investment incoming |
| Competitor raised >$20M and targets your ICP | 12-month runway for them to compete hard |
| Prospects evaluate you to justify competitor decision | You're the "check box" — fix perception or segment |

## Integration with C-Suite Roles

| Intelligence Type | Feeds To | Output Format |
|------------------|----------|---------------|
| Product moves | CPO | Roadmap input, feature gap analysis |
| Pricing changes | CRO, CFO | Pricing response recommendations |
| Funding rounds | CEO, CFO | Strategic positioning update |
| Hiring signals | CHRO, CTO | Talent market intelligence |
| Customer wins/losses | CRO, CMO | Battlecard updates, positioning shifts |
| Marketing campaigns | CMO | Counter-positioning, channel intelligence |

## References
- `references/ci-playbook.md` — OSINT sources, win/loss framework, positioning map construction
- `templates/battlecard-template.md` — sales battlecard template
