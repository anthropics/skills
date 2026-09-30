---
name: google-ads-management
description: >-
  Comprehensive Google Ads campaign management skill. Covers account audits,
  keyword research and match type strategy, RSA ad copy generation, Smart
  Bidding configuration (tCPA/tROAS), Performance Max optimization, Shopping
  campaign setup, audience targeting, conversion tracking, Quality Score
  improvement, budget allocation, remarketing, and competitor analysis.
  Use when the user asks about Google Ads, PPC, campaign management,
  ad optimization, or paid search strategy.
---

# Google Ads Management

## Overview

This skill teaches Claude how to manage Google Ads accounts at an expert level. It covers the complete lifecycle: account audits, campaign creation, keyword strategy, ad copy, bidding, and ongoing optimization. The patterns come from managing hundreds of accounts across every industry vertical.

## When to Use

Use this skill whenever the user mentions:
- Google Ads, AdWords, PPC, or paid search
- Campaign performance, CPA, ROAS, CTR, Quality Score
- Keywords, match types, negative keywords, search terms
- Ad copy, RSA, headlines, descriptions
- Bidding strategies (Smart Bidding, tCPA, tROAS, Maximize Conversions)
- Performance Max, PMax, Shopping campaigns
- Budget allocation, pacing, or forecasting
- Audience targeting, remarketing, Customer Match
- Conversion tracking, attribution, Enhanced Conversions
- Account structure, campaign organization

## Account Audit Framework

When asked to audit a Google Ads account, follow this sequence:

1. **Account Summary** — Pull overall spend, conversions, CPA, ROAS for last 30 days
2. **Campaign Performance** — Rank campaigns by spend, identify top/bottom performers
3. **Keyword Analysis** — Check Quality Score distribution, identify low-QS high-spend keywords
4. **Search Term Review** — Find wasted spend on irrelevant queries
5. **Ad Copy Assessment** — Check RSA asset ratings, identify "Low" performers
6. **Bidding Strategy Evaluation** — Verify Smart Bidding has enough data (30+ conversions/month)
7. **Extension Coverage** — Ensure all campaigns have sitelinks, callouts, structured snippets
8. **Conversion Tracking** — Verify tracking fires correctly, check Enhanced Conversions status

Present findings in a structured report with severity ratings (Critical / High / Medium / Low) and a prioritized action plan.

## Keyword Strategy

### Match Type Decision Framework

```
High conversion rate (>5%) + low volume (<1000/mo) → Exact Match
Transactional intent + 3+ words → Phrase Match
High volume (>5000/mo) + Smart Bidding active → Broad Match
Informational intent (how, what, why) → Negative keyword candidate
```

### Negative Keyword Management

Maintain three levels:
- **Account-level**: Universal negatives (free, jobs, salary, DIY, porn)
- **Campaign-level**: Theme separation (brand terms negative in non-brand campaigns)
- **Ad group-level**: Fine-tuning within themes (embedded negatives for query funneling)

Review Search Terms Report weekly. Add negatives for any term with spend > 2x target CPA and zero conversions.

## RSA Ad Copy

### Headlines Strategy (15 max, 30 chars each)

Provide a mix:
- 3-4 keyword-focused (match search intent)
- 3-4 benefit-driven (why choose you)
- 2-3 CTA headlines (Get Quote, Shop Now, Start Free Trial)
- 2-3 social proof (Rated 4.9 Stars, 10K+ Customers)
- 1-2 offers (Free Shipping, 20% Off Today)
- 1-2 brand name headlines

### Descriptions Strategy (4 max, 90 chars each)

- Description 1: Lead value proposition
- Description 2: Supporting benefit + CTA
- Description 3: Trust/credibility (years in business, certifications)
- Description 4: Offer details or urgency

Pin only to Position 1 when brand guidelines require it. Leave most unpinned for optimization.

## Smart Bidding

### Progression Path

```
Week 1-2:  Maximize Clicks (with CPC cap) → gather click data
Week 3-4:  Maximize Conversions (no target) → build conversion history
Week 5+:   Target CPA or Target ROAS → optimize efficiency
```

### Key Rules

- Never start a new campaign with Target CPA — insufficient data
- Need 30+ conversions in 30 days for tCPA, 50+ for tROAS
- Set tCPA at actual CPA first, then lower by 10-15% every 2 weeks
- Don't make changes during learning period (1-2 weeks after any significant change)
- Budget-constrained campaigns: check Search Impression Share lost to budget

## Quality Score

Three components, each rated Below Average / Average / Above Average:

| Component | How to Improve |
|-----------|----------------|
| Expected CTR | Better ad copy, stronger CTAs, all extensions enabled |
| Ad Relevance | Include target keyword in headlines, tighten ad group themes |
| Landing Page Experience | Speed (<3s load), mobile-friendly, relevant content, HTTPS |

Priority: Fix Landing Page Experience first (helps all keywords on that page), then Ad Relevance (quick ad copy fix), then Expected CTR (ongoing testing).

## Performance Max

- 1-3 PMax campaigns per account (don't fragment data)
- Each asset group needs: 20 images, 5 videos, 5 headlines, 5 long headlines, 5 descriptions
- Use brand exclusions to prevent PMax from cannibalizing brand Search campaigns
- Set only primary conversion goals (purchases, qualified leads) — remove micro-conversions
- Provide strong audience signals: Customer Match lists, custom segments with competitor URLs

## Budget Allocation

The 70/20/10 framework:
- **70%** to proven performers (positive ROAS campaigns)
- **20%** to growth/testing (new campaigns, audiences, creatives)
- **10%** to brand protection and competitive defense

Never let high-ROI campaigns be budget-limited. Scale by max 20% every 2 weeks.

## Examples

**User:** "Audit my Google Ads account"
**Claude:** Pulls account summary, campaigns, wasted spend, quality scores, recommendations. Presents structured findings with severity ratings and action plan.

**User:** "My CPA is too high, how do I lower it?"
**Claude:** Asks clarifying questions (which campaigns, current vs target CPA), then recommends specific actions: negative keyword additions, QS improvements, bid strategy adjustments, landing page fixes.

**User:** "Set up a new Search campaign for lead gen"
**Claude:** Proposes campaign structure (name, settings, ad groups, keywords, ad copy, extensions, bid strategy, conversion goals), presents for user approval before creating.

## Platform Compatibility

| Platform    | Supported |
|-------------|-----------|
| Claude Code | ✅        |
| Claude.ai   | ✅        |
| Cursor      | ✅        |
| Codex       | ✅        |
| Gemini CLI  | ✅        |

## Additional Resources

For the complete skill library with 73 skills across 10 categories, see [Agent Skills by googleadsagent.ai](https://github.com/itallstartedwithaidea/agent-skills).

---

Created by [John Williams](https://itallstartedwithaidea.com) — 15+ years in paid media | [googleadsagent.ai](https://googleadsagent.ai)
