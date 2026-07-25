---
name: "competitive-teardown"
description: "Analyzes competitor products and companies by synthesizing data from pricing pages, app store reviews, job postings, SEO signals, and social media into structured competitive intelligence. Produces feature comparison matrices scored across 12 dimensions, SWOT analyses, positioning maps, UX audits, pricing model breakdowns, action item roadmaps, and stakeholder presentation templates. Use when conducting competitor analysis, comparing products against competitors, researching the competitive landscape, building battle cards for sales, preparing for a product strategy or roadmap session, responding to a competitor's new feature or pricing change, or performing a quarterly competitive review."
---

# Competitive Teardown

**Tier:** POWERFUL  
**Category:** Product Team  
**Domain:** Competitive Intelligence, Product Strategy, Market Analysis

---

## When to Use

- Before a product strategy or roadmap session
- When a competitor launches a major feature or pricing change
- Quarterly competitive review
- Before a sales pitch where you need battle card data
- When entering a new market segment

---

## Teardown Workflow

Follow these steps in sequence to produce a complete teardown:

1. **Define competitors** — List 2–4 competitors to analyze. Confirm which is the primary focus.
2. **Collect data** — Use `references/data-collection-guide.md` to gather raw signals from at least 3 sources per competitor (website, reviews, job postings, SEO, social).  
   _Validation checkpoint: Before proceeding, confirm you have pricing data, at least 20 reviews, and job posting counts for each competitor._
3. **Score using rubric** — Apply the 12-dimension rubric below to produce a numeric scorecard for each competitor and your own product.  
   _Validation checkpoint: Every dimension should have a score and at least one supporting evidence note._
4. **Generate outputs** — Populate the templates in `references/analysis-templates.md` (Feature Matrix, Pricing Analysis, SWOT, Positioning Map, UX Audit).
5. **Build action plan** — Translate findings into the Action Items template (quick wins / medium-term / strategic).
6. **Package for stakeholders** — Assemble the Stakeholder Presentation using outputs from steps 3–5.

---

## Data Collection Guide

> Full executable scripts for each source are in `references/data-collection-guide.md`. Summaries of what to capture are below.

### 1. Website Analysis

Key things to capture:
- Pricing tiers and price points
- Feature lists per tier
- Primary CTA and messaging
- Case studies / customer logos (signals ICP)
- Integration logos
- Trust signals (certifications, compliance badges)

### 2. App Store Reviews

Review sentiment categories:
- **Praise** → what users love (defend / strengthen these)
- **Feature requests** → unmet needs (opportunity gaps)
- **Bugs** → quality signals
- **UX complaints** → friction points you can beat them on

**Sample App Store query (iTunes Search API):**
```
GET https://itunes.apple.com/search?term=<competitor_name>&entity=software&limit=1
# Extract trackId, then:
GET https://itunes.apple.com/rss/customerreviews/id=<trackId>/sortBy=mostRecent/json?l=en&limit=50
```
Parse `entry[].content.label` for review text and `entry[].im:rating.label` for star rating.

### 3. Job Postings (Team Size & Tech Stack Signals)

Signals from job postings:
- **Engineering volume** → scaling vs. consolidating
- **Specific tech mentions** → stack (React/Vue, Postgres/Mongo, AWS/GCP)
- **Sales/CS ratio** → product-led vs. sales-led motion
- **Data/ML roles** → upcoming AI features
- **Compliance roles** → regulatory expansion

### 4. SEO Analysis

SEO signals to capture:
- Top 20 organic keywords (intent: informational / navigational / commercial)
- Domain Authority / backlink count
- Blog publishing cadence and topics
- Which pages rank (product pages vs. blog vs. docs)

### 5. Social Media Sentiment

Capture recent mentions via Twitter/X API v2, Reddit, or LinkedIn. Look for recurring praise, complaints, and feature requests. See `references/data-collection-guide.md` for API query examples.

---

## Scoring Rubric (12 Dimensions, 1-5)

| # | Dimension | 1 (Weak) | 3 (Average) | 5 (Best-in-class) |
|---|-----------|----------|-------------|-------------------|
| 1 | **Features** | Core only, many gaps | Solid coverage | Comprehensive + unique |
| 2 | **Pricing** | Confusing / overpriced | Market-rate, clear | Transparent, flexible, fair |
| 3 | **UX** | Confusing, high friction | Functional | Delightful, minimal friction |
| 4 | **Performance** | Slow, unreliable | Acceptable | Fast, high uptime |
| 5 | **Docs** | Sparse, outdated | Decent coverage | Comprehensive, searchable |
| 6 | **Support** | Email only, slow | Chat + email | 24/7, great response |
| 7 | **Integrations** | 0-5 integrations | 6-25 | 26+ or deep ecosystem |
| 8 | **Security** | No mentions | SOC2 claimed | SOC2 Type II, ISO 27001 |
| 9 | **Scalability** | No enterprise tier | Mid-market ready | Enterprise-grade |
| 10 | **Brand** | Generic, unmemorable | Decent positioning | Strong, differentiated |
| 11 | **Community** | None | Forum / Slack | Active, vibrant community |
| 12 | **Innovation** | No recent releases | Quarterly | Frequent, meaningful |

**Example completed row** (Competitor: Acme Corp, Dimension 3 – UX):

| Dimension | Acme Corp Score | Evidence |
|-----------|----------------|---------|
| UX | 2 | App Store reviews cite "confusing navigation" (38 mentions); onboarding requires 7 steps before TTFV; no onboarding wizard; CC required at signup. |

Apply this pattern to all 12 dimensions for each competitor.

---

## Templates

> Full template markdown is in `references/analysis-templates.md`. Abbreviated reference below.

### Feature Comparison Matrix

Rows: core features, pricing tiers, platform capabilities (web, iOS, Android, API).  
Columns: your product + up to 3 competitors.  
Score each cell 1–5. Sum to get total out of 60.  
**Score legend:** 5=Best-in-class, 4=Strong, 3=Average, 2=Below average, 1=Weak/Missing

### Pricing Analysis

Capture per competitor: model type (per-seat / usage-based / flat rate / freemium), entry/mid/enterprise price points, free trial length.  
Summarize: price leader, value leader, premium positioning, your position, and 2–3 pricing opportunity bullets.

### SWOT Analysis

For each competitor: 3–5 bullets per quadrant (Strengths, Weaknesses, Opportunities for us, Threats to us). Anchor every bullet to a data signal (review quote, job posting count, pricing page, etc.).

### Positioning Map

2x2 axes (e.g., Simple ↔ Complex / Low Value ↔ High Value). Place each competitor and your product. Bubble size = market share or funding. See `references/analysis-templates.md` for ASCII and editable versions.

### UX Audit Checklist

Onboarding: TTFV (minutes), steps to activation, CC-required, onboarding wizard quality.  
Key workflows: steps, friction points, comparative score (yours vs. theirs).  
Mobile: iOS/Android ratings, feature parity, top complaint and praise.  
Navigation: global search, keyboard shortcuts, in-app help.

### Action Items

| Horizon | Effort | Examples |
|---------|--------|---------|
| Quick wins (0–4 wks) | Low | Add review badges, publish comparison landing page |
| Medium-term (1–3 mo) | Moderate | Launch free tier, improve onboarding TTFV, add top-requested integration |
| Strategic (3–12 mo) | High | Enter new market, build API v2, achieve SOC2 Type II |

### Stakeholder Presentation (7 slides)

1. **Executive Summary** — Threat level (LOW/MEDIUM/HIGH/CRITICAL), top strength, top opportunity, recommended action
2. **Market Position** — 2x2 positioning map
3. **Feature Scorecard** — 12-dimension radar or table, total scores
4. **Pricing Analysis** — Comparison table + key insight
5. **UX Highlights** — What they do better (3 bullets) vs. where we win (3 bullets)
6. **Voice of Customer** — Top 3 review complaints (quoted or paraphrased)
7. **Our Action Plan** — Quick wins, medium-term, strategic priorities; Appendix with raw data

## Related Skills

- **Product Strategist** (`product-team/product-strategist/`) — Competitive insights feed OKR and strategy planning
- **Landing Page Generator** (`product-team/landing-page-generator/`) — Competitive positioning informs landing page messaging
