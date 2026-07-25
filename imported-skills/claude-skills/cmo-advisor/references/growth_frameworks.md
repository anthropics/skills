# Growth Frameworks Reference

Playbooks for PLG, sales-led, community-led, and hybrid growth models. Includes growth loops, funnel design, and guidance on when and how to switch models.

---

## 1. Product-Led Growth (PLG) Playbook

### What PLG Actually Is

PLG means the product is the primary distribution mechanism. Not "we have a free trial." Not "our product is self-serve." PLG means the product creates acquisition, retention, and expansion — and does so at a scale and cost no sales team can match.

**The minimum requirements for PLG to work:**
1. **Fast time-to-value:** Users must get a meaningful outcome within one session (ideally < 30 minutes)
2. **Low friction to start:** No sales call, no implementation project, no credit card required (for top of funnel)
3. **Built-in virality or network effects:** Usage creates exposure or value that draws in other users
4. **Self-serve monetization or expansion path:** Freemium → paid, or individual → team → company

If any of these is missing, you don't have PLG — you have a website with a free trial.

### PLG Funnel: The Four Stages

**Stage 1: Acquisition**
The user discovers and signs up for the product without talking to sales.

Key channels:
- Organic search (SEO targeting jobs-to-be-done searches)
- Product hunt launches
- Referral and invite loops (users share the product with colleagues)
- Developer communities and open-source contributions

Metric: Visitor-to-signup rate

Benchmark: 2-8% for B2B SaaS (varies heavily by product complexity)

**Stage 2: Activation**
The user reaches the "aha moment" — the point where the product delivers its core value for the first time.

Finding the aha moment:
- Look at the behaviors that differentiate users who stay from users who churn in the first 30 days
- The aha moment is not creating an account. It's completing the first outcome.
- For Slack: sending a message in a real channel
- For Dropbox: adding a file from a second device
- For HubSpot: publishing a form that captures a real lead

Metric: Activation rate (% of signups who complete the aha moment action within 7 days)

Benchmark: 25-40% is strong. < 15% means the onboarding is broken.

**Stage 3: Retention**
Users return to the product and build habitual use.

Retention analysis:
- Cohort retention curves (by signup week/month)
- Day 1, Day 7, Day 30, Day 90 retention rates
- Feature adoption by retained vs. churned users (which features predict retention?)

Metric: D30 retention rate (% of users still active 30 days after signup)

Benchmark: > 40% D30 retention is strong for B2B products

**Stage 4: Revenue**
Self-serve conversion from free to paid, or expansion from individual to team.

PQL (Product-Qualified Lead) signals:
- Reached a usage limit (invites, storage, seats)
- Used a premium feature in trial mode
- Team size on the account reached a threshold
- High-frequency usage above a defined threshold

Metric: PQL conversion rate (% of PQLs who convert to paid within 30 days)

Benchmark: 15-30% for well-designed PLG products

### PLG Expansion Model

PLG growth compounds through account expansion:

```
Individual user discovers product
    → Gets value, invites teammates
        → Team adopts product
            → Becomes department-wide
                → Finance/IT gets involved
                    → Enterprise contract
```

This is "bottom-up" enterprise: individual adoption precedes company-wide purchase. It's also the most defensible moat — when every engineer in the company uses your product individually, procurement cancellation is very hard.

**Expansion levers:**
- Seat-based pricing (more users = more revenue, aligned with value)
- Usage-based pricing (more usage = more value = more revenue)
- Feature gating (team/enterprise features visible but gated, creating pull to upgrade)
- Admin discovery (usage reports surface to managers who didn't know they had a product champion)

### PLG Diagnostic

| Question | Healthy | Unhealthy |
|----------|---------|-----------|
| Time-to-value | < 30 minutes | > 2 hours |
| Activation rate | > 30% | < 15% |
| D30 retention | > 40% | < 20% |
| PQL conversion | > 15% | < 5% |
| NPS from self-serve users | > 40 | < 20 |
| Viral coefficient | > 0.3 | < 0.1 |

### PLG Team Structure

```
Head of Growth (often VP Product or VP Marketing)
├── Growth PM (owns activation and retention loops in product)
├── Growth Engineer (2-3 engineers dedicated to growth experiments)
├── Data Analyst (experimentation, funnel analysis, cohort reports)
└── Growth Marketer (acquisition, SEO, referral programs)
```

The growth team sits between product and marketing. This is intentional — they own the product loops that drive acquisition and retention.

---

## 2. Sales-Led Growth (SLG) Model

### The SLG System

In SLG, marketing's job is to fill the sales pipeline. Sales converts it. The system only works if marketing and sales agree on definitions, SLAs, and shared metrics.

**The SLG funnel:**

```
Awareness (Impressions, reach, brand search)
    ↓
Lead (Name + contact info captured)
    ↓
MQL — Marketing Qualified Lead (meets ICP criteria, intent signal detected)
    ↓ [Marketing → Sales handoff]
SAL — Sales Accepted Lead (sales reviews and accepts the lead)
    ↓
SQL — Sales Qualified Lead (sales confirms budget, authority, need, timeline)
    ↓
Opportunity (Formal deal in pipeline, has a close date)
    ↓
Closed-Won
```

**The MQL definition problem:**
Most marketing-sales friction traces to an unclear MQL definition. The MQL should be:
- ICP-matched (company size, industry, role)
- Intent-signaled (visited pricing page, attended webinar, downloaded high-intent content)
- Not just email address + "subscribed to newsletter"

**A concrete MQL definition:**
> Company 50-500 employees, B2B SaaS, role is VP Engineering or CTO or CISO, AND has performed 2+ of: attended webinar, visited pricing page, requested demo, downloaded security report, attended event.

This definition makes the MQL useful. If you can't score it in your CRM without human judgment, it's not a definition — it's a guideline.

### SLG Conversion Rate Benchmarks

| Stage | Average B2B SaaS | Top Quartile |
|-------|-----------------|--------------|
| Lead → MQL | 5-15% | > 20% |
| MQL → SAL | 50-70% | > 75% |
| SAL → SQL | 30-50% | > 60% |
| SQL → Opportunity | 60-80% | > 85% |
| Opportunity → Closed-Won | 20-30% | > 40% |

**End-to-end:** Lead → Closed-Won: 1-5% (wide range by ACV and ICP quality)

### Pipeline Coverage Mechanics

A healthy SLG pipeline has 3-4x coverage against quota.

If a sales rep has a $500K quarterly quota:
- They need $1.5M-$2M in active pipeline
- Pipeline must be distributed across stages (not all "prospecting")
- Stage distribution benchmark: 30% early, 40% mid, 30% late

Insufficient coverage (< 3x) is a lagging indicator of a miss — by the time coverage is low, it's too late to recover in the same quarter. Coverage should be tracked weekly.

### SLG Demand Generation Channels

**High-intent channels (bottom of funnel):**
- Paid search on buying-intent keywords (e.g., "[competitor] alternative", "best [category] software")
- Review site presence (G2, Capterra) — buyers use these before vendor websites
- Outbound SDR targeting specific accounts (ABM)

**Medium-intent channels (middle of funnel):**
- Webinars and virtual events (capture active learners)
- Gated content (guides, benchmarks, templates — ICP-specific)
- Retargeting to website visitors

**Awareness channels (top of funnel):**
- Content and SEO (captures people learning about the problem)
- Podcast sponsorships, industry media
- Conference sponsorship and speaking
- Paid social (LinkedIn for B2B)

### ABM (Account-Based Marketing) in SLG

ABM flips the funnel: instead of generating leads and filtering for good ones, you start with target accounts and run coordinated campaigns against them.

**Tiers:**
- **Tier 1 (1:1):** 5-20 strategic accounts, fully customized campaigns, dedicated SDR+AE pairs, executive outreach
- **Tier 2 (1:few):** 50-200 accounts, programmatic personalization, SDR sequences, targeted events
- **Tier 3 (1:many):** 500+ accounts, standard campaigns with light personalization

ABM requires tight sales/marketing alignment. If sales doesn't work the accounts marketing targets, ABM produces zero results.

---

## 3. Community-Led Growth (CLG)

### The CLG Thesis

Community-led growth works when:
1. Your buyers want to learn from peers, not vendors
2. There's a strong practitioner identity (developers, data teams, security, FinOps)
3. Your category is complex enough that buyers need education before purchasing
4. You can commit to building genuine community, not a marketing channel in disguise

**The fundamental rule of CLG:** The community must deliver value to members whether or not they ever buy your product. If the only purpose of the community is to sell to members, the community will die.

### CLG Stages

**Stage 1: Find the community**
The community often exists before you build it. Find where your practitioners already gather:
- Slack groups, Discord servers
- Subreddits and LinkedIn groups
- Conference hallways
- Open-source repositories

Before building, participate. Earn trust. Understand the conversations.

**Stage 2: Become the knowledge hub**
Establish your company as the best source of information on the category problem:
- Publish the benchmark study everyone references
- Host the conference that defines the industry
- Create the certification practitioners want on their resume
- Open-source the tools the community needs

**Stage 3: Build the platform**
Create a dedicated community space (Slack, Discord, forum):
- Community must be practitioner-first, not vendor-first
- Community managers who genuinely care about member value
- Content from members, not just from your company
- Events that build member relationships, not just product demos

**Stage 4: Convert community to customers**
Community members who become customers do so because they trust you, not because you sold them. Conversion paths:
- Community members see peer success with your product
- Product-qualified signals from community members who trial the product
- Direct outreach from sales to active community members (with permission and context)
- Enterprise deals from companies whose employees are active in the community

### CLG Metrics

| Metric | Definition | Health Signal |
|--------|-----------|--------------|
| Monthly active members | Members who post, comment, or engage | > 15% of total members |
| Community-sourced pipeline | $ pipeline where community was first touch | Track and trend |
| Community-influenced pipeline | $ pipeline with any community touchpoint | > 30% of total pipeline |
| NPS of community members vs. non-members | Loyalty difference | Community members should score 20+ pts higher |
| Member-generated content % | % of content posted by non-employees | > 60% is healthy community |
| Time from community join to product trial | | Shortens as community matures |

### CLG Anti-Patterns

- **Community as a newsletter:** If members can't interact with each other, it's not a community — it's a list.
- **Product launches in the community:** Nothing kills community trust faster than using it for sales announcements.
- **Community without a community manager:** Communities left to run themselves become ghost towns or become toxic.
- **Measuring community by member count:** Ghost members are noise. Active engagement is signal.

---

## 4. Hybrid Growth Models

### PLG + SLG ("Product-Led Sales" or PLS)

The most common hybrid at growth stage. PLG handles SMB self-serve; sales closes enterprise.

**The PQL-to-sales handoff:**

Define the triggers that move a product-qualified lead to a sales-assisted motion:
- Company has > X users (e.g., 10+ users on a team account)
- Usage exceeds Y threshold in 30 days
- Account is a named target in the ABM list
- User explicitly requested a demo or upgrade assistance

**The risk:** Sales team ignores PLG pipeline because deal size is smaller. Fix: separate quotas and commission structures for self-serve expansion vs. new enterprise logos.

**The opportunity:** PLG creates pre-qualified champions inside accounts. Sales doesn't have to create interest — they convert it. Win rates in PLS motions are typically 30-50% higher than cold outbound.

### SLG + CLG

Community builds brand and generates inbound pipeline for sales.

This hybrid works when:
- Sales cycles are long (6-18 months)
- Buyers do extensive research before engaging with vendors
- The community validates your credibility before sales conversations begin

**The integration:**
- Community team feeds content insights to demand gen
- Event attendees become high-priority SDR sequences
- Active community members get dedicated AE outreach with community context
- Win/loss analysis includes community touchpoints

### PLG + CLG

The developer/open-source hybrid. PLG handles product adoption; community handles advocacy and content.

**Examples:** HashiCorp (Terraform community + enterprise sales), Elastic (open-source + community + commercial), Tailscale (developer community + self-serve + enterprise).

**How it compounds:**
```
Community member learns from community content
    → Discovers open-source or free tier
        → Gets value in first session
            → Shares experience in community
                → New members discover product through community content
```

---

## 5. Growth Loops vs. Funnels

### The Difference

**A funnel** is linear. It requires constant input at the top to produce output at the bottom. If you stop feeding it, it stops producing.

**A growth loop** is cyclical. Output from one stage becomes input to the next. The system compounds.

### Common Growth Loops

**Viral loop:**
```
User gets value → Invites colleague → Colleague signs up →
Colleague invites another colleague → ...
```
Viral coefficient (K) = (Average invites per user) × (Conversion rate of invites)
- K > 1: Exponential growth (rare)
- K 0.5-1: Strong viral assist
- K < 0.3: Viral is not a meaningful growth driver

**Content SEO loop:**
```
Publish content on [topic] → Ranks in search →
Drives signups → Users share content → Builds backlinks →
Better rankings → More content is possible
```
This loop takes 12-24 months to activate but is extraordinarily defensible once running.

**UGC (User-Generated Content) loop:**
```
Users share their work publicly (templates, analyses, portfolios) →
Others discover the work → They find the product →
They create and share their own work → ...
```
Figma, Notion, Airtable, Canva — all run this loop.

**Data network effect loop:**
```
More users → More data → Better product →
More users attracted → ...
```
LinkedIn, Waze, Duolingo — accuracy or relevance improves as the user base grows.

**Integration loop:**
```
Product integrates with X → X's users discover your product →
More integrations possible → More discovery surfaces → ...
```
Zapier, Slack apps, Salesforce AppExchange — being in the ecosystem creates distribution.

### Building a Growth Loop

**Step 1: Map the current funnel**
Where do customers come from? What are the conversion steps?

**Step 2: Find the output**
What does a successful customer produce?
- Invite emails
- Shared content
- Public work visible to others
- Reviews or testimonials

**Step 3: Design the loop**
How does that output become tomorrow's input to acquisition?
- If they share → is there a landing page that captures the new visitor?
- If they invite → is the invite experience friction-free?
- If they create content → does it rank in search or appear in relevant communities?

**Step 4: Measure loop velocity**
For each loop, measure:
- Cycle time: How long does one full cycle take?
- Conversion at each step: Where does the loop break down?
- Loop coefficient: How many new users does one existing user generate?

---

## 6. When to Switch Growth Models

### The Warning Signs

**PLG-to-SLG triggers:**
- Enterprise accounts are signing up via PLG but aren't expanding without human intervention
- Average deal sizes in enterprise are 10-20x SMB, and you're leaving revenue on the table
- Product adoption in enterprise requires configuration or integration that needs support
- PLG accounts churn at higher rates than sales-assisted accounts

**SLG-to-PLG/PLS triggers:**
- CAC is increasing year-over-year as competition for sales talent intensifies
- Smaller competitors are winning deals with self-serve
- Customers are asking "can I just try this myself?"
- ACV is declining as the market matures and products commoditize
- Sales team efficiency (revenue per sales rep) is declining

**Adding CLG to existing motion:**
- Sales cycles are long and trust is the primary barrier
- SEO and content are generating traffic but low conversion (awareness without trust)
- Competitors are building community and you're not present
- Customer success teams report that customers who participate in user groups retain better

### The Transition Playbook

**Phase 1: Prove it before scaling (months 1-6)**
Don't restructure the team to support the new model before proving it works.
- Run a pilot: 3-5 SDRs testing PLG signals as outreach triggers (for PLG → PLS)
- Or: Launch a beta community with 100 core customers (for adding CLG)
- Measure the metrics of the new model, compare to current model

**Phase 2: Parallel running (months 6-12)**
Run both models simultaneously. Don't kill the current model while building the new one.
- Set clear boundaries on which accounts go to which motion
- Build dedicated teams for each model (don't ask the same people to do both)
- Define success metrics for the new model independently

**Phase 3: Rebalance (months 12-18)**
Once the new model proves its unit economics:
- Shift headcount and budget to the more efficient model
- Keep the old model for the segments where it still works
- Document what the new model requires to sustain itself

**The anti-pattern:** Announcing a model shift without proof, restructuring the team, and discovering after 12 months that the new model doesn't work. By then, the old model's momentum is gone and you've burned a year.

### Growth Model Maturity Matrix

| Dimension | PLG | SLG | CLG |
|-----------|-----|-----|-----|
| Time to first results | 3-6 months | 1-3 months | 12-18 months |
| Requires up-front product investment | High | Low | Medium |
| Scales without linear headcount | Yes | No | Yes |
| Predictable pipeline | Low (early) | High | Low (early) |
| CAC trend over time | Decreases | Flat/increases | Decreases |
| Works for ACV > $50K | Only with SLG assist | Yes | Yes |
| Works for ACV < $5K | Yes | No | Only with PLG |
| Defensibility once established | High | Low | Very high |
