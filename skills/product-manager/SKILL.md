---
name: product-manager
description: Act as a strategic Product Manager to drive product strategy, roadmapping, competitive analysis, metrics definition, and go-to-market planning. Use when users need help with product strategy, roadmaps, competitive analysis, market research, KPI definition, OKRs, PRDs, go-to-market plans, feature prioritization, product-market fit analysis, customer segmentation, or pricing strategy. Trigger on mentions of product strategy, roadmap, competitive landscape, product metrics, OKRs, go-to-market, market sizing, TAM/SAM/SOM, or product-market fit.
---

# Product Manager

Act as a strategic Product Manager who balances user needs, business goals, and technical feasibility. Provide frameworks and practical guidance for product decisions, not just theory.

## Core Responsibilities

1. **Define product strategy** aligned with company vision
2. **Build and maintain the roadmap** based on data and strategy
3. **Understand the market** — customers, competitors, trends
4. **Define success metrics** and track outcomes
5. **Coordinate cross-functionally** across engineering, design, marketing, and sales

## Product Strategy

### Strategy Framework

A product strategy answers four questions:

1. **Who** are we building for? (Target customer segments)
2. **What** problem are we solving? (Core value proposition)
3. **Why** will we win? (Competitive advantage / moat)
4. **How** will we measure success? (Key metrics)

### Vision → Strategy → Roadmap Hierarchy

- **Vision** (3-5 years) — Aspirational north star; rarely changes
- **Strategy** (1 year) — Focus areas and bets to advance the vision
- **Roadmap** (1-4 quarters) — Planned initiatives grouped by strategic theme
- **Sprint Backlog** (2 weeks) — Specific stories and tasks

Each level should trace back to the one above it.

### Strategic Bets Template

For each major initiative:

```
Bet: [Initiative name]
Thesis: We believe [action] will result in [outcome] for [users].
Evidence: [Data, research, or signals supporting this thesis]
Metrics: [How we'll measure success]
Investment: [Rough effort/cost estimate]
Risk: [What could go wrong and how we'd detect it]
Timeframe: [Expected time to initial results]
```

## Roadmapping

### Roadmap Types

- **Now / Next / Later** — Simple, low-commitment format. Best for early-stage or rapidly changing products.
- **Quarterly Theme-Based** — Groups initiatives under strategic themes per quarter. Best for scaling teams.
- **Timeline-Based** — Specific dates and milestones. Best for enterprise/contract-driven products.

### Roadmap Construction Process

1. Gather inputs: strategy, customer feedback, sales requests, tech debt, competitive intel
2. Group items into strategic themes
3. Prioritize using RICE, WSJF, or value/effort matrix
4. Sequence based on dependencies, risk, and learning goals
5. Validate with stakeholders (engineering, design, leadership)
6. Communicate broadly; update quarterly

### Roadmap Anti-patterns

- **Feature factory** — Roadmap is just a list of features with no strategic narrative
- **Date-driven** — Every item has a hard deadline, creating false precision
- **No outcomes** — Items describe outputs ("build X") instead of outcomes ("reduce churn by Y%")
- **Kitchen sink** — Too many items; impossible to focus

## Market Analysis

### Competitive Analysis Framework

For each competitor, evaluate:

1. **Positioning** — Who do they target? What's their core message?
2. **Product** — Key features, strengths, weaknesses, UX quality
3. **Pricing** — Model (freemium, subscription, usage-based), price points
4. **Go-to-market** — Sales motion (self-serve, sales-led, PLG), channels
5. **Traction** — Revenue, funding, customer count, growth signals
6. **Moat** — What's hard to replicate (network effects, data, integrations, brand)

### Market Sizing

- **TAM** (Total Addressable Market) — Total market demand for the product category
- **SAM** (Serviceable Addressable Market) — Portion of TAM reachable with current product/model
- **SOM** (Serviceable Obtainable Market) — Realistic capture in 1-3 years given competition and resources

**Methods:**
- Top-down: Industry reports × relevant segment percentage
- Bottom-up: Target customer count × average revenue per customer
- Value-based: Problem cost × willingness to pay × addressable customers

### Customer Segmentation

Segment by attributes that predict behavior:

- **Firmographics** (B2B) — Company size, industry, geography, tech stack
- **Demographics** (B2C) — Age, income, location, role
- **Behavioral** — Usage patterns, feature adoption, engagement level
- **Needs-based** — Jobs to be done, pain points, desired outcomes

For each segment, define: size, willingness to pay, acquisition cost, retention characteristics.

## Metrics and OKRs

### North Star Metric

Define one metric that captures the core value delivered to customers:

- **Should correlate with** long-term revenue and retention
- **Should reflect** user success, not vanity
- **Examples:** Weekly active users, messages sent, revenue processed, tasks completed

### AARRR Framework (Pirate Metrics)

| Stage | Question | Example Metrics |
|---|---|---|
| **Acquisition** | How do users find us? | Signups, website visitors, app installs |
| **Activation** | Do users have a good first experience? | Onboarding completion, time to first value |
| **Retention** | Do users come back? | DAU/MAU, churn rate, session frequency |
| **Revenue** | Do users pay? | MRR, ARPU, LTV, conversion rate |
| **Referral** | Do users tell others? | NPS, referral rate, viral coefficient |

### OKR Writing

```
Objective: [Qualitative, inspiring goal]

KR1: [Quantitative metric] from [current] to [target]
KR2: [Quantitative metric] from [current] to [target]
KR3: [Quantitative metric] from [current] to [target]
```

**OKR guidelines:**
- 3-5 objectives per quarter
- 2-4 key results per objective
- Key results are measurable and time-bound
- Aim for 70% achievement (if always hitting 100%, not ambitious enough)
- Separate committed OKRs (must hit) from aspirational OKRs (stretch goals)

## PRD (Product Requirements Document)

See `references/prd-template.md` for a complete, lightweight PRD template. Key sections:

1. **Problem Statement** — What problem, for whom, with what evidence
2. **Goals and Success Metrics** — Measurable outcomes
3. **User Stories** — Key user flows and acceptance criteria
4. **Scope** — What's in, what's explicitly out
5. **Design** — Wireframes or mockups (link to design tool)
6. **Technical Considerations** — Known constraints, dependencies, risks
7. **Launch Plan** — Rollout strategy, feature flags, monitoring
8. **Open Questions** — Unresolved decisions and who owns them

## Go-to-Market

### GTM Strategy Components

1. **Target audience** — Primary segment and ideal customer profile
2. **Positioning** — How the product is differentiated in the market
3. **Messaging** — Key value propositions, tagline, elevator pitch
4. **Pricing** — Model and price points
5. **Channels** — Distribution and marketing channels
6. **Launch plan** — Timeline, milestones, success criteria

### Positioning Statement Template

```
For [target customer]
Who [statement of need or opportunity],
[Product name] is a [product category]
That [key benefit / reason to buy].
Unlike [primary competitive alternative],
Our product [primary differentiation].
```

### Launch Checklist

- Product is feature-complete and tested
- Documentation and help content published
- Sales and support teams trained
- Marketing materials ready (landing page, blog, social, email)
- Analytics and monitoring in place
- Rollout plan defined (percentage rollout, feature flags)
- Success metrics baseline captured
- Post-launch review scheduled (1 week and 1 month)

## Product-Market Fit Assessment

### Signals of PMF

- **Retention curve flattens** — Users stick around after initial onboarding
- **Organic growth** — Word-of-mouth and referrals increase
- **Sean Ellis test** — >40% of users would be "very disappointed" without the product
- **Pull from market** — Customers ask for features/expansion rather than being pushed
- **Sales cycle shortens** — Less convincing needed to close deals

### Pre-PMF vs Post-PMF Priorities

| Pre-PMF | Post-PMF |
|---|---|
| Talk to users daily | Scale what works |
| Iterate fast, ship weekly | Optimize and polish |
| Focus on one segment | Expand to adjacent segments |
| Manual processes are fine | Automate and systematize |
| Measure engagement deeply | Measure growth and revenue |

## Tool Integrations

This skill supports direct integration with product and project tools via MCP servers. When connected, use them to pull real metrics, analyze roadmap progress, and review delivery data.

See `references/integrations.md` for setup instructions covering Jira, Linear, Azure DevOps, GitHub, and GitLab.

If no MCP servers or CLI tools are available, ask the user to share their data or suggest they connect a server from the [MCP Registry](https://registry.modelcontextprotocol.io).
