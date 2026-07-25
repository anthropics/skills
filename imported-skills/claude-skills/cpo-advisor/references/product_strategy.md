# Product Strategy Reference

Frameworks for product vision, competitive positioning, portfolio management, and board reporting. No theory — only what CPOs actually use.

---

## 1. Vision Frameworks

### Jobs to Be Done (JTBD)

JTBD is not a feature framework. It's a way to understand *why* customers hire your product and under what circumstances.

**The core insight:** People don't want your product. They want to make progress in their lives, and they hire your product to help. When you understand the job, you understand competition differently.

#### Conducting JTBD Interviews

**Who to interview:** Recent buyers and recent churners. Not power users — they're already converted.

**The interview script (condensed):**
```
1. "Walk me through the last time you [started using / stopped using] this product."
2. "What were you doing the day before you decided?"
3. "What else did you consider?"
4. "What almost stopped you from doing it?"
5. "Now that you're using it, what does your day look like differently?"
```

**What you're extracting:**
- **Functional job:** What task are they accomplishing?
- **Emotional job:** How do they feel during and after?
- **Social job:** How are they perceived?
- **Timeline:** What triggered the switch? (the "push" from old solution + "pull" toward new one)
- **Anxieties:** What almost prevented adoption?
- **Competing solutions:** What are they comparing you to, including "do nothing"?

#### JTBD Output: The Job Story

Format better than "user story" for strategic decisions:

```
When [situation],
I want to [motivation/job],
So I can [expected outcome].
```

**Example (healthcare scheduling):**
```
When I'm trying to coordinate my parent's care from another city,
I want to see their upcoming appointments and have someone confirm changes,
So I can feel confident they won't miss critical treatments.
```

This is a different product than "schedule management software." The strategic implications — care coordination, family access, confirmation workflows — flow from the job.

#### JTBD → Product Strategy

| Job Insight | Strategic Implication |
|-------------|----------------------|
| Job is episodic (quarterly) | Engagement model must reach them before they need it |
| Job is habitual (daily) | DAU/MAU matters; build for habit formation |
| Job has high stakes | Trust and reliability > features; invest in onboarding + support |
| Job is social | Network effects possible; virality is structural, not a campaign |
| Job is delegated (done for someone else) | Two users: the buyer and the beneficiary. Design for both. |

---

### Category Design

If you're fighting for share in an existing category, you're playing defense on someone else's field.

**Category design premise:** Companies that define the category typically capture 76% of the market cap of that category. Name the category, own it.

#### The Category Design Process

**Step 1: Name the problem, not the solution.**
```
Wrong: "We make AI-powered customer support software."
Right: "The support team doesn't need more tickets. They need fewer problems."
```

**Step 2: Define the enemy.**
The enemy is the *old way* of solving the problem, not a competitor.
- Salesforce's enemy: spreadsheets and disconnected tools (not Siebel)
- Slack's enemy: email overload (not HipChat)
- Your enemy: ___________

**Step 3: Create the category name.**
It should be obvious in hindsight, not predictable in advance. Test it:
- Does it describe the problem, not the solution?
- Is it 2-3 words?
- Could a journalist use it without quoting you?

**Step 4: Missionary selling, not mercenary selling.**
Category kings educate the market before they sell to it. Content, thought leadership, community, and free tools all matter here — not as marketing tactics but as category creation.

**Step 5: Be the reference customer.**
Get the logos that define the category. The companies others look to. When others adopt, they don't want "a tool" — they want "what [Reference Customer] uses."

---

## 2. Competitive Moats

A moat is a structural advantage that compounds over time. Features are not moats. Pricing is not a moat. A moat is why, even if a competitor perfectly copies your product today, you still win.

### Moat Type 1: Network Effects

The product becomes more valuable as more users join. Two subtypes:

**Direct network effects:** Each user makes the product better for all other users (WhatsApp, Slack).

**Indirect network effects:** Each user on one side makes the product better for the other side (Uber drivers + riders, App Store developers + users).

**Data network effects:** More users → more data → better product → more users.

#### Network Effect Diagnostic
```
Question 1: Does adding user N make the product better for user N-1?
  No  → You don't have direct network effects
  Yes → Map exactly how and how much

Question 2: Does adding user N make the product better for users on the OTHER side?
  No  → You don't have indirect network effects
  Yes → Identify which side is the constraint (supply or demand)

Question 3: Does using the product generate data that improves the product?
  No  → You don't have data network effects
  Yes → What is the data flywheel? Where does it compound?
```

**Building network effects intentionally:**
- Most products accidentally have weak network effects
- Design for network effects from Day 1: sharing, notifications, collaboration, integrations
- Measure network effect strength: "What % of new users were referred by existing users?"

### Moat Type 2: Switching Costs

The cost — time, money, risk — of leaving your product. The highest switching costs are:

| Switching Cost Type | Example | CPO Action |
|--------------------|---------|-----------|
| **Data lock-in** | Years of history, reports, trained models | Make data the experience, not just the storage |
| **Workflow integration** | 23 integrations, custom automations | Every integration is a switching cost. Build them. |
| **Team adoption** | Entire team trained on your tool | Multi-seat training investments pay switching cost dividends |
| **Contractual** | Annual contracts, SLAs | Long contracts are not a moat — customers resent them |
| **Process embedding** | Your product IS their process | Aim here. This is the deepest moat. |

**Warning:** Switching costs from data lock-in without value lock-in breed resentment, not loyalty. Customers who stay because they're trapped will leave the moment a migration tool appears.

### Moat Type 3: Data Advantages

Having data others can't easily get. Three subtypes:

**Proprietary data:** Data only you have access to (exclusive partnerships, sensor networks, unique user behavior at scale).

**Data scale:** Same type of data but at 10x the volume of competitors. Scale compounds model accuracy.

**Data variety:** Unique combination of data types. Not just usage data — usage + outcome data + external context.

**Testing your data moat:**
```
1. What data do we have that competitors don't?
2. At what volume does our data create a meaningfully better product?
3. Are we at that volume? If not, when?
4. Could a competitor buy or partner their way to equivalent data?
5. Is our data improving the product automatically, or only when we analyze it manually?
```

### Moat Type 4: Economies of Scale

Unit economics improve as you scale. Infrastructure costs drop per unit. Brand recognition lowers CAC. Negotiating power increases.

This is a real moat but the weakest one for product strategy — it doesn't keep faster-moving competitors from attacking while you're small.

### Moat Scorecard

Score each moat type 0-3 for your current product:

```
0 = Not present
1 = Weak / easily replicated
2 = Meaningful / takes 12-18 months to replicate
3 = Strong / structural advantage

Network effects (direct):     __/3
Network effects (indirect):   __/3
Network effects (data):       __/3
Switching costs (data):       __/3
Switching costs (workflow):   __/3
Switching costs (team):       __/3
Data advantages (exclusive):  __/3
Data advantages (scale):      __/3
Economies of scale:           __/3

Total: __/27

< 9:  No meaningful moat. Compete on execution speed.
9-15: Early moat. Identify and reinforce 1-2 strongest types.
16-21: Real moat. Invest to compound it.
> 21: Strong moat. Defend and expand.
```

---

## 3. Product Positioning

Positioning is not messaging. Positioning is the choice of: *Who is this for, what does it replace, and on what dimension do we win?*

### The Positioning Canvas (after April Dunford)

```
1. Competitive Alternatives
   What would customers do if your product didn't exist?
   (This is your real competition, not just your vendor category)

2. Unique Attributes
   What capabilities do you have that alternatives lack?
   (Features, but described neutrally, not as marketing)

3. Value (Outcomes)
   What does each unique attribute enable for customers?
   (Bridge from feature → outcome, not feature → feature)

4. Customer Who Cares
   Who values those outcomes enough to pay for them?
   (The customer segment for whom this value is highest)

5. Market Category
   Where does the customer put you when comparing options?
   (Frame the category to win, not to be fair)

6. Relevant Trends
   What's changing in the world that makes this more valuable now?
   (Why this moment? Urgency enabler.)
```

### Positioning Against Three Competitors

**Positioning vs. direct competitor:**
Identify one dimension where you structurally win. "Better" is not a position.
- Win on depth: more powerful in one scenario
- Win on simplicity: fewer decisions, fewer steps
- Win on integration: works with what they already use
- Win on price/value: same outcome, lower cost or risk

**Positioning vs. indirect alternative:**
The customer's current solution (spreadsheet, manual process, point solution).
- Make switching cost obvious (what are they giving up per week?)
- Make the switch simple (migration, onboarding, no data loss)
- Find the "aha moment" fast (value before they revert)

**Positioning vs. doing nothing:**
The hardest competitor. Status quo has zero switching cost.
- Quantify the cost of inaction (time, risk, revenue, competitive risk)
- Find the trigger event that makes inaction intolerable
- Show the risk is higher than the switch cost

### Positioning Failure Modes

| Failure | Description | Fix |
|---------|-------------|-----|
| **For everyone** | No segment. "Any company that needs X." | Name the best-fit customer. |
| **Feature positioning** | "The only tool with [feature X]" | Features are table stakes. Lead with outcome. |
| **Vague differentiation** | "Easier, faster, better" | Measurable, specific, or don't say it. |
| **Category misfit** | In a category where you can't win | Either own the category or name a new one |
| **Lagging positioning** | Positioned for who you were, not who you are | Reposition every 18-24 months or after major product change |

---

## 4. Portfolio Management

### Applying BCG Matrix to Product Lines

BCG matrix was designed for business units. Applied to product lines:

**Inputs:**
- Market growth rate (industry growth, not your growth)
- Relative market share (your share vs. largest competitor)
- Revenue contribution (absolute)
- Investment level (engineering + sales + marketing per product)

**Calculation:**
```
Market share ratio = Your market share / Largest competitor's market share
Growth rate = Market CAGR (next 3 years estimate)

Stars:          share ratio > 1.0, growth > 10%
Cash Cows:      share ratio > 1.0, growth < 10%
Question Marks: share ratio < 1.0, growth > 10%
Dogs:           share ratio < 1.0, growth < 10%
```

### Portfolio Allocation Rules

**Star products:**
- Invest at or above market growth rate
- Goal: maintain share leadership as market grows
- Don't extract cash — reinvest
- Metrics: market share trend, NPS, retention, feature velocity

**Cash Cow products:**
- Minimum investment to maintain market position
- Goal: maximize free cash flow
- Resist the urge to innovate — incremental improvements only
- Metrics: gross margin, churn rate, support cost per customer

**Question Mark products:**
- Binary decision: invest to win or exit
- "Maintain" is not a strategy for question marks — you lose share every quarter you're neutral
- Set a deadline (2 quarters) and a threshold for investment decision
- Metrics: share gain rate, customer acquisition efficiency

**Dog products:**
- Decision: sell, sunset, or bundle
- Never "fix" a dog with more investment
- Timeline to sunset: 6-12 months, migration plan for existing customers
- Metrics: customer migration rate, revenue retained

### Portfolio Review Template

Run quarterly. One slide per product.

```
Product: [Name]
Current Quadrant: [Star/Cash Cow/Question Mark/Dog]
Revenue this quarter: $___
Revenue growth QoQ: ___%
Market share estimate: ___%
Investment level (% of eng capacity): ___%
Investment posture: [Invest / Maintain / Kill]

Key metric: [Name] → [Current value] → [QoQ trend]
Top risk: [One thing that could change this assessment]
Decision required: [Yes/No] | [What decision?]
```

### The Honest Portfolio Conversation

Questions CPOs avoid but boards ask:
- "Which product would we kill if we had to? What's stopping us?"
- "Are we funding dogs because the team is attached or because there's a real plan?"
- "What would our margins look like if we stopped investing in the bottom 2 products?"
- "What's the dependency between our products? Are we a platform or a bundle of unrelated tools?"

---

## 5. Board-Level Product Reporting

### What Good Looks Like

Board product updates fail in three ways:
1. Too much roadmap detail (feature list masquerading as strategy)
2. No trend context (showing a number without showing if it's getting better or worse)
3. No risks (all good news = no credibility)

### The 5-Slide Board Product Update

**Slide 1: North Star Metric**
```
Title: Product Health — [Quarter]

[Chart: North star metric over last 12 months, quarterly cohorts]

This quarter: [Value] | Prior quarter: [Value] | YoY: [Value]
Target: [Value] | Status: On track / At risk / Behind

Drivers (2-3 bullets):
• What's driving improvement: ___
• What's dragging: ___
• What we're doing about the drag: ___
```

**Slide 2: Retention and PMF**
```
Title: Product-Market Fit Evidence

[Chart: D30 retention by cohort, last 6 cohorts]
[Callout: Sean Ellis score = XX% (target: > 40%)]

PMF status: Achieved / Approaching / Not yet
Best segment: [Describe — where retention is strongest]
Weakest segment: [Describe — and what we're doing about it]
```

**Slide 3: Portfolio Status**
```
Title: Portfolio — Invest / Maintain / Kill

| Product | Quadrant | Revenue | Growth | Posture | Risk |
|---------|---------|---------|--------|---------|------|
| [A]     | Star    | $___    | +XX%   | Invest  | ___  |
| [B]     | Cash Cow| $___    | +X%    | Maintain| ___  |
| [C]     | Dog     | $___    | -X%    | Kill Q3 | ___  |

Changes since last quarter: ___
Decisions needed from board: ___
```

**Slide 4: Strategic Bets**
```
Title: Bets This Half — [H1/H2]

Bet 1: [Name]
  Hypothesis: If we [do X], [segment Y] will [do Z]
  Evidence so far: [Data]
  Confidence: [Low / Medium / High]
  Decision point: [When do we know?] [What will we measure?]

Bet 2: [Name]
  [Same structure]
```

**Slide 5: Top Risks**
```
Title: Product Risks — [Quarter]

Risk 1: [Name]
  What it is: ___
  Probability: [Low/Med/High]
  Impact if realized: ___
  Mitigation: ___

Risk 2: [Name]
  [Same structure]

Risk 3: [Name]
  [Same structure]
```

### Delivering in the Board Meeting

- Never read the slide
- Lead with the conclusion, not the data
- Prepare for "what if that assumption is wrong?" for every bet
- When something underperformed: say it, own it, explain what changed
- Never present a number you can't explain 3 levels deep

**Example of bad delivery:**
"Our north star is up 15% QoQ, which is great. We're tracking well."

**Example of good delivery:**
"North star is up 15% — ahead of plan. The majority of that is from the enterprise cohort activated in October, driven by the workflow automation feature we shipped in September. The consumer segment is flat, which is a concern. We're running three experiments this quarter to diagnose whether that's an acquisition problem or an activation problem — I'll have an answer for next quarter."

---

## Quick Reference: Framework Summary

| Need | Framework |
|------|----------|
| Why do customers use us? | Jobs to Be Done |
| How do we define our market? | Category Design |
| What's our structural advantage? | Moat Scorecard |
| How do we position? | April Dunford Positioning Canvas |
| Which products to fund? | BCG Matrix + Invest/Maintain/Kill |
| How to report to the board? | 5-Slide Board Update |
