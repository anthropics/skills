# Pricing Strategy

Pricing is not a one-time decision. It's an ongoing hypothesis about value and willingness to pay. Most SaaS companies are underpriced by 20-40%.

---

## Pricing Models

### Per Seat / User

**How it works:** Customer pays a fixed amount per user, per month or year.

**Best for:**
- Collaboration tools (everyone who uses it needs a license)
- Productivity software where value scales with users
- Products where you want viral / network growth within accounts

**Pricing structure:**
```
Starter: $15/user/month (1-10 users)
Professional: $30/user/month (11-100 users)  
Enterprise: Custom (100+ users, negotiated)
```

**Pros:**
- Simple to understand and sell
- Revenue scales naturally with customer growth
- Predictable for customers (fixed monthly cost)

**Cons:**
- Customers negotiate volume discounts aggressively
- Discourages broad adoption if price is high (seat hoarding)
- Doesn't capture value for power users vs. light users
- Enterprises can negotiate $5/seat on a $25 product

**Watch for:** Customers sharing logins to avoid per-seat cost. Enforce with IP restrictions or SSO audit logs.

---

### Usage-Based Pricing (UBP)

**How it works:** Customer pays for what they consume — API calls, data processed, messages sent, compute hours, etc.

**Best for:**
- API companies, infrastructure, data platforms
- AI products (per-token, per-query pricing)
- Products where value scales non-linearly with usage
- Land-and-expand: low entry cost, grows with customer success

**Pricing structure:**
```
Free tier: First 10K API calls/month
Pay-as-you-go: $0.002 per API call
Committed use: $500/month for 500K calls (better rate)
Enterprise: Custom contract, committed volume discount
```

**Pros:**
- Customer pays in proportion to value received
- Low barrier to entry (customers start small, scale up)
- Natural expansion: customer success = revenue growth
- No "unused licenses" problem

**Cons:**
- Revenue is unpredictable for both you and the customer
- Hard to forecast; hard to budget for customer
- Customers may optimize to reduce usage (and your revenue)
- Complex billing; requires robust usage tracking infrastructure

**Usage-based pricing math:**
```
Unit cost (your COGS per unit): $0.0002 per API call
Target gross margin: 80%
Price = COGS / (1 - margin) = $0.0002 / 0.20 = $0.001 minimum

Add markup for value delivered above cost: $0.002 per call (10x markup at scale)
```

**Hybrid usage + seat approach:**
- Platform fee: $500/month (access, support, base features)
- Usage fee: $0.001 per API call above included 100K

---

### Flat Rate / Subscription

**How it works:** One price for full access, regardless of usage or users.

**Best for:**
- Simple products with limited feature differentiation
- Products where usage is predictable and bounded
- Customers who want budget certainty
- Early stage before you've figured out value segmentation

**Pros:**
- Simplest to sell and explain
- Easiest billing implementation
- Customers love budget predictability

**Cons:**
- Leaves money on the table for heavy users
- No natural expansion revenue mechanism
- Light users pay the same as power users (retention risk)

**When to move away from flat rate:**
- 20% of customers are using 80% of the product capacity
- Power users would clearly pay more; light users churn or underutilize
- You have a clear expansion story waiting to happen

---

### Tiered / Feature-Based

**How it works:** Multiple packages (Starter, Pro, Enterprise) with different feature sets and/or usage limits.

**Best for:**
- Multi-use-case products
- Different buyer types (individual vs. team vs. enterprise)
- Products with a natural upgrade path based on sophistication

**Structure (Good / Better / Best):**
```
Starter ($49/mo):      Core features, 3 users, 10GB storage
Professional ($149/mo): Advanced features, 25 users, 100GB, API access
Business ($499/mo):    All features, 100 users, 1TB, SSO, priority support
Enterprise (custom):   Unlimited, custom integrations, SLA, dedicated CSM
```

**Tier design principles:**
- Starter tier: removes friction, proves value, not the revenue center
- Professional: the primary revenue tier; 60-70% of customers land here
- Enterprise: custom pricing allows you to capture maximum value
- Each tier upgrade should have an obvious "must-have" feature for the target buyer

**What to gate on each tier:**
| Feature Type | Where to Put It |
|-------------|----------------|
| Core product functionality | Starter (must be useful) |
| Collaboration features | Pro (drives team usage) |
| Admin, security, SSO | Business/Enterprise |
| API / integrations | Pro and above |
| SLAs, dedicated support | Enterprise only |
| Advanced analytics | Business/Enterprise |

---

### Hybrid Pricing

**How it works:** Combination of models (e.g., platform fee + per seat + usage).

**Example:**
```
Platform fee: $2,000/month (access, core features, admin console)
Per seat: $50/user/month (up to 200 users)
Usage overage: $0.10/action above 100K included actions
```

**When to use hybrid:**
- Enterprise customers want budget certainty (platform fee) but your value scales with usage
- You have different cost structures for different features
- Customers have very different usage patterns across the base

**Pros:** Captures value at multiple dimensions. Hybrid is most common in enterprise SaaS.
**Cons:** More complex to explain and bill. Sales training burden increases.

---

## Value-Based Pricing Methodology

Cost-plus pricing is a race to the bottom. Price on value, not cost.

### Step 1: Define the Economic Outcome

What business result does your product deliver? Be specific.

**Weak:** "We help companies save time"
**Strong:** "We reduce onboarding time for new enterprise software by 40%, saving 8 hours per employee"

Map to one of:
- **Revenue increase** — "Our customers close 25% more deals using our CRM intelligence"
- **Cost reduction** — "We eliminate 60% of manual data entry for finance teams"
- **Risk reduction** — "We reduce compliance violations by 90%, avoiding $500K+ in potential fines"
- **Time savings** — "CSMs spend 5 fewer hours per week on manual reporting"

### Step 2: Quantify Per Customer

Calculate the dollar value of the outcome for your average customer.

```
Example: Data entry automation product
  Target customer: 50-person finance team
  Manual data entry: 4 hours/person/week
  Hours saved with product: 2.4 hours/person/week (60% reduction)
  Fully loaded cost of finance analyst: $75/hour
  
  Weekly savings: 50 employees × 2.4 hours × $75 = $9,000
  Annual savings: $9,000 × 52 weeks = $468,000
```

### Step 3: Determine Willingness to Pay

Customers will typically pay 10-20% of the value delivered for software.

```
Annual value delivered: $468,000
Willingness to pay range: $46,800 - $93,600/year
Current market pricing: ~$60,000/year

Your pricing: $72,000/year (between median and upper WTP)
```

**Test your hypothesis:**
- Interview 5-10 customers: "If we charged $X/year, is that reasonable?"
- Van Westendorp Price Sensitivity Meter:
  - "At what price is this too cheap to trust?"
  - "At what price is this a good deal?"
  - "At what price is this getting expensive but still worth it?"
  - "At what price is this too expensive?"

### Step 4: Validate with Win Rate Analysis

```
Run this analysis quarterly:
  Track win rate by price point (segmented if possible)
  Win rate 30-40%: pricing is likely right
  Win rate < 20%: price is too high OR value demonstration is broken
  Win rate > 50%: you're underpriced

Note: Distinguish between "lost on price" and "lost on fit."
  Lost on price + good ROI proof: test lower price or improve value story
  Lost on fit: ICP problem, not pricing problem
```

---

## Packaging (Good / Better / Best)

### The Three-Package Framework

Packaging is not just about features. It's about serving different buyer personas with different budgets and needs.

**Buyer personas by tier:**
```
Starter → The individual contributor or small team trying to solve an immediate problem
  - Low budget authority
  - Low-friction purchase (credit card, self-serve)
  - Needs quick time to value

Professional → The team manager or department head
  - $10K-100K budget authority
  - Works with inside sales
  - Needs collaboration features and reporting

Enterprise → The VP or C-suite buyer
  - Unlimited budget (but requires justification)
  - Needs compliance, security, SLAs, dedicated support
  - Long buying process, multiple stakeholders
```

### Packaging Design Rules

1. **Each tier must be useful on its own.** Starter can't be crippled—customers need to succeed.
2. **Upgrade triggers must be obvious.** When a customer hits a limit, the next tier should solve it clearly.
3. **Don't gate features that drive adoption.** Collaboration features gated in a low tier kill viral growth.
4. **Enterprise pricing is custom.** Show "Contact Sales" or a starting price. Don't publish a firm enterprise price—you'll anchor too low.
5. **Annual vs. monthly pricing:** Charge 15-25% more for monthly vs. annual. Incentivize annual prepay.

### Pricing Page Design

- Lead with the most popular tier (visually prominent)
- Show annual pricing by default (with toggle to monthly)
- Highlight one or two "recommended" plans
- Feature comparison table: minimize the number of rows (overwhelm = no decision)
- Show logos of customers on each tier (social proof by segment)
- Live chat for enterprise CTA, not "Contact Sales" form

---

## Pricing Experiments and Rollout

### Before You Change Pricing

**Internal checklist:**
- [ ] Validate new pricing with 5-10 current customers (interviews)
- [ ] Run a willingness-to-pay survey with 50+ prospects
- [ ] Model revenue impact: how many customers at new pricing are equivalent to current ARR?
- [ ] Get CFO sign-off on cash flow impact
- [ ] Prepare messaging for customers, website, sales team
- [ ] Set a rollout date 60-90 days out

### Testing Approaches

**Cohort testing (safest):**
- New signups see new pricing; existing customers are grandfathered
- Monitor: conversion rate, ACV, win rate, time-to-close
- Run for 90 days before full rollout

**A/B pricing test (higher stakes):**
- Half of new signups see price A, half see price B
- Risk: word gets out that prices differ (customer frustration)
- Use only on self-serve, where purchase is not sales-assisted

**Segment-specific rollout:**
- Change pricing in one segment (e.g., SMB) while holding enterprise steady
- Lower risk than full rollout; validate before expanding

### Pricing Rollout Plan

```
Day 0:  Decision made, pricing document approved
Day -60: Internal communication to sales, CS, support
Day -45: Customer communication drafted and reviewed
Day -30: New pricing live on website for new customers
Day -30: Existing customer email sent (90-day grandfather period)
Day -30: Sales team trained, FAQ document ready
Day -14: Second reminder to existing customers
Day 0:   Existing customers transition to new pricing
Day +30: Win rate analysis, NRR impact review
```

### Grandfathering Policy

- **Standard:** Grandfather existing customers at old price for 12 months
- **Aggressive:** 90 days grandfather, then new pricing applies (use if you're raising significantly)
- **Never:** Retroactive pricing changes with no notice. This is a churn trigger and brand damage.

Grandfathering message framing:
> "We're investing significantly in [feature areas]. As a valued customer, your pricing remains unchanged through [date]. After that, your new rate will be $X — still X% less than new customer pricing as a thank-you for your partnership."

---

## Competitive Pricing Analysis

### Mapping the Competitive Landscape

```
Step 1: List all direct competitors
Step 2: Find their public pricing (website, G2, Capterra)
Step 3: Secret shop their sales process for unpublished pricing
Step 4: Talk to customers who considered them ("What did they quote you?")
Step 5: Map to your packaging (apples-to-apples comparison)

Output: Competitive pricing matrix
  You: $X/month per seat at Pro tier
  Competitor A: $Y/month per seat at equivalent tier
  Competitor B: Custom (enterprise only)
```

### Competitive Positioning by Price

| Your Position | Situation | Response |
|--------------|-----------|---------|
| Significantly cheaper | Unclear why | Raise prices or clarify differentiation |
| Slightly cheaper | Winning on price | Test raising price, monitor win rate |
| At market | Competing on features | Make sure differentiation is clear in sales |
| Slightly more expensive | Win rate healthy | Price is justified by value |
| Significantly more expensive | Win rate low | Improve value proof or re-examine ICP |

### When "They're Cheaper" Appears in Deals

**Coach your reps:**
1. "What makes [Competitor] worth choosing over the $X difference?" (reframe value, not price)
2. "If price were equal, which would you choose and why?" (understand true preference)
3. "What's the cost of not solving this problem in Q3?" (urgency + value)
4. "What's their implementation cost and time?" (TCO, not ACV)

**If price is truly the barrier:**
- Offer a pilot at reduced scope (not price) to prove value
- Multi-year deal with year-one discount
- Defer payment to match their budget cycle (start in Q4, bill in Q1)
- Confirm it's price and not a champion issue or lack of urgency

---

## When to Raise Prices

### Green Lights for a Price Increase

**Product signals:**
- Customer usage growing QoQ (product delivers real value)
- NPS consistently > 40
- Feature requests indicate you're solving critical workflows
- Customers measuring and can articulate ROI

**Market signals:**
- Win rate > 35% (strong signal of underpricing)
- Waitlist or high inbound conversion without price objections
- Competitors raising prices (market is moving up)
- You've added significant value (new features, integrations, uptime improvements)

**Business signals:**
- Gross margin below 70% (cost inflation requires pricing response)
- CAC payback > 24 months (need higher ACV to fix unit economics)
- Haven't raised prices in 2+ years (inflation alone justifies adjustment)

### How Much to Raise

**Conservative:** 10-15% increase. Low risk, low disruption.
**Standard:** 15-30% increase. Acceptable if value story is strong.
**Aggressive:** 30-50% increase. Only with major product investment or clear underprice.
**Repositioning:** 2-5x increase. Rare; requires moving to a new buyer persona.

**Rule:** If fewer than 20% of prospects mention price as a concern, you're underpriced. Test.

### Price Increase Execution

1. Raise new business pricing immediately on the website
2. Communicate to existing customers with 90 days notice
3. Grandfather for 12 months OR give a 10-15% loyalty discount on new price
4. Track: conversion rate (new business), churn rate (existing), expansion ARR impact
5. Monitor win rate for 60 days post-increase; adjust if win rate drops > 5 points

**What not to do:**
- Don't apologize for raising prices
- Don't over-explain the justification (confident framing wins)
- Don't let sales reps negotiate discounts back to old pricing "just this once"
- Don't raise prices and remove features simultaneously
