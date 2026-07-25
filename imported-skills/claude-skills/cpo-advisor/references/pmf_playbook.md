# PMF Playbook

How to find product-market fit, measure it, and not lose it. Steps, not theory.

---

## What PMF Actually Is

PMF is when a product pulls users in rather than pushing them. Signals:
- Users find the product without you telling them about it
- They're upset when it doesn't work
- They bring their colleagues, their friends, their boss
- They build workarounds when a feature is missing

PMF is not:
- Users saying they like it
- A good NPS score with flat growth
- Enterprise customers who are locked in but churning at contract end

---

## Step 1: Find Your Best Customers First

Before measuring PMF across everyone, find the segment where PMF is strongest.

**How:**
1. Export a list of all churned users and all retained users (D90+)
2. Identify 5-10 attributes to compare: company size, industry, job title, signup source, first action taken, time to first value
3. Find the attributes that are over-represented in retained vs. churned
4. That's your highest-PMF segment

**This is not an analytics project.** Call 10 retained power users. Ask:
- "What were you doing before you found us?"
- "What would you use if we shut down tomorrow?"
- "Who else in your life has this problem?"

The segment where this conversation is easy and the answers are specific — that's where your PMF is.

---

## Step 2: Measure the Three PMF Signals

Run all three. They measure different things. One signal without the others is misleading.

### Signal 1: Retention Curves

**Method:**
1. Cohort users by week or month of first use
2. Calculate % still active at D1, D7, D14, D30, D60, D90
3. Plot the curve for each cohort

**Interpretation:**

| Curve Shape | What It Means |
|-------------|--------------|
| Drops to zero | No PMF. Product doesn't solve a recurring problem. |
| Drops and keeps dropping | Weak PMF. Some people find value, but not enough to keep coming back. |
| Drops then flattens above 0 | PMF signal. A core group finds ongoing value. |
| Flattens higher with each newer cohort | PMF improving. You're learning. |

**Benchmarks:**

| Segment | D30 Retention (PMF threshold) | D90 Retention (strong PMF) |
|---------|-------------------------------|---------------------------|
| Consumer | > 20% | > 10% |
| SMB SaaS | > 40% | > 25% |
| Enterprise SaaS | > 60% | > 45% |
| Marketplace (buyers) | > 30% | > 20% |
| PLG (free-to-paid) | > 25% free D30, > 50% paid D30 | > 15% free D90 |

**If retention is below threshold:**
- Don't run more acquisition. You'll just churn faster.
- Find the users who ARE retained. Understand why. Build for them.

---

### Signal 2: Sean Ellis Test

Survey users with one question: "How would you feel if you could no longer use [Product]?"

**Answers:**
- Very disappointed
- Somewhat disappointed
- Not disappointed (it really isn't that useful)
- N/A — I no longer use [Product]

**Scoring:**
- Count only "very disappointed" responses
- Divide by total non-churned respondents
- PMF threshold: **> 40% "very disappointed"**

**Sample size requirement:** Minimum 40 responses. Under 40, the signal is noisy.

**When to run it:**
- When you have 100-500 active users
- Quarterly for ongoing tracking
- After major product changes

**What to do with "somewhat disappointed":**
Don't lump them with "very disappointed." The delta between "somewhat" and "very" is where your retention problem lives. Interview people in the "somewhat" group. What's missing? Why only somewhat?

**When score is 20-35%:** You have a segment with PMF. Find them. Ask what they love. Run a separate survey for just that segment.

**When score is < 20%:** Your core value proposition isn't working. This is not a retention tactics problem. Revisit the fundamental problem you're solving.

---

### Signal 3: Organic Growth and Referral

**Metric:** % of new signups that came from existing user referral, word of mouth, or organic search — without a paid incentive.

**Threshold:** > 20% of new users are coming organically without incentive programs.

**How to measure:**
1. Tag signup source: paid, organic search, referral (with referral code), direct/dark social
2. Track monthly. Is the organic % trending up or stable?
3. Interview organic signups: "How did you hear about us?" (don't trust the dropdown)

**Why this matters:** Paid growth can mask the absence of PMF. You can buy users who churn. You can't buy users who tell their friends.

---

## Step 3: Run PMF Experiments (Pre-PMF)

If you're below thresholds, don't optimize — experiment. The goal is to find the version of the product where at least a small segment has PMF.

### The PMF Experiment Loop

```
1. Pick one customer segment + one hypothesis about their job to be done
2. Remove everything from the product that doesn't serve that job
3. Run a 4-week cohort with only that segment
4. Measure retention + Sean Ellis for that cohort
5. If PMF signal: this is your beachhead. Double down.
   If no signal: new hypothesis. Repeat.
```

**Time box:** Each experiment 4-8 weeks. If you're running experiments for 18+ months with no signal, revisit the problem space, not just the solution.

### What to Change

| Lever | Change | Expected Impact |
|-------|--------|-----------------|
| Target segment | Narrow ICP from "all companies" to "Series A SaaS" | Faster learning, higher retention |
| Core job | Reframe from feature-benefit to outcome-benefit | Better product decisions |
| Onboarding | Remove steps to time-to-value | D1 retention up |
| Pricing | Move from per-seat to per-outcome | Align incentives with value |
| Channel | Switch from outbound to PLG | Different segment discovers product |

---

## Step 4: Validate PMF (Post-Signal, Pre-Scale)

Congratulations, you have a retention curve that flattens. Before you scale:

**Validate that it's real:**
- Can you acquire more of the same customers? (Test CAC at 2x current volume)
- Do the retained users expand? (Are they buying more seats, upgrading?)
- Is the NPS from retained users > 40?
- Are they forgiving of bugs and slowness? (Love, not tolerance)

**Validate the unit economics:**
- LTV / CAC > 3x (for SaaS)
- Payback period < 18 months
- Gross margin > 60% (SaaS), > 40% (marketplace)

**The danger zone:** Convincing yourself you have PMF before economics are viable. High retention with terrible unit economics is not a business — it's a hobby that grows.

---

## PMF by Business Model

### B2B SaaS

**Primary signal:** D90 retention > 45% in target segment.

**Secondary signals:**
- NPS from retained users > 50
- Expansion revenue from retained accounts (NRR > 110%)
- Sales cycle shortening as word-of-mouth increases

**PMF finding strategy:**
- Start with one vertical, not the whole market
- Get 3-5 reference customers who use it daily and refer others
- Don't expand segment until you can replicate the reference case

**Common false signals:**
- Retained users who are locked in by contract, not value
- Expansion revenue from upselling, not from organic growth
- High satisfaction survey scores with flat usage data

---

### B2C / Consumer

**Primary signal:** D30 retention > 20%, with a flat or rising tail at D90.

**Secondary signals:**
- DAU/MAU ratio > 20% (daily habit product: > 40%)
- Session depth (users exploring multiple features, not one-and-done)
- Organic referral rate > 20% of new installs

**PMF finding strategy:**
- Consumer PMF is about habit formation — which behavior do you own in a user's day?
- Find the "aha moment" (the action that predicts retention). Build everything to get users there faster.
- Segment ruthlessly — consumer PMF is often strong in one demographic, weak in others.

**Common false signals:**
- High D1 retention from email campaigns that re-engage dormant users
- Good NPS from vocal users who are power users, not typical users
- Media buzz driving installs from wrong audience

---

### Marketplace

**Primary signal:** Successful transaction rate and repeat buyer rate.

**Secondary signals:**
- Supply-side retention (sellers/providers coming back)
- Liquidity score: % of demand requests matched within acceptable time
- Referral: both sides sending others

**PMF challenge:** You have two customers (supply and demand). PMF can exist on one side and not the other.

**PMF finding strategy:**
- Start with constrained geography or category — don't try to be national before local works
- Measure GMV per cohort, not just transaction count
- Find the "magic moment" for both buyer and seller. Optimize for both.

---

### PLG (Product-Led Growth)

**Primary signal:** Free-to-paid conversion rate + paid retention.

**Secondary signals:**
- Time to activation (reaching the "aha moment" in free tier)
- PQL (product-qualified lead) conversion to paid
- Team invites from individual users (virality coefficient)

**PMF finding strategy:**
- The free tier must have genuine value — not a crippled trial
- Track activation milestone (the action that predicts conversion)
- Optimize activation before conversion — conversion optimizations don't work if nobody activates

---

## After PMF: The Scaling Trap

Most companies that fail after PMF weren't ready to scale. They scaled the wrong thing.

### The Scaling Trap

You have PMF with segment A. You hire sales and start selling to segment B. Segment B doesn't retain. NPS drops. Engineers chase segment B feature requests. Segment A users feel abandoned.

**This is the most common way early-stage companies die after PMF.**

### What to Do After PMF

**First 90 days after confirming PMF:**
1. Document your best customer profile in extreme detail
2. Build the playbook to replicate the reference customer, not to expand the ICP
3. Hire sales to replicate, not to expand
4. Instrument everything — you need to know what's driving retention for every new cohort
5. Don't launch new features. Remove friction from the path that's already working.

**The expansion question:** Only expand ICP when:
- You can replicate the reference customer at 3x volume with same retention
- CAC is declining (word of mouth in the reference segment)
- You've exhausted density in the reference segment

**Don't expand ICP to save the business.** Expanding ICP when retention is declining is panic, not strategy.

---

## How to Know When PMF Is Slipping

PMF is not a binary state. It can degrade. Watch for:

| Signal | What's Happening | Response |
|--------|-----------------|----------|
| D30 retention declining across cohorts | Product changes or market change are eroding value | Run Sean Ellis test immediately. Interview churned users. |
| Sean Ellis score dropping | Users less passionate about the product | Feature gap opening. Competitive pressure. |
| NPS dropping for retained users | Power users seeing degraded experience | Product quality or performance issues. |
| Organic referral rate declining | Satisfied users less enthusiastic | Product becoming commoditized. Moat eroding. |
| Support tickets shifting from feature requests to bug reports | Technical debt catching up | Engineering quality investment needed. |
| Sales cycles lengthening | ICP no longer self-evident. Positioning drift. | Re-run positioning exercise. Sharpen ICP. |

**The PMF quarterly check:**
Run Sean Ellis test every quarter. Track D30 retention by cohort every month. Put both on the CPO dashboard. These are your vital signs.

---

## Quick Reference

| Test | Threshold | Frequency |
|------|-----------|-----------|
| Sean Ellis | > 40% very disappointed | Quarterly |
| D30 retention (B2B SaaS) | > 40% | Monthly (by cohort) |
| D30 retention (consumer) | > 20% | Monthly (by cohort) |
| D90 retention (B2B SaaS) | > 45% | Monthly (by cohort) |
| Organic signup % | > 20% | Monthly |
| NPS (retained users) | > 40 | Quarterly |
| DAU/MAU (if daily product) | > 20% | Weekly |

Use `scripts/pmf_scorer.py` to run all dimensions together with weighted scoring.
