# CRO — Conversion Rate Optimization Guide

## What is CRO?

CRO = increasing the percentage of visitors who take a desired action (sign up, buy, book, download).

**Formula:** Conversions ÷ Visitors × 100 = Conversion Rate

Even small improvements compound:
- 10,000 visitors/mo × 2% CVR = 200 conversions
- 10,000 visitors/mo × 3% CVR = 300 conversions (+50% revenue, same traffic)

---

## CRO by Page Type

### Landing Pages (`page-cro`)

**Above the fold:**
- H1 = clear value proposition (what + who + why)
- Subheadline = support the claim with specifics
- CTA = one primary action, action-oriented copy ("Start free trial" not "Submit")
- Hero image = show outcome, not product feature
- Social proof = number of users, recognizable logos

**Trust signals:**
- Money-back guarantee
- Security badges (SSL, SOC2, etc.)
- Review stars + count (G2, Trustpilot, Capterra)
- Named customer testimonials with photo + title

**Friction reducers:**
- No credit card required
- Takes X minutes
- Cancel anytime
- Free forever tier (if applicable)

**CTA best practices:**
- One primary CTA per section (not 3 competing buttons)
- Repeat CTA at top + bottom
- Button color: high contrast to background
- CTA copy: specific ("Get my free audit") beats generic ("Get started")

---

### Signup / Registration Flows (`signup-flow-cro`)

**Reduce fields:**
- Only ask what you need to activate the user
- Delay optional fields (phone, company size) until onboarding
- Use social login (Google, GitHub) to eliminate form entirely

**Progress indication:**
- Show steps: "Step 2 of 3"
- Progress bar for multi-step flows
- "Almost there!" copy at final step

**Inline validation:**
- Show errors as user types, not after submit
- Green checkmark when field is valid
- Helpful error messages ("Password must be 8+ characters" not "Invalid")

**Micro-copy:**
- Below email field: "No spam, unsubscribe anytime"
- Below password: "We'll never share your password"
- CTA button: match to value ("Create my account" not "Submit")

---

### Onboarding Flows (`onboarding-cro`)

**Goal:** Get user to first "aha moment" as fast as possible

**First session checklist:**
- Welcome screen: confirm what they signed up for
- One key action (not 5 choices) — guide to highest-value feature
- Empty states: show what the product looks like with data (demo mode)
- Progress checklist: "Complete your profile" gamifies setup

**Activation triggers:**
- Define your activation event (user has connected X, created Y, invited Z)
- Every onboarding step should move toward activation
- Email sequences timed to steps, not just days

---

### Pricing Pages (`paywall-upgrade-cro`)

**Pricing page structure:**
1. Short headline → reinforce value, not just price
2. Plan comparison: 3 tiers is the sweet spot (anchoring effect)
3. Highlight recommended plan (most common choice + highest margin)
4. Annual vs monthly toggle (show savings: "Save 20%")
5. Feature comparison table below the fold
6. FAQ section (handle objections: cancellation, data, limits)
7. Social proof: logos, testimonials specific to upgrade

**Psychological principles:**
- Decoy pricing: middle plan makes top plan look reasonable
- Loss framing: "You're missing out on X" vs "Get X"
- Urgency: limited-time offer, seats remaining (only if real)

---

### Forms (`form-cro`)

**General rules:**
- One column layout outperforms two columns
- Labels above fields (not inside/placeholder-only)
- Logical field order (matches mental model)
- Auto-focus first field on load
- Submit button = descriptive ("Send my quote" not "Submit")

**Multi-step forms:**
- Start with easiest/least personal questions
- End with contact info (commitment/consistency principle)
- Show progress indicator
- Allow back navigation

---

### Popups (`popup-cro`)

**When to show:**
- Exit intent: triggers when cursor moves to close tab
- Time delay: 30–60 seconds after page load (not immediate)
- Scroll depth: after 50–70% scroll
- Specific pages: high-intent pages only

**What works:**
- Specific offer (10% off, free checklist, exclusive content)
- Minimal fields (email only)
- Clear close button (don't hide it — frustration = bounce)
- Mobile: full-screen or bottom sheet, not centered modal

**What doesn't:**
- Popups on arrival (too early, high bounce)
- Multiple popups per session
- Vague CTAs ("Subscribe to our newsletter")
- No obvious way to close

---

## A/B Testing Framework (`ab-test-setup`)

### Test Prioritization (PIE Framework)
Score each test idea 1–10 on:
- **P**otential: how much could it improve?
- **I**mportance: how much traffic/revenue does this page get?
- **E**ase: how hard is it to implement?

Run highest PIE-score tests first.

### Statistical Significance
- Minimum sample: 1,000 visitors per variant
- Minimum duration: 2 weeks (captures weekly patterns)
- Significance threshold: 95% confidence before declaring winner
- Don't stop early (peeking problem)

### What to Test (Highest Impact First)
1. Headline / value proposition
2. CTA copy + color
3. Hero image / video
4. Pricing display
5. Social proof placement
6. Form length
7. Button placement
8. Page layout / sections

### Tools Integration
- Use **Google Analytics** goals to track conversions
- Connect to Semrush for traffic context
- Segment by: traffic source, device, new vs returning

---

## Analytics Tracking Setup (`analytics-tracking`)

### Events to Track (Minimum)
```
Page view → Goal: every page
CTA click → Goal: primary + secondary CTAs
Form start → Goal: funnel entry
Form submit → Goal: conversion
Sign up → Goal: activation
Purchase → Goal: revenue (with value)
Error → Event: form errors, 404s
```

### Funnel Tracking
Map your conversion funnel and track each step:
```
Landing → [Drop %] → Pricing → [Drop %] → Signup → [Drop %] → Activation
```

Drop rates by step reveal exactly where to focus CRO efforts.

### UTM Parameter Standards
Always tag your campaigns:
```
utm_source=google
utm_medium=cpc
utm_campaign=brand-keywords
utm_content=headline-v2
utm_term=semrush+review
```

---

## Free Tool Strategy (`free-tool-strategy`)

Free tools are one of the highest-ROI SEO + CRO strategies:

**Why they work:**
- Attract backlinks naturally (tools get cited/shared)
- Capture leads in exchange for results
- Demonstrate product value before purchase
- Target high-intent keywords ("free X calculator", "free X checker")

**Examples that work:**
- Calculators (ROI, pricing, savings)
- Graders / auditors (website score, ad score)
- Generators (headline generator, meta description generator)
- Converters (file converters, unit converters)
- Templates (downloadable in exchange for email)

**CRO of free tools:**
1. Results screen = upgrade prompt (show what paid unlocks)
2. Email gate for full results
3. Save/share results functionality (virality)
4. "What to do next" section → drives to product

---

## Churn Prevention (`churn-prevention`)

**Churn indicators to monitor:**
- Login frequency drop
- Feature usage decline
- Support ticket increase
- Billing page visits without upgrade

**Retention triggers:**
- Day 3 / Day 7 / Day 14 / Day 30 email sequences
- In-app prompts when usage drops
- Personalized "here's what you haven't tried" nudges
- Success milestones: celebrate when user hits value moments

**At-risk user playbook:**
1. Detect: usage < X days in past 14
2. Trigger: personalized email with tips
3. Offer: extend trial, free call, discount
4. Escalate: account manager outreach for high-value accounts
