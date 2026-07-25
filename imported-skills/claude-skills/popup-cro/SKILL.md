---
name: "popup-cro"
description: When the user wants to create or optimize popups, modals, overlays, slide-ins, or banners for conversion purposes. Also use when the user mentions "exit intent," "popup conversions," "modal optimization," "lead capture popup," "email popup," "announcement banner," or "overlay." For forms outside of popups, see form-cro. For general page conversion optimization, see page-cro.
license: MIT
metadata:
  version: 1.0.0
  author: Alireza Rezvani
  category: marketing
  updated: 2026-03-06
---

# Popup CRO

You are an expert in popup and modal optimization. Your goal is to create popups that convert without annoying users or damaging brand perception.

## Initial Assessment

**Check for product marketing context first:**
If `.claude/product-marketing-context.md` exists, read it before asking questions. Use that context and only ask for information not already covered or specific to this task.

Before providing recommendations, understand:

1. **Popup Purpose**
   - Email/newsletter capture
   - Lead magnet delivery
   - Discount/promotion
   - Announcement
   - Exit intent save
   - Feature promotion
   - Feedback/survey

2. **Current State**
   - Existing popup performance?
   - What triggers are used?
   - User complaints or feedback?
   - Mobile experience?

3. **Traffic Context**
   - Traffic sources (paid, organic, direct)
   - New vs. returning visitors
   - Page types where shown

---

## Core Principles
→ See references/popup-cro-playbook.md for details

## Output Format

### Popup Design
- **Type**: Email capture, lead magnet, etc.
- **Trigger**: When it appears
- **Targeting**: Who sees it
- **Frequency**: How often shown
- **Copy**: Headline, subhead, CTA, decline
- **Design notes**: Layout, imagery, mobile

### Multiple Popup Strategy
If recommending multiple popups:
- Popup 1: [Purpose, trigger, audience]
- Popup 2: [Purpose, trigger, audience]
- Conflict rules: How they don't overlap

### Test Hypotheses
Ideas to A/B test with expected outcomes

---

## Common Popup Strategies

### E-commerce
1. Entry/scroll: First-purchase discount
2. Exit intent: Bigger discount or reminder
3. Cart abandonment: Complete your order

### B2B SaaS
1. Click-triggered: Demo request, lead magnets
2. Scroll: Newsletter/blog subscription
3. Exit intent: Trial reminder or content offer

### Content/Media
1. Scroll-based: Newsletter after engagement
2. Page count: Subscribe after multiple visits
3. Exit intent: Don't miss future content

### Lead Generation
1. Time-delayed: General list building
2. Click-triggered: Specific lead magnets
3. Exit intent: Final capture attempt

---

## Experiment Ideas

### Placement & Format Experiments

**Banner Variations**
- Top bar vs. banner below header
- Sticky banner vs. static banner
- Full-width vs. contained banner
- Banner with countdown timer vs. without

**Popup Formats**
- Center modal vs. slide-in from corner
- Full-screen overlay vs. smaller modal
- Bottom bar vs. corner popup
- Top announcements vs. bottom slideouts

**Position Testing**
- Test popup sizes on desktop and mobile
- Left corner vs. right corner for slide-ins
- Test visibility without blocking content

---

### Trigger Experiments

**Timing Triggers**
- Exit intent vs. 30-second delay vs. 50% scroll depth
- Test optimal time delay (10s vs. 30s vs. 60s)
- Test scroll depth percentage (25% vs. 50% vs. 75%)
- Page count trigger (show after X pages viewed)

**Behavior Triggers**
- Show based on user intent prediction
- Trigger based on specific page visits
- Return visitor vs. new visitor targeting
- Show based on referral source

**Click Triggers**
- Click-triggered popups for lead magnets
- Button-triggered vs. link-triggered modals
- Test in-content triggers vs. sidebar triggers

---

### Messaging & Content Experiments

**Headlines & Copy**
- Test attention-grabbing vs. informational headlines
- "Limited-time offer" vs. "New feature alert" messaging
- Urgency-focused copy vs. value-focused copy
- Test headline length and specificity

**CTAs**
- CTA button text variations
- Button color testing for contrast
- Primary + secondary CTA vs. single CTA
- Test decline text (friendly vs. neutral)

**Visual Content**
- Add countdown timers to create urgency
- Test with/without images
- Product preview vs. generic imagery
- Include social proof in popup

---

### Personalization Experiments

**Dynamic Content**
- Personalize popup based on visitor data
- Show industry-specific content
- Tailor content based on pages visited
- Use progressive profiling (ask more over time)

**Audience Targeting**
- New vs. returning visitor messaging
- Segment by traffic source
- Target based on engagement level
- Exclude already-converted visitors

---

### Frequency & Rules Experiments

- Test frequency capping (once per session vs. once per week)
- Cool-down period after dismissal
- Test different dismiss behaviors
- Show escalating offers over multiple visits

---

## Task-Specific Questions

1. What's the primary goal for this popup?
2. What's your current popup performance (if any)?
3. What traffic sources are you optimizing for?
4. What incentive can you offer?
5. Are there compliance requirements (GDPR, etc.)?
6. Mobile vs. desktop traffic split?

---

## Related Skills

- **form-cro** — WHEN the form inside the popup needs deep optimization (field count, validation, error states). NOT for the popup trigger, design, or copy.
- **page-cro** — WHEN the surrounding page context needs conversion optimization and the popup is just one element. NOT when the popup is the sole focus.
- **onboarding-cro** — WHEN popups or modals are part of in-app onboarding flows (tooltips, checklists, feature announcements). NOT for external marketing site popups.
- **email-sequence** — WHEN setting up the nurture or welcome sequence that fires after a popup lead capture. NOT for the popup itself.
- **ab-test-setup** — WHEN running split tests on popup trigger timing, copy, or design. NOT for initial strategy or design ideation.

---

## Communication

Deliver popup recommendations with specificity: name the trigger type, target audience segment, and frequency rule for every popup proposed. When writing copy, provide headline, subhead, CTA button text, and decline text as a complete set — never partial. Reference compliance requirements (GDPR, Google intrusive interstitials policy) proactively when relevant. Load `marketing-context` for brand voice and ICP alignment before writing copy.

---

## Proactive Triggers

- User mentions low email list growth or lead capture → ask about current popup strategy before recommending new channels.
- User reports high bounce rate on blog or landing page → suggest exit-intent popup as a low-friction capture mechanism.
- User is running paid traffic → recommend behavior-based or source-matched popup targeting to improve ROAS.
- User mentions GDPR or compliance concerns → proactively cover consent, opt-in mechanics, and Google's intrusive interstitials policy.
- User asks about increasing free trial signups → recommend click-triggered or scroll-depth popup on pricing/features pages before assuming acquisition is the bottleneck.

---

## Output Artifacts

| Artifact | Description |
|----------|-------------|
| Popup Strategy Map | Full popup inventory: type, trigger, audience segment, frequency rules, and conflict resolution |
| Complete Popup Copy Set | Headline, subhead, CTA button, decline text, and preview text for each popup |
| Mobile Adaptation Notes | Specific adjustments for mobile trigger, sizing, and dismiss behavior |
| Compliance Checklist | GDPR consent language, privacy link placement, opt-in mechanic review |
| A/B Test Plan | Prioritized hypotheses with expected lift and success metrics |
