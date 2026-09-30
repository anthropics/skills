# Phase 3 — Prototype Feasibility

## Goal
Define the smallest possible thing that tests the riskiest assumption — before writing
production code. The output is a **fake-door or paper prototype plan**, not actual code.

---

## 3.1 Identify the Core Assumption to Test

Every idea has one assumption that, if wrong, kills everything.
Pick the single most important one to test first:

Examples:
- "Users will trust AI-generated prep plans" (trust assumption)
- "People will pay $29/mo for this" (monetization assumption)
- "The UX flow makes sense to a new user in < 60 seconds" (usability assumption)
- "Users have this problem frequently enough to return" (retention assumption)

State this explicitly:
```
Core Assumption: [one sentence]
Test Method: [how the prototype proves/disproves it]
```

---

## 3.2 Prototype Options (pick the right level)

Choose based on what assumption is being tested:

### Level 1 — Static Landing Page (1–3 hours)
- One-page site with value prop, feature list, pricing, CTA ("Join waitlist" / "Get early access")
- Test: **demand** — will people click and give their email?
- Build with: Claude Artifact (HTML), Carrd, Framer, or a simple React component
- Success metric: >5% conversion on cold traffic, or 20+ signups from personal network

### Level 2 — Clickable UI Mock (4–8 hours)
- Claude Artifact (React) showing the core user flow with fake/hardcoded data
- Test: **UX clarity** — does the flow make sense without explanation?
- Include: The single most important screen (dashboard, results page, wizard step)
- Success metric: A new user can describe what the product does in 30 seconds without prompting

### Level 3 — Wizard of Oz (1–2 days)
- Real UI, but Claude (or a human) does the work behind the scenes manually
- Test: **value quality** — is the output actually useful enough to pay for?
- Build with: Claude API-powered artifact, or just do it manually via chat
- Success metric: User says "I'd pay for this" or "This saved me X hours"

### Level 4 — Spike / Technical Prototype (2–5 days)
- Build only the hardest technical piece — not the full product
- Test: **feasibility** — can this actually be built to the required quality?
- See Phase 4 for guidance on what to spike

---

## 3.3 Fake-Door Test Plan

Define concretely:
- **What page/flow to build**
- **Where to send traffic** (Twitter/X, Reddit, a community, personal network)
- **The CTA** — what the user clicks or submits
- **What you measure** in 48–72 hours
- **Pass threshold** — what result means "proceed to Phase 4"

Format:
```
Prototype Type: Level [1/2/3/4]
Build Time: ~X hours
Platform: [where you'd build it]
CTA: [exact button text or action]
Traffic Source: [where you'd send people]
Pass Condition: [specific measurable outcome]
```

---

## 3.4 What NOT to Build Yet

List 3–5 features the idea probably includes that should NOT be in the prototype:
- Auth / user accounts
- Persistent database
- Admin dashboard
- Billing / payments
- Onboarding flow

These are validated later. Prototyping them first is sunk cost.
