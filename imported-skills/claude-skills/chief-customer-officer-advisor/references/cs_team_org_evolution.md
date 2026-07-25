# CS Team Org Evolution — The Decision: "What CS role do we hire next, and how is CS different from Support / AM / IM?"

This reference answers exactly one decision: **for our stage and the customer outcomes we're failing to deliver, what is the next CS role to hire?**

## The Wrong Question

> "Should we hire a CSM or a Support engineer?"

This is the wrong question. Most CSMs and Support engineers hired at the wrong stage cannot deliver value because:
- The role they're hired into doesn't match the customer outcomes being missed
- The infrastructure (CRM, health scores, playbooks) isn't ready for them to be productive
- Founders confuse the four customer-facing roles and hire the wrong one

## The Right Question

> "What customer outcome are we failing to deliver, and which role unblocks that?"

This shifts hiring from role-taxonomy to outcome-shipping. CS org grows in response to specific failure modes.

## The Six Customer-Facing Roles (founders confuse these)

| Role | Owns | Does NOT own |
|---|---|---|
| **Customer Support** | Reactive issue resolution (ticket queue); product knowledge; first response | Renewal, expansion, strategic relationship, proactive outreach |
| **Customer Success Manager (CSM)** | Proactive value realization + renewal + expansion lead | Day-to-day support tickets, technical implementation |
| **Account Manager (AM)** | Commercial relationship + expansion close + contract negotiation | Day-to-day success, technical depth, ticket resolution |
| **Implementation Manager (IM)** | Onboarding + go-live + first-value delivery | Ongoing success after launch (hands off to CSM) |
| **CS Operations (CS Ops)** | Tooling, data, analytics, playbooks, health scores | Direct customer relationships |
| **Customer Marketing** | Advocacy, case studies, references, customer events | 1:1 customer relationships, renewal/expansion |

**The most common confusions:**
- **CSM = Support:** No. CSMs do proactive value realization. Support is reactive.
- **CSM = AM:** Some companies combine; risky. CSM lens is success outcomes; AM lens is commercial.
- **CSM = Implementation:** No. Implementation is launch-bounded; CSM is ongoing.

## The Five Stages

### Stage 1: Pre-PMF / Pre-seed / Seed
**Team size:** 1-15 people. **CS team:** 0 dedicated.

**Reality:** Founder does customer success. Every customer is hand-held by a co-founder. This is fine and even useful — customer obsession is the right founder behavior at this stage.

**Don't hire:** CSM, Support engineer, AM. Premature.

**Tooling:** Direct customer Slack channels, email, weekly founder check-ins. No CRM needed beyond a spreadsheet.

**When to move to stage 2:** Founder is spending >40% of week on customer issues AND has 10+ paying customers AND can articulate the post-sale playbook clearly.

### Stage 2: Series A
**Team size:** 15-50 people. **CS team:** 1-3.

**First hire: Customer Success Manager (NOT Support engineer first).**

Why: at this stage the biggest leakage is proactive value realization, not ticket volume. CSM handles onboarding, renewal preparation, expansion identification.

Profile:
- 3-5 years experience in B2B SaaS CS
- Strong product fluency (can demo and explain)
- Comfortable with ambiguity (playbooks don't exist yet — they'll build them)

**Second hire: Customer Support engineer / specialist.**

Why: once you have 30+ paying customers, ticket volume becomes real. Support handles the reactive load so CSMs can stay proactive.

Profile:
- Strong technical aptitude + customer empathy
- Comfortable with the product
- Documentation-oriented (will build the knowledge base)

**Third hire: Implementation specialist (often part-time / shared with CSM).**

Why: at higher ACVs, onboarding is its own discipline. Bad onboarding kills retention before the customer ever sees the product's value.

**Don't hire yet:** AM (CSM handles renewals), CS Ops (CSMs do their own ops), Customer Marketing.

**When to move to stage 3:** 100+ paying customers, $1M+ ARR, 3+ CSMs, segmentation tiers are real.

### Stage 3: Series B
**Team size:** 50-200. **CS team:** 4-10.

**Fourth hire: CS Manager (internal promotion).**

Why: 4+ CSMs need a manager. Original CSM lead should be promoted internally; external hires miss the playbook context.

**Fifth hire: CS Operations.**

Why: by Series B, CSMs are spending 30%+ of their time on tooling, reporting, and data work. CS Ops centralizes this; CSMs get their time back for customer-facing work.

Profile:
- Analytical (SQL + spreadsheets minimum; ideally light scripting)
- Has run CRM workflows (Gainsight, ChurnZero, Vitally, or even just Salesforce reports)
- Builds health scores, playbook automation, exec dashboards

**Sixth hire (conditional): Account Manager — separate from CSM.**

Trigger:
- CSMs are good at success but bad at commercial (renewals delayed, expansion under-closed)
- ACV justifies a dedicated commercial role (Enterprise+ segment)
- Multi-product company where cross-sell motion is distinct

Profile: closer / commercial DNA, NOT a success person. AM owns the contract; CSM owns the relationship and success outcomes.

**Seventh hire (conditional): Customer Marketing.**

Trigger:
- 5+ public reference customers
- Conference / event presence needed
- Advocacy is a strategic priority

**When to move to stage 4:** 250+ customers, $5M+ ARR, multiple segment tiers, CS team is 8+ people.

### Stage 4: Growth (Series C / pre-IPO)
**Team size:** 200-1000. **CS team:** 10-50.

**Director / VP CS.**

Triggers:
- CS team is 10+
- CS is a board-level conversation (NRR is in the company narrative)
- CS strategy needs an executive who isn't the founder

Profile: has run CS org at $20M+ ARR, scaled CS through hyper-growth, has comp + ladder + comp-plan design experience.

**Tier-specific specialization:**

By this stage, CSM roles should specialize:
- Strategic CSM: senior, multi-account, executive-facing
- Enterprise CSM: standard CSM career path
- Mid-market CSM: pooled coverage, automation-heavy
- SMB / tech-touch lead: 1 CSM owns the entire long-tail

**Implementation team scaled separately:** dedicated Implementation Managers for Strategic + Enterprise, hand-offs to CSMs at go-live.

**Add: Renewals team (optional but common at growth stage).**

Trigger: CSMs are losing focus on success outcomes because renewal-cycle work consumes them. Dedicated Renewals team takes contract management; CSMs stay on success.

### Stage 5: Late-stage (Series D+, post-IPO)
**Team size:** 1000+. **CS team:** 50-300+.

**CCO promotion or hire.**

Triggers:
- CS is in the company strategic narrative
- Customer experience as a whole (CS + Support + Marketing + Product feedback loops) needs a single leader
- Multi-product portfolio needs unified customer view

CCO profile:
- Has run CS / CX at scale ($100M+ ARR)
- Strong on cross-functional (product, marketing, sales) collaboration
- Comfortable with board-level reporting on retention

**Customer Operations (CustOps) as a unified function.**

Combines: CS Ops + Support Ops + Customer Marketing Ops + Customer Data infra. Centralized, serves all customer-facing teams.

**Federated CSM model.**

CSMs embed in product lines / verticals / geographies. Central CS function provides playbooks + tooling + governance; embedded CSMs deliver day-to-day.

## The AM vs CSM Split Decision

The single most-debated CS org question.

**When to split (separate AM and CSM):**
- ACV $20K+ (Enterprise+)
- CSMs hate commercial work and are losing renewals
- Multi-product cross-sell motion is distinct from success outcomes
- Sales-led GTM model (AM is a natural extension of the AE)

**When NOT to split (CSM owns commercial):**
- Mid-market and below
- PLG / self-serve motion
- Small CS team where context-switching cost is low
- Founder still close enough to deals

**The hybrid (most common):**
- CSM owns relationship + renewal
- AM exists ONLY for expansion close (when complex commercial work justifies a closer)
- AM commission split between CSM (who identified) and AM (who closed)

## Anti-Patterns

- **Hiring Support as the first CS hire.** Support solves a problem you may not yet have at sub-50 customers; CSM solves a problem you have at day one (proactive value).
- **Hiring CS Ops before CSMs.** Premature; nothing to operate. CS Ops emerges from the friction CSMs experience.
- **Promoting the top CSM to manager without training.** Best ICs often fail as managers; provide management training or external hire.
- **CSM + AM combined indefinitely.** Works at sub-$5M ARR; breaks above. Plan the split before it becomes a crisis.
- **CSM = "Support Plus."** Tickets routed to CSMs because "they know the customer best" destroys CSM proactive time. Strict ticket routing to Support.
- **Treating Customer Marketing as a CS extension.** Different discipline; reports up through Marketing, not CS, in most healthy orgs.
- **Hiring a CCO at sub-$10M ARR.** Political role; nothing to operate. Wait until the function justifies an executive.

## The Hiring Sequencing Rule

Never hire the next CS role until:
1. The current role is filled and ramped (3-6 months in seat)
2. That role has shipped a specific customer outcome
3. You can name the gap the next hire will fill

**The discipline:** every CS hire ties to a specific customer outcome the business is currently failing to deliver.

## When This Reference Doesn't Help

- **Comp benchmarking for specific roles.** See `c-level-advisor/skills/chro-advisor/scripts/comp_benchmarker.py`.
- **Leveling ladders.** See `c-level-advisor/skills/chro-advisor/references/leveling_ladders.md`.
- **CS Ops tooling selection (Gainsight, ChurnZero, Vitally, etc.).** Tactical; not strategic.
- **Performance management.** Standard people management.

This reference is about strategic CS team evolution as a function of customer outcomes, not HR mechanics.

---

**Source observations (non-exhaustive):**

- Nick Mehta, Dan Steinman, Lincoln Murphy — "Customer Success" (Wiley, 2016)
- Nick Mehta, Allison Pickens — "The Customer Success Economy" (Wiley, 2020) — chapters on org evolution
- Bessemer Venture Partners — "State of the Cloud" annual report (CS-as-% of revenue benchmarks)
- TSIA — annual CS benchmarks including org structure across SaaS stages
- Gainsight — Pulse conference talks on org maturity
- Direct observations from 30+ B2B SaaS CS org evolutions, 2018-2026
- ChurnZero — annual CS salary + ratio surveys
- Lincoln Murphy — extensive blog writing on AM vs CSM split
