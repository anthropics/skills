# Sales Playbook

Frameworks for building, running, and scaling a B2B SaaS sales organization.

---

## Sales Process Design

A sales process is a repeatable series of steps that takes a prospect from first contact to closed revenue. Without it, you have individual heroics, not a scalable machine.

### The Core Funnel

```
Lead Generation → Qualification → Discovery → Demo → Trial / POC → Proposal → Negotiation → Close → Handoff
```

Each stage has a clear entry criterion, exit criterion, and owner.

### Stage Definitions

#### Stage 0: Lead / Suspect
- **Entry:** Contact exists in CRM with basic firmographic data
- **Owner:** Marketing or SDR
- **Exit criterion:** Meets ICP criteria (company size, industry, tech stack)
- **Action:** Research, prioritize, add to outbound sequence

#### Stage 1: Prospecting / Outreach
- **Entry:** ICP-qualified account, no contact yet
- **Owner:** SDR or AE (depending on model)
- **Exit criterion:** Meeting booked with a qualified contact
- **Action:** Multi-channel outreach (email + call + LinkedIn), 8-12 touch sequence
- **Key metric:** Meeting booked rate (benchmark: 2-5% of outbound contacts)

#### Stage 2: Discovery
- **Entry:** First meeting confirmed
- **Owner:** AE (SDR hands off or joins)
- **Exit criterion:** Confirmed: pain, budget range, decision process, timeline
- **Action:** Ask questions. Listen. Map the org. Don't pitch yet.
- **Key metric:** Discovery-to-demo rate (benchmark: 60-80% proceed)

**Discovery question framework:**
```
Situation:    "How do you currently handle [problem area]?"
Problem:      "What's the impact when [pain point] happens?"
Implication:  "If this continues, what does that mean for [business goal]?"
Need-payoff:  "If we solved this, what would that be worth to you?"
```

#### Stage 3: Demo / Solution Presentation
- **Entry:** Confirmed pain and fit from discovery
- **Owner:** AE (+ SE for complex products)
- **Exit criterion:** Prospect agrees to evaluate / trial; next step defined
- **Action:** Show the workflow that solves their specific pain (not a feature tour)
- **Key metric:** Demo-to-trial/proposal rate (benchmark: 40-60%)

**Demo structure:**
1. Recap their pain (show you listened) — 5 min
2. Show the "aha moment" (fastest path to value) — 10 min
3. Walk the specific workflow they described — 15 min
4. Handle objections, confirm fit — 5 min
5. Define clear next step (date, owners, criteria) — 5 min

Never show features they didn't ask for. Every additional feature is noise until they have a reason to care.

#### Stage 4: Trial / POC
- **Entry:** Prospect commits to evaluate with real data/use case
- **Owner:** AE + CSM or SE
- **Exit criterion:** Success criteria met, POC success confirmed
- **Action:** Define success criteria upfront (in writing). Set a tight timeframe (2-4 weeks max).
- **Key metric:** POC-to-proposal rate (benchmark: 50-70%)

**POC setup requirements:**
```
Before any POC:
  □ Signed NDA
  □ Written success criteria ("We'll move forward if X happens")
  □ Named champion who owns the evaluation
  □ Executive sponsor identified
  □ Defined timeline with end date
  □ Agreed next step if criteria are met
```

If you can't get written success criteria, you don't have a real opportunity. You have a "we'll see."

#### Stage 5: Proposal / Pricing
- **Entry:** POC success OR strong discovery fit for simple products
- **Owner:** AE
- **Exit criterion:** Proposal received, timeline to decision confirmed
- **Action:** Present in a live call, never email a proposal cold
- **Key metric:** Proposal-to-negotiation rate (benchmark: 50-75%)

**Proposal structure:**
1. Problem statement (their words, not yours)
2. Proposed solution (mapped to their workflow)
3. ROI summary (value delivered vs. investment)
4. Pricing options (give 2-3 options; anchors the decision)
5. Next steps with dates

#### Stage 6: Negotiation
- **Entry:** Verbal intent to proceed, price/terms discussion begins
- **Owner:** AE (+ VP Sales for large deals)
- **Exit criterion:** Mutual agreement on terms; contract sent
- **Action:** Never discount before they ask. Discount on scope, not on margin.
- **Key metric:** Negotiation win rate (benchmark: 70-85%)

**Negotiation principles:**
- Get something for everything you give. Discount → multi-year. Fast close → early pay discount.
- Don't negotiate against yourself. Silence after an offer is not rejection.
- Know your walk-away before you enter. If you don't have a BATNA, you have no leverage.
- Legal/procurement delay ≠ deal death. Keep the champion engaged.

#### Stage 7: Close
- **Entry:** Signed contract or PO received
- **Owner:** AE
- **Exit criterion:** Contract countersigned, kickoff date set
- **Action:** Celebrate with the customer. Immediately introduce CSM.
- **Key metric:** Average close rate (closed won ÷ all closed = won + lost)

#### Stage 8: Handoff to Customer Success
- **Entry:** Deal closed
- **Owner:** AE + CSM
- **Exit criterion:** Customer has met their assigned CSM, kickoff scheduled
- **Action:** Internal handoff call with AE + CSM. AE shares: deal context, key stakeholders, use case, success criteria, any promises made during the sale.

**Handoff document (AE fills before first CS meeting):**
```
Account: [name]
ACV: $X
Close date: [date]
Primary contact: [name, title, email]
Economic buyer: [name, title]
Use case: [specific workflow]
Success criteria: [what they said good looks like in 90 days]
Promises made: [anything specific committed during sale]
Risk flags: [competitive, budget, champion strength]
```

---

## MEDDPICC Qualification Framework

MEDDPICC is the enterprise qualification standard. If you can't answer every letter, you don't have a qualified opportunity — you have a conversation.

### M — Metrics
What is the quantified business impact? What does winning look like in numbers?

- "What's the current cost of [the problem]?"
- "How do you measure success in this area today?"
- "If we achieve X outcome, what does that save or earn you?"

**Red flag:** No metrics = no business case = hard to get budget.

### E — Economic Buyer
Who has final authority to approve the budget?

- "Who else will be involved in the final decision?"
- "Have you purchased solutions in this range before? Who approved that?"
- "When we get to final terms, who needs to sign?"

**Red flag:** You only know the user buyer. Economic buyer hasn't engaged.

### D — Decision Criteria
What factors will they use to evaluate and select a solution?

- "What's most important in your evaluation?"
- "How will you compare options?"
- "What does the ideal solution look like to you?"

**Why it matters:** If you don't know their criteria, you're guessing what to prove. Define the criteria before you compete on them.

### D — Decision Process
What are the steps from evaluation to signed contract?

- "Walk me through your process from here to signed agreement."
- "Does procurement get involved? Legal? InfoSec?"
- "Have you purchased software at this price before? How long did that take?"

**Red flag:** No defined process = unlimited sales cycle.

### P — Paper Process
What's the contract and legal process?

- "Who manages vendor contracts on your side?"
- "What's your standard MSA, or do you use ours?"
- "How long does legal review typically take?"

**Why it matters:** Legal and procurement have killed many "done" deals. Start early. Route to your legal team simultaneously.

### I — Identify Pain
What is the specific, felt pain driving this evaluation?

- "What triggered this initiative now vs. six months ago?"
- "What happens if you don't solve this in Q3?"
- "On a scale of 1-10, how urgent is this for your team?"

**Red flag:** Pain isn't felt by the economic buyer. User pain ≠ budget authority.

### C — Champion
Who will actively sell your solution internally when you're not in the room?

- "Who else have you brought into this evaluation?"
- "Can you help us get access to [economic buyer / IT / security]?"
- "If the decision went the wrong way, who would be disappointed?"

**Red flag:** Your champion is enthusiastic but has no internal influence.

### C — Competition
Who else are they evaluating? What's your position?

- "Are you looking at alternatives?"
- "What made you start with us?"
- "Have you used [Competitor X] before?"

**Why it matters:** Knowing the competitive field tells you what you need to prove and what to neutralize.

### MEDDPICC Scorecard

| Letter | Score 1 | Score 2 | Score 3 |
|--------|---------|---------|---------|
| Metrics | No numbers | Approximate value | Specific ROI model |
| Economic Buyer | Unknown | Named, not engaged | Engaged directly |
| Decision Criteria | Vague | Partially defined | Written, weighted |
| Decision Process | Unknown | Verbal description | Steps confirmed, timeline known |
| Paper Process | Unknown | Basic awareness | Legal contacts, standard process known |
| Identify Pain | No urgency | User-level pain | Executive-level pain with consequences |
| Champion | No advocate | Friendly contact | Actively selling internally |
| Competition | Unknown | Identified | Position mapped, differentiation clear |

**Score each 1-3. Total 16+/24 = qualified opportunity. Under 12 = unqualified, do not forecast.**

---

## Sales Compensation Plans

Comp drives behavior. Design it precisely.

### Base / Variable Split

| Role | Base % | Variable % | Rationale |
|------|--------|-----------|-----------|
| SDR | 60-70% | 30-40% | Activity-based, not purely revenue |
| AE (Inside Sales) | 50% | 50% | Balanced risk/reward |
| AE (Enterprise) | 55-60% | 40-45% | Longer cycle, higher base for stability |
| VP Sales | 50% | 50% | Accountable for team results |
| CSM (retention focus) | 70% | 30% | Less variable, stable relationship role |
| CSM (expansion focus) | 60% | 40% | Expansion quota adds variable |

### Commission Structure

**Standard AE plan:**
```
Base: $80K
Variable: $80K (at 100% quota attainment)
OTE: $160K

Commission rate: OTE variable ÷ Quota
  If quota = $800K ARR: commission = $80K ÷ $800K = 10% of ARR closed

Accelerators (performance above quota):
  101-125% quota: 1.25x commission rate (12.5% of ARR)
  126-150% quota: 1.5x commission rate (15% of ARR)
  > 150% quota: 2.0x commission rate (20% of ARR)
```

**Why accelerators matter:**
- They keep top performers motivated past quota
- They make it possible for top reps to earn $200K+ (attracting talent)
- They create the "make it rain" culture

### SDR Compensation

SDRs are measured on output (meetings booked, pipeline created), not closed revenue.

```
Quota: 20 qualified meetings booked per month (or $X pipeline created)
Commission: $150-300 per qualified meeting held

Accelerators:
  If a meeting converts to closed won: Bonus $250-500
  If monthly meetings > 125% of quota: 1.5x rate on upside meetings
```

### Clawbacks

A clawback recovers commission paid on deals that churn or are fraudulently closed.

**Common clawback rules:**
- Full clawback if customer cancels within 90 days of close
- 50% clawback if customer cancels within 91-180 days
- No clawback after 180 days (AE shouldn't be penalized for future CS failures)
- Clawbacks vest: pay commission immediately but apply against next quarter's payout if triggered

**Why clawbacks matter:**
- Without them, reps are incentivized to close any deal, regardless of fit
- With them, reps self-qualify more carefully

### SPIFFs (Sales Performance Incentive Funds)

Short-term tactical incentives for specific behaviors:
- $5K bonus for closing a new vertical deal this quarter
- 1.5x commission on annual prepay deals in Q4
- $1K for closing a deal in a new geographic territory

Use SPIFFs sparingly. Overuse trains reps to wait for the SPIFF before engaging.

### Multi-Year and Prepay Incentives

Align rep behavior with company cash flow:
- Multi-year deals: Credit full TCV against quota, pay commission upfront on TCV
- Annual prepay: 10-20% uplift on commission rate
- Monthly billing: Standard commission rate

---

## Enterprise vs. SMB vs. Self-Serve Models

### Self-Serve / PLG

**Characteristics:**
- Product is the primary acquisition channel
- Credit card required (no invoicing)
- No human touch in the initial purchase
- Sales engages only at enterprise signals (high usage, team expansion, compliance needs)

**Funnel:**
```
Website → Free trial / Freemium → Activation → PQL → Expansion → Enterprise
```

**Key metrics:**
- Free-to-paid conversion rate (benchmark: 2-5% of signups)
- Time to activation (first core action)
- PQL → expansion conversion rate
- NRR from self-serve base

**Sales involvement triggers (PQL signals):**
- Team size > 10 seats
- Usage spikes (power user patterns)
- Feature limit hits on core features
- Job title change (new economic buyer appears in account)

### SMB Inside Sales

**Characteristics:**
- ACV $5K-25K
- 30-60 day sales cycle
- Inbound-heavy or light outbound
- SDR → AE → CS model
- Phone + email + video; no in-person

**Funnel:**
```
Inbound/MQL → SDR qualifies → AE discovery → Demo → Proposal → Close
```

**Key metrics:**
- MQL-to-SQL rate (benchmark: 15-25%)
- SQL-to-close rate (benchmark: 20-30%)
- Average sales cycle (30-60 days)
- AE productivity: $600K-$1M quota per rep

**Team ratios:**
- 1 SDR supports 3-4 AEs
- 1 CSM manages $1M-2M ARR

### Enterprise Sales

**Characteristics:**
- ACV $50K+
- 90-365 day sales cycle
- Outbound prospecting + inbound from brand
- AE + SE + executive sponsor model
- Multi-stakeholder: champion, economic buyer, IT, legal, procurement

**Funnel:**
```
Account targeting → Executive outreach → Discovery → POC → Security review → Legal → Procurement → Close
```

**Key metrics:**
- Deals in pipeline (volume matters less, quality more)
- POC win rate (benchmark: 60-75%)
- Average sales cycle (3-12 months)
- AE productivity: $1.5M-$3M quota per rep

**Team ratios:**
- 1 SE supports 3-4 AEs
- 1 CSM manages $2M-5M ARR (named accounts, high-touch)

---

## Sales Hiring and Ramp

### What "Good" Looks Like by Role

**SDR (entry level):**
- 1-2 years of outbound experience OR strong track record in customer-facing role
- Resilient: rejection is the job
- Coachable: SDR is a proving ground, not a final destination
- Can write clear, concise prospecting emails without templates

**AE (inside sales):**
- 2-4 years sales experience, preferably SaaS
- Can articulate their process for a discovery call
- Knows their numbers: quota, attainment, average deal size, sales cycle
- Shows how they build pipeline (AEs who only work inbound are a risk)

**AE (enterprise):**
- 4-8 years B2B sales, at least 2 in enterprise
- Has closed deals > $100K ACV
- Can name the stakeholders in a complex deal they navigated
- Understands procurement, security review, multi-year contracts

**VP Sales:**
- Has scaled a team from where you are to 2x your size
- Can build a comp plan from scratch
- Has hiring and firing experience
- Revenue from a repeatable process, not personal relationships

### Interview Process

**3-stage process:**
1. **Recruiter screen** (30 min): Motivation, experience, logistics
2. **Manager interview** (60 min): Structured questions on process, examples, numbers
3. **Panel / role play** (90 min): Mock discovery call + debrief; team fit

**Role play rubric:**
- Did they prepare (knew your product, your ICP)?
- Did they ask before pitching?
- Did they handle pushback without capitulating immediately?
- Did they confirm a next step with a date?

### Onboarding Structure (6-Week Ramp)

| Week | Focus | Activities |
|------|-------|-----------|
| 1 | Company, product, ICP | Onboarding sessions, product sandbox, shadow AE calls |
| 2 | Sales process, tools, messaging | CRM training, call review, write first prospecting emails |
| 3 | First outreach | Send first sequences, book first meetings, shadow closes |
| 4 | Independent discovery | Lead own discovery calls with manager reviewing |
| 5 | Full cycle | Handle pipeline independently, weekly coaching |
| 6 | Quota-bearing | 25% of quota expectation; full accountability begins |

### Performance Management

**Clear standards, no surprises:**
```
Month 3: 25% of quota expected. Miss by > 50% → performance conversation.
Month 4: 50% of quota expected. Miss by > 40% → PIP warning.
Month 5: 75% of quota. Miss by > 30% → formal PIP.
Month 6+: 100% of quota. Consistent miss → exit.
```

**PIP (Performance Improvement Plan) — not for show:**
- Should include specific, measurable targets (not "improve attitude")
- 30-60 day timeline
- Weekly check-ins with manager
- If targets aren't met: exit, no extensions
- A PIP that doesn't lead to improvement or exit is a management failure

**Rule:** Low performers who stay cost you your top performers. They watch what you tolerate.
