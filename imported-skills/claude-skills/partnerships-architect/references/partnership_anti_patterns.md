# Partnership Anti-Patterns

The named failure modes encoded as warnings and validation errors across the three
scripts. Each anti-pattern below is sourced from real channel post-mortems and the
academic literature on channel economics. If your partnership program has any of these,
re-tier or unwind.

## Core principle

A bad partnership is more expensive than no partnership. The fixed program cost (MDF,
overhead, certification, joint marketing) is paid every quarter regardless of throughput.
A partner that produces sub-floor volume converts the program from "investment" into
"subsidy" — and subsidies are silent margin destroyers that compound across years.

The kill criteria embedded in every tier exist to make the unwind mechanical. The
moment a kill criterion triggers, the human review is "execute the contract" not
"renegotiate the relationship." The contract was the renegotiation; if you wait until
the criterion triggers to start the conversation, you have already lost the 6 months
you needed to source the replacement partner.

---

## The 8 anti-patterns (named and indexed)

### 1. "Partner = anyone who asked"

The default sin of inbound partnerships. A prospect emails "we should partner," the
account manager forwards to BD, BD forwards to legal, and 6 weeks later there is a
signed "partner agreement" with no commitments on either side.

Test: run the intake template honestly. If `named_accounts_sourced_count = 0` AND
`end_customer_relationships_pct < 30`, this is not a partner. Sign at REFERRAL tier
with auto-sunset, or do not sign.

Sources: Forrester partner research (60%+ of inbound partner inquiries at early-stage
SaaS lack independent demand); Joe Hessling partner-program failure analyses.

### 2. "White-label without margin enough to fund support"

OEM deal looks great on the deck. Net margin per deal looks great. Three months in, you
discover the OEM customer base is 4x the support volume of your direct customers
(because they don't know your product, and the OEM didn't actually train their CS team).

Test: model `our_cost_to_serve_via_partner_usd` honestly, including Tier-2+ support
load, escalation triage, custom-integration debugging, and post-incident reporting. If
the top of the revshare band produces negative per-deal margin, do not sign.

Sources: Hewlett-Packard channel post-mortems (1990s inkjet OEM cases); IBM channel-
conflict cases (post-PC-divestiture, late 1990s through 2005).

### 3. "Revshare for influenced-only deals at sourced rates"

Partner attends a few meetings, sends an intro email, accelerates a deal that was
already in motion. Their CRM logs it as "partner-sourced." Your CRM logs it as
"originated outbound rep X." The contract was ambiguous. The partner invoices at 30%
revshare on the full ARR.

Test: written attribution rules in the contract. "Sourced" requires partner to have
introduced AND owned the relationship through stage 2. "Influenced" pays at ≤ 50% of
sourced rate. Disputed attribution defaults to influenced.

Sources: SiriusDecisions partner research; Jay McBain on the "most-misused word in
channel."

### 4. "No kill criteria for under-performing partner"

The partnership has been declining for 4 quarters. The exec sponsor on the partner side
left 2 quarters ago. The certified reps were never replaced. Pipeline-sourced is at 20%
of the floor. But there is no clause in the contract specifying what happens — so the
program stays funded, the MDF gets paid, and the relationship dies slowly while you
keep writing checks.

Test: every tier has named kill criteria in the contract. RESELLER: <25% of target in
any quarter triggers 90-day cure. STRATEGIC: <70% of floor in 2 consecutive quarters
triggers joint exec review. The criteria are mechanical, not discretionary.

Sources: IBM channel-conflict case studies; MIT Sloan research on disproportionate
strategic-tier revshare paid to long-dead partnerships.

### 5. "Channel conflict ignored until reps quit"

Your top AE has been working an account for 8 months. The OEM partner signs the same
account through their channel motion. The deal closes — but to the partner. Your AE
gets nothing (no SPIFF, no attribution, no comp). Two weeks later, your top AE quits.

Test: Rules of Engagement (ROE) signed BEFORE any joint pursuit begins. Named-account
map. Conflict resolution at named human (Sales Director ↔ Partner Sales lead), not
committee. Documented escalation path. Channel-conflict log reviewed at every QBR.

Sources: Jay McBain (Canalys) — channel conflict is the #1 partner program killer;
written ROE published before partner signs prevents 80% of disputes.

### 6. "Exclusive territory granted to weak partner"

Partner asks for exclusive territory at signing — "we need protection to invest in
sales." You grant exclusive EMEA. Two quarters later, the partner has produced 1 deal.
Two more quarters: still 1. Meanwhile, three other partners are asking for EMEA. Your
contract prevents you from signing them. Three years later, you are stuck with a dead
partner in exclusive territory.

Test: exclusivity, if granted, is performance-conditioned. Volume floor by quarter;
miss the floor twice, exclusivity converts to non-exclusive. Never grant unconditional
exclusivity at signing.

Sources: Hewlett-Packard channel post-mortems (Indigo press division partnerships);
Pradeep Chintagunta on channel power dynamics.

### 7. "MDF without ROI accountability"

Quarter 1: $15k MDF sent. Quarter 2: $15k MDF sent. Quarter 3: $15k MDF sent. Quarter
4: no named pipeline attributable to MDF spend. Partner reports "we are building
brand awareness." You have spent $60k.

Test: every MDF disbursement tied to a named program (webinar, field event, content
piece) with named pipeline expectation. Quarterly true-up with attributable pipeline.
Sub-floor pipeline triggers MDF pause, not "let's give it more time."

Sources: Forrester channel research; AWS Partner Network MDF accountability framework
(public APN documentation).

### 8. "No offboarding plan when partnership ends"

The partnership has ended. Now: what happens to the joint customers? Where does the
customer data go? Who answers their support calls? Whose brand is on the renewal? Is
there a non-compete? Can the partner keep selling to the customers they sourced? The
answers are being negotiated in real time, under pressure, with lawyers on the phone.

Test: offboarding plan in the original contract. Data hand-back procedures, customer
continuity ownership, IP cleanup, brand take-down timeline, post-termination
non-compete (if any). Negotiate offboarding while the relationship is healthy.

Sources: IBM channel-conflict case studies; Salesforce AppExchange research on
partnership endings.

---

## Sources (≥ 7 authoritative references)

1. **Forrester Research** — *Channel Software Tech Stack* and partner-led research
   (Jay McBain era). Documents the partner-led-deals-from-your-own-pipeline anti-
   pattern and MDF accountability gaps in early-stage SaaS partner programs.
2. **Tom Tunguz** — Redpoint Ventures GP; channel-conflict and SaaS partner economics
   writing (tomtunguz.com archives, 2014-2024). Source for the "channel conflict
   trap" terminology and the data on rep attrition correlated with unresolved channel
   conflict.
3. **Joe Hessling** — partner-program failure analyses (industry talks, PartnerHub
   presentations). Source for the "no independent demand" failure mode and the
   discipline of partnership intake-template honesty as a leading indicator.
4. **MIT Sloan Management Review** — articles on disproportionate revshare to
   "strategic" partners (e.g., research on partnership ROI miscalibration, 2010-2020
   archive). Quantifies the cost of strategic-tier programs that produce sub-tier
   results.
5. **Hewlett-Packard channel post-mortems** — published case studies and academic
   write-ups of the HP inkjet, Indigo, and EDS partial integration channel programs.
   Source for anti-patterns 2, 6, and the data behind hardware-tier revshare floors.
6. **IBM channel-conflict case studies** (post-PC-divestiture era, 1990s-2005) — both
   internal IBM publications and Harvard Business Review case treatments. Source for
   anti-patterns 4 and 8 specifically — what happens when kill criteria and
   offboarding are not in writing.
7. **Salesforce AppExchange research** — public AppExchange ISV partner research, 2015-
   2024. Source for partnership-ending anti-patterns and the data on ISV partner
   churn correlated with absent offboarding clauses.
8. **Pradeep Chintagunta** (Chicago Booth) — *Channel power, channel investment, and
   partner economics* academic literature. Source for the principle that channel
   partnerships without volume floor break even in theory and lose money in practice.
