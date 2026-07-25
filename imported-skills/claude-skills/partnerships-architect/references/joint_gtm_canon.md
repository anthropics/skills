# Joint GTM Canon

Source material behind `joint_gtm_planner.py`'s tier-validated motion matrix and the
90-day milestone defaults. The discipline encoded here is: a partnership does not exist
until a joint pursuit closes a deal that neither side would have closed alone.

## Core principle

Joint GTM is not a marketing event. It is a sales motion that has to produce
attributable revenue against a named, written floor — within one sales cycle, or the
partnership is theatre.

The 90-day plan exists to manufacture decision-grade evidence: did this partner actually
move pipeline, or did we just throw a launch party? Without the structure, partnership
reviews degrade into "we like working with them" — which is a feeling, not a data point.

---

## The 4 sales motions

### pure_referral

Partner sends a lead. Your AE runs the entire sale. Partner gets a finder's fee on close.
No exclusivity, no MDF, no certification. Operates at REFERRAL tier; sometimes RESELLER
and SI_CONSULTING.

Anti-pattern: paying finder's fee on accounts already in your pipeline. The first job of
the program is attribution discipline — was this lead really new to us before the
partner sent it?

### co_sell

Partner and your AE jointly pursue the same account. Partner brings access; you bring
product. Both sides on calls, both forecasted. Revshare paid on close. Operates at
RESELLER, OEM, SI_CONSULTING, STRATEGIC tiers.

Anti-pattern: "co-sell" that is really "we let them watch" — partner attends meetings
but does not actively progress the deal. After 90 days, look at who advanced the deal
between stages. If your rep moved every stage, it was not co-sell — pay influenced rate,
not sourced.

### channel_led

Partner runs the full sales motion; you provide SE support and product. Partner
forecasts; you do not. Operates at RESELLER, OEM, STRATEGIC tiers — never REFERRAL or
SI_CONSULTING.

Anti-pattern: channel-led claimed but every demo requires your SE. If your SE is on
every customer call, the partner cannot sell the product solo — they are channel-led on
paper, co-sell in reality. Recertify or change the motion.

### white_label

Partner's brand on the front; you are invisible to the end customer. Partner owns
support, branding, customer relationship. Operates at OEM tier only. Requires
higher revshare to compensate for the loss of customer relationship.

Anti-pattern: white-label without margin sufficient to fund your Tier-2+ support cost.
If you are the de-facto product owner but only see 45% of the revenue, and your CTS
takes 30% of that, you are running a charity.

---

## The 90-day milestone structure

### Pre-launch (day -30 to 0)

Five non-negotiables: signed agreement; named exec sponsors both sides; jointly built
Target Account List (TAL) with conflict resolution per account; partner sales
certification; Rules of Engagement (ROE) signed before any joint pursuit. OEM and
STRATEGIC tiers add an integration QA + support runbook signoff.

### Launch (day 0 to 30)

Three measurable beats: first joint pursuit named within 7 days; 5 joint pursuits in
flight by day 15; first closed-won (or clear blocker isolation) by day 30. Channel-led
motions add a partner-led-demo-without-our-SE validation at day 20.

### Mid-quarter checkpoint (day 45)

Hard gates: pipeline-sourced ≥ 50% of 90-day floor; at least 1 closed-won OR named
blocker with owner + remediation date; certified rep count maintained; ROE working (zero
unresolved escalations); kill-criteria triggered? If yes, escalate to partnership
committee NOW.

### 90-day decision (day 90)

Decision-grade artifact: pipeline-sourced ≥ floor, deals-closed-won ≥ floor, win/loss
doc, certified rep count maintained, channel-conflict log clean. Outcome: continue /
re-tier / unwind, with named human accountable. No "let's see another quarter" — that's
how dead partnerships compound.

---

## Industry profile notes

- **SaaS**: 8x deal_avg_size as pipeline floor for RESELLER; 12x for STRATEGIC
- **API**: higher pipeline multiples (10x reseller, 15x strategic) — API deals are
  smaller and higher-volume
- **Enterprise software**: lower deal-count floors but higher pipeline multiples
- **Marketplace**: highest pipeline multiples (12-18x) — partner volume is the whole
  point
- **Hardware**: highest MDF defaults ($100k OEM, $200k STRATEGIC) — hardware partner
  programs require physical inventory, demo equipment, certified field engineers

---

## Sources (≥ 7 authoritative references)

1. **Aaron Ross & Marylou Tyler** — *Predictable Revenue* (PebbleStorm, 2011). Source
   for the cold-source vs. partner-source attribution distinction; the
   "Cold Calling 2.0" framework's principle is that channel source is a different
   pipeline economy than direct outbound — they cannot share metrics or comp plans.
2. **Winning by Design** — Jacco van der Kooij and team. SaaS sales methodology
   incorporating partner-attached deals into the bow-tie funnel; the discipline of
   tracking partner-attached vs. partner-sourced separately is canon here.
3. **Jay McBain** — Chief Analyst at Canalys (formerly Forrester); industry's leading
   voice on co-sell discipline. Public writing (LinkedIn newsletter,
   Channel-as-a-Service podcast 2019-2024) frames co-sell as "the most-misused word in
   channel" — most "co-sell" is actually referral, and the difference matters for
   revshare math.
4. **Microsoft Partner Network playbooks** (MPN public documentation; Microsoft Inspire
   and Build sessions, 2018-2024). Operational source for tier structure, MCT/MCP
   certification cadence, and the principle that channel-led motions require partner
   certification + customer-facing partner-of-record designation BEFORE joint
   pursuits begin.
5. **AWS Partner Network research** (APN public documentation; AWS re:Invent Partner
   Day content, 2017-2024). Source for the consulting partner vs. technology partner
   distinction, the competency-tier model, and the "partner-led" SI motion mechanics.
6. **SiriusDecisions** (now Forrester after 2018 acquisition) — partner-program research
   and the SiriusDecisions Demand Waterfall framework. Source for the discipline of
   tracking partner-sourced pipeline separately from partner-influenced, and the
   benchmark that partner-influenced should pay at ~50% the revshare rate of
   partner-sourced.
7. **Bridge Group SaaS Sales Benchmarks** (annual) — partner-attached deal benchmarks,
   ramp times for partner reps vs. direct reps, and the data behind the "12 months
   minimum to evaluate a partner program" heuristic encoded as a warning in the
   joint_gtm_planner.
8. **Maria Pergolino & Aaron Ross** — *From Impossible to Inevitable* (Wiley, 2016).
   Chapter on channel reproduces the discipline that partner programs without named
   pipeline floors are decoration; the 8x-deal-avg-size pipeline floor convention for
   RESELLER tier derives from this and SiriusDecisions data.
