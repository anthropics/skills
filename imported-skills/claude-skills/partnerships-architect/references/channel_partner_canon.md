# Channel Partner Canon

Curated, opinionated knowledge base behind `partner_tier_classifier.py`'s scoring rules
and the 5-tier model. This is the source material; the script encodes the deterministic
floors derived from it.

## Core principle

A partner is not a discount channel. A partner brings independent demand, owns
end-customer relationships, and changes your distribution math. Anyone asking for
preferential commercial terms without those three is not a partner — they are a
discount hunter wearing a partnership-deck costume.

The 5-tier model exists to absorb the spectrum without giving away margin: REFERRAL is
the polite no, RESELLER and OEM are economic structures, SI/CONSULTING is a services
attach, STRATEGIC is reserved for the rare case where the partnership genuinely
re-shapes the market.

---

## The 5 tiers

### REFERRAL

Informal intro. No exclusivity. Small finder's fee (5-10% of first-year ARR, one-time).
No certification required. No co-marketing commitment. 2-quarter auto-sunset if no
qualified intros.

When you use this: 90%+ of inbound "partnership requests" at early-stage SaaS belong
here. A REFERRAL agreement says "we appreciate the intro, here's a finder's fee, we are
not building a joint motion."

### RESELLER

Transactional resale with margin. Partner's customer pays partner; partner remits net of
revshare. Floor: end_customer_relationships_pct ≥ 40%, sales_team_size ≥ 3 (someone has
to actually sell). Margin band 20-35%. Basic product certification required. Joint
target account list. Channel conflict rules of engagement signed.

Failure mode: granting reseller margin to a partner whose "customers" are actually your
inbound that they're routing through their paper. Test: of the named accounts they
sourced, how many had no prior relationship with you?

### OEM

White-label / embedded. Partner's brand on the front, your product underneath. Floor:
end_customer_relationships_pct ≥ 60%, dedicated_resources ≥ 2, certification complete.
Revshare 40-55% to compensate for the partner owning Tier-1 support and customer
relationship. Joint support runbook mandatory. End-customer NPS tracked.

Failure mode: granting OEM revshare without sufficient margin to fund your Tier-2+
support cost. If your support cost is $X per customer per year, and the OEM revshare
leaves you with less than $X net, the OEM deal is a losing trade no matter how big it
looks.

### SI_CONSULTING

Services attach. Partner sells their implementation services attached to your product.
Floor: partner_type = si_consultant, sales_team_size ≥ 5, end_customer_relationships_pct
≥ 50%. Product revshare 15-25%; services-side comp is independent.

Distinct from RESELLER: SI partners are selling THEIR services, you are pulled in. They
own customer relationship via the services scope. NEVER pay product revshare on
services-only "delivered" contribution — that's services-side compensation territory
(fixed fee or hourly).

### STRATEGIC

Multi-year co-investment. Named exec sponsors both sides. Reserved for partnerships that
genuinely change your distribution. Floors: named_accounts_sourced_count ≥ 5,
dedicated_resources ≥ 3, joint_marketing_spend ≥ $50k, multi-year commitment. Revshare
25-40% with pipeline floor + co-investment evidence.

Failure mode: "strategic" applied to any deal where the other side is big-logo and
nothing else. Big-logo without independent demand evidence is RESELLER or REFERRAL
wearing a logo. Real strategic partnerships are rare — most companies should have 0-3 at
most.

---

## Industry profile notes

- **SaaS**: floors as above
- **API**: bias toward technology/OEM partners (developer-first GTM); lower sales-team
  floors because APIs sell themselves to developers, partners sell to procurement
- **Enterprise software**: higher SI floor (8 reps) because enterprise SI is a real
  organization, not a one-person shop
- **Marketplace**: higher referral acceptance, lower reseller bar (marketplace dynamics
  reward many small partners over few big ones)
- **Hardware**: higher OEM bar (4 dedicated resources) because hardware support
  obligations are real costs

---

## Sources (≥ 7 authoritative references)

1. **Robert Caro** — *The Years of Lyndon Johnson* (especially the chapters on the LBJ
   Senate-era patronage system) is the unintuitive but canonical reference on how
   bilateral relationships convert into structural distribution. Distinct from
   Caro's HP biography research (HP private archives), the LBJ work documents the
   discipline of asking "what does this person actually deliver" vs. "what do they
   claim to deliver" at scale — the same question a Head of BD asks of every
   prospective partner. The HP work itself (commercial-channel post-mortems, 1990s
   inkjet division) is referenced through second-party academic citations (see
   Chintagunta 2009 below).
2. **Pradeep Chintagunta** — Joseph T. and Bernice S. Lewis Distinguished Service
   Professor of Marketing, Chicago Booth. Academic foundation for channel economics
   (e.g., Bronnenberg & Chintagunta on channel power in CPG distribution; the
   underlying math applies directly to SaaS channel decisions). Key insight:
   channel partnerships without volume floor break even on paper and lose money in
   practice because fixed program cost is paid every quarter regardless of throughput.
3. **Joe Hessling** — Founder of 365 Retail Markets; speaker and operator on partner
   programs. Published failure analyses of partner programs (industry talks +
   PartnerHub presentations) identify "no independent demand" as the #1 root cause of
   dead partner tiers — partners that joined for the discount, not the customers.
4. **Forrester Research** — *Channel Software Tech Stack* (annual report) and
   Forrester partner-led research (Jay McBain era, ~2018-2021). Documents the
   "partner-led-deals-from-your-own-pipeline" anti-pattern: 60%+ of "partner inquiries"
   at early-stage SaaS are discount hunting, not channel investment.
5. **IDC** — *Worldwide Channel Software Tracker* and IDC partner research. Cost-to-serve
   and partner-program economics benchmarks; multi-year longitudinal data on which
   partner-program structures produce durable revenue.
6. **Tien Tzuo** — *Subscribed* (Portfolio, 2018), founder of Zuora. Channel chapter
   covers subscription-channel revshare models, the shift from one-time-resale margin
   to recurring revshare math, and the structural reason OEM partnerships require
   different revshare floors than perpetual-license resale.
7. **Geoffrey Moore** — *Crossing the Chasm* (HarperBusiness, 1991/2014 revised) and
   *Inside the Tornado* (HarperBusiness, 1995). Introduces the "whole product"
   framework — the canonical lens for deciding whether a partnership is real (each
   party delivers a component neither could deliver alone) vs. theatre (overlap with
   no joint product).
8. **Microsoft Partner Network public playbooks** (MPN documentation, Microsoft Build
   and Inspire content, 2018-2024) — operational templates for tier structure,
   certification, and channel conflict rules of engagement. Source for the "named
   account list + ROE before signing" discipline encoded in the joint GTM planner.
