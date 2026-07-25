---
name: partnerships-architect
description: "Use when a startup is approached by a prospective partner and someone has to decide should we sign this partner, at what partner tier (referral / reseller / OEM / SI-consulting / strategic alliance), with what joint GTM commitment, and at what revshare. Classifies partner tier from independent-demand evidence vs. preferential-terms hunting, designs a 90-day joint GTM plan, models revshare against direct-sale margin, and surfaces kill criteria for unwinding under-performing partnerships. For Head of Partnerships, Head of BD, and Founder-CEOs doing reseller agreement, OEM deal, or strategic alliance review — not technical sale enablement, not channel cost economics, not M&A."
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [commercial, partnerships, channel-partners, joint-gtm, revshare, oem, reseller, strategic-alliance]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# partnerships-architect

## Purpose

Help Head of Partnerships, Head of BD, and Founder-CEOs answer four questions when a
prospective partner shows up:

1. **Is this a real partner, or someone hunting preferential terms without independent demand?**
2. **At what tier should we sign them?** (Referral / Reseller / OEM / SI-Consulting / Strategic Alliance)
3. **What's the 90-day joint GTM plan that proves the partnership works?**
4. **What revshare makes economic sense — and at what point does the partnership beat direct sale?**

The skill emits a tier verdict + GTM plan + revshare band with explicit kill criteria. It
does **not** sign the deal. The human, after running this skill, decides.

## When to use

- A prospective partner has approached and asked for reseller / OEM / "strategic" terms
- You're designing a new partner program tier structure
- You're reviewing an existing partnership that's underperforming and need to decide: re-tier, restructure GTM, or unwind
- A Big Logo wants a "strategic alliance" — and you need to validate it's real, not vendor-lock theatre
- A consulting firm or SI wants services revshare on your product
- A platform vendor offers OEM / white-label and you need to model the math
- You suspect "partner-sourced" deals are actually your own pipeline being skimmed for margin

**Do not use for:**
- Technical demos and POCs → `business-growth/sales-engineer`
- Cost-to-serve and ROI math on existing channel → sibling `channel-economics`
- Whole-company revenue strategy → `c-level-advisor/cro-advisor`
- Acquiring a company instead of partnering → `c-level-advisor/ma-playbook`
- Per-deal discount approval inside a signed partner contract → `deal-desk`

## Workflow

### Step 1 — Intake (≈ 20 min)

Fill `assets/partnership_intake_template.md`. Capture: partner_name, partner_type, evidence
of independent demand (named accounts they've sourced, end-customer relationships,
their sales team size), strategic value (geo / product / brand / channel economics),
commitments they've offered (joint marketing spend, dedicated headcount, certification,
sales targets).

If the intake template can't be honestly filled out, the prospective partner has not
demonstrated enough substance to evaluate. Stop. Go back to them.

### Step 2 — Tier classify

Run `scripts/partner_tier_classifier.py --input intake.json --profile saas --output markdown`.
Output ranks the partner into 1 of 5 tiers — REFERRAL / RESELLER / OEM / SI-CONSULTING /
STRATEGIC — with deterministic floors. STRATEGIC requires named_accounts ≥ 5 AND
multi-year commit AND dedicated resources. Skill emits rationale + kill criteria.

### Step 3 — Joint GTM plan

Run `scripts/joint_gtm_planner.py --input gtm.json --profile saas --output markdown`.
Output: 90-day plan with pre-launch milestones (training, certification, materials),
launch motion (target accounts, sales play, MDF allocation), mid-quarter checkpoint, and
90-day success criteria. Validates: cannot plan channel-led GTM for REFERRAL tier; cannot
plan white-label for non-OEM tier.

### Step 4 — Revshare model

Run `scripts/revshare_modeler.py --input revshare.json --output markdown`. Computes
margin per deal direct vs. via partner, recommended revshare % band based on partner
contribution depth (sourced > influenced > delivered), break-even partner ROI, and
long-term economics — at projected scale, does partner economics beat direct?

### Step 5 — Decide

Take tier + GTM plan + revshare band into the partnership committee. Skill does not sign
the partner — you do. Document kill criteria in the contract so the unwind is mechanical
when triggered.

## Scripts

- `scripts/partner_tier_classifier.py` — 5-tier classifier with deterministic floors per tier
- `scripts/joint_gtm_planner.py` — 90-day joint GTM plan generator with tier-validated motion
- `scripts/revshare_modeler.py` — revshare band + break-even ROI + long-term economics

All scripts: stdlib only. `--help` and `--sample` work on all three.

## Quick example

```bash
# Emits a 5-tier partner classification with deterministic floors per tier for the built-in sample partner
cd commercial/skills/partnerships-architect && python3 scripts/partner_tier_classifier.py --sample
```

## References

- `references/channel_partner_canon.md` — Caro on HP indirect channels, Chintagunta on channel economics, Hessling on partner programs, Forrester channel software stack, IDC channel research, Tien Tzuo subscription-channel models, Geoffrey Moore whole-product partnerships
- `references/joint_gtm_canon.md` — Aaron Ross *Predictable Revenue* (cold-source vs partner), Winning by Design, Jay McBain on co-sell, Microsoft Partner Network playbook, AWS Partner Network research, SiriusDecisions partner benchmarks, Bridge Group SaaS partner data
- `references/partnership_anti_patterns.md` — Forrester partner-led-from-your-pipeline research, Tom Tunguz on channel conflict, Hessling failure analyses, MIT Sloan on disproportionate strategic revshare, HP channel post-mortems, IBM channel-conflict cases, Salesforce AppExchange research

## Assumptions

- A partner who cannot produce evidence of independent demand (named accounts, end-customer
  relationships, their own sales team) is hunting preferential terms, not a partner.
- Industry profiles (`--profile`) tune defaults — they don't override your data.
- Revshare % bands are recommendations; the contract negotiation, MDF policy, and
  exclusivity terms are human commercial decisions outside this skill.
- "Partner-sourced" requires the partner to have introduced the deal AND owned the
  primary relationship. "Partner-influenced" pays at a lower band. Pay attribution
  matters more than slide-deck claims.
- This skill is for partnership design, not signed-partner deal management — once
  signed, per-deal commercial review routes to `deal-desk`.
- Kill criteria are mandatory. A partnership without a written unwind trigger compounds
  the bad-partner problem over years.

## Anti-patterns

- **"Partner = anyone who asked."** A partner with no independent demand is a discount hunter.
  Run the tier classifier — REFERRAL tier exists precisely to absorb these without giving
  away reseller margin.
- **Granting OEM / white-label terms without margin sufficient to fund support.** OEM means
  you support a customer you don't own. If the revshare doesn't fund Tier-2 support cost,
  the OEM deal is a losing trade.
- **Paying sourced-tier revshare on influenced-only deals.** Influenced ≠ sourced. The deal
  was going to close anyway. Pay the influenced rate.
- **No kill criteria for under-performing partner.** "Strategic alliances" without sunset
  clauses become permanent obligations after the executive sponsor leaves.
- **Channel conflict ignored until reps quit.** When your direct rep and your partner both
  show up at the same account, you lose either the rep or the partner. Decide the rules of
  engagement before, not after.
- **Exclusive territory granted to a weak partner.** This locks out the strong partner who
  would have actually sourced the deals.
- **MDF without ROI accountability.** Market Development Funds without named pipeline,
  reported ROI, and a quarterly true-up are subsidy, not investment.
- **No offboarding plan when partnership ends.** Customer continuity, data hand-back, IP
  cleanup, and brand take-down must be pre-negotiated. They're impossible to negotiate after
  the relationship has soured.

## Distinct from

- **business-growth/sales-engineer** — technical sale: demos, POCs, integration scoping.
  Operates after the partnership decision is made and a deal is in flight.
- **channel-economics** (sibling) — cost-to-serve and ROI math on an existing channel.
  Quantifies whether a signed partner is profitable. partnerships-architect decides
  whether to sign in the first place and at what tier.
- **c-level-advisor/cro-advisor** — strategic CRO judgment (when to hire a VP Channel,
  whole-company revenue mix decisions). partnerships-architect is per-partnership.
- **c-level-advisor/ma-playbook** — when the answer is "acquire them" not "partner with
  them." Trigger: the partner has independent moat you cannot replicate, or the
  partnership requires equity to align incentives. Re-route to ma-playbook.
- **deal-desk** — per-deal discount approval on signed partner contracts.

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time by `/cs:grill-commercial` or the orchestrator. Recommended answer +
canon citation per question. Never bundled. Lock 1-3 before opening 4-6.

1. **"Name 5 end customers this partner has already sold to in the last 12 months — at companies you would target yourself."**
   Recommended: if they cannot, they have no independent demand. Sign at REFERRAL tier only,
   if at all. Reseller/OEM/Strategic floors require demonstrated end-customer relationships.
   Canon: Joe Hessling — partner-program failure analyses identify "no independent demand"
   as the #1 root cause of dead partner tiers.

2. **"Is this partner asking for preferential commercial terms, or asking how to bring you customers?"**
   Recommended: discount hunters lead with terms; real partners lead with accounts. Listen
   to the first 30 minutes of the first meeting.
   Canon: Forrester channel research — 60%+ of "partner inquiries" at early-stage SaaS are
   discount hunting, not channel investment.

3. **"What's the joint value proposition in one sentence, and who is the named end-customer it serves?"**
   Recommended: if there is no joint value prop distinct from either party's solo offering,
   there is no partnership — there is co-marketing at best.
   Canon: Geoffrey Moore (*Crossing the Chasm*) — whole-product partnerships exist when
   neither party alone delivers the customer outcome.

4. **"At what % discount / revshare does this partnership beat the direct-sale economics, and at what scale?"**
   Recommended: model break-even pipeline volume. If partner-sourced deals must exceed
   30% of channel volume to beat direct, and partner can plausibly deliver 5%, you have
   built a losing program.
   Canon: Pradeep Chintagunta (Chicago Booth) on channel economics — channel partnerships
   without volume floor break even in theory and lose money in practice.

5. **"What are the named kill criteria for unwinding this partnership, and are they in the contract?"**
   Recommended: minimum pipeline floor by quarter, minimum certified resources, minimum
   joint deals closed, 90-day cure period. Unwinding without pre-agreed criteria becomes
   a 2-year legal battle.
   Canon: IBM channel-conflict case studies (1990s post-divestiture) — undocumented kill
   criteria converted bad partners into permanent obligations.

6. **"If this partner sells to one of YOUR direct accounts, who wins — your rep or them?"**
   Recommended: Rules of Engagement in writing, signed before kickoff. Territory by named
   account, by segment, or by geo. Conflict resolution at named human, not committee.
   Canon: Jay McBain (Canalys) — channel conflict is the #1 partner program killer; written
   ROE published before partner signs prevents 80% of disputes.

7. **"Is this a partnership, or should this be an acquisition?"**
   Recommended: if the partner has independent moat you cannot replicate AND the
   partnership requires multi-year exclusivity AND the partnership requires equity-like
   alignment, you're describing an acquisition. Re-route to `ma-playbook`.
   Canon: HP channel post-mortems (Indigo, EDS partial integrations) — partnerships
   structured as acquisitions-without-equity destroy more value than either pure path.

Walk depth-first. Lock 1-3 (is this a real partner?) before opening 4-7 (is the structure
right?). After all 7 are answered, invoke `partner_tier_classifier.py` →
`joint_gtm_planner.py` → `revshare_modeler.py` in sequence.
