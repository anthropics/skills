---
name: deal-desk
description: Use when reviewing a specific inbound deal before close — when sales has asked for a discount that exceeds AE authority, when the customer has redlined the MSA, when per-deal economics (margin after discount, multi-year payment shape, indemnity exposure) need to be quantified, or when discount approval needs to be routed to a named human approver (Sales Director, VP Sales, CFO, CRO, General Counsel). Covers deal review, discount approval routing, per-deal margin scoring, deal exception handling, MSA redline triage, contract landmine detection (uncapped indemnity, MFN, perpetual license-back, missing DPA), and named-approver chain assembly. NEVER auto-approves — every output is a numeric scorecard plus a routing recommendation to a named human.
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [commercial, deal-desk, discount, margin, approval, redline, msa, terms]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# deal-desk

Per-deal review and discount-approval routing. Scores deal margin + risk, routes discount approval to the right human, redlines T&Cs against commercial policy. **Never auto-approves.** Every output is a score plus a routing recommendation to a named human approver.

## Purpose

Deal Desk / RevOps / sales leadership live at the moment between *sales-team-asks-for-discount* and *CFO/CRO/legal-signs*. This skill quantifies the asks and routes them.

Three deterministic tools:

1. `deal_scorer.py` — Scores a deal 0-100 across 5 dimensions (margin, risk, strategic value, commercial fit, term shape) and assigns one of four verdicts: **APPROVE / REVIEW / ESCALATE / DECLINE** — each tied to a named approver chain.
2. `discount_approval_router.py` — Maps a discount-percent + deal-size + tier to a named approver chain (AE → Manager → Director → VP → CFO/CRO) with estimated cycle days. Honors industry-tuned policy bands.
3. `terms_redliner.py` — Detects 10 founder/seller-killer patterns in deal terms (uncapped indemnity, MFN, perpetual license-back, missing DPA, NET-60+, broad non-solicit, etc.) with severity + standard counter + named legal/commercial approver.

## When to use

Invoke this skill when:

- Sales has flagged a discount request above AE authority.
- A customer has returned a redlined MSA and you need triage before routing to legal.
- The deal needs CFO sign-off and you want a defensible margin breakdown.
- An RFP response requires multi-year terms and you need to score the shape.
- A renewal expansion is bundled with a discount and you need to verify policy fit.
- You're building a deal-desk approval queue and need consistent routing.

**Do NOT use this skill to**: author the proposal (use `business-growth/contract-and-proposal-writer`), redesign the discount matrix (use the `commercial-policy` sibling skill), or do deep legal redline of full contract text (use `c-level-advisor/skills/general-counsel-advisor`).

## Workflow

1. **Intake the deal** — Sales/AE fills `assets/deal_intake_template.md` with ARR, term, discount, payment terms, customer tier, strategic flags, and any customer-flagged term redlines (20-min fill-out).
2. **Score margin + risk** — Run `deal_scorer.py --input deal.json --profile {saas|enterprise-software|services|marketplace}`. Read the composite + per-dimension breakdown + verdict.
3. **Route the discount** — Run `discount_approval_router.py --input deal.json --profile <same>`. Get the named approver chain + estimated cycle days. Modifiers (enterprise floor, SMB fast-lane) are surfaced explicitly.
4. **Flag the redlines** — Run `terms_redliner.py --input deal_terms.json`. Get ranked CRITICAL/HIGH/MEDIUM/LOW findings with the counter-language and the approver who must sign each.
5. **Assemble the packet** — Combine the three outputs into a deal-desk review packet. Always include the named approver chain. The packet is **a recommendation**, not an approval.

## Scripts

| Script | Purpose | Industry profiles |
|---|---|---|
| `scripts/deal_scorer.py` | 5-dimension scorecard with verdict + chain | saas, enterprise-software, services, marketplace |
| `scripts/discount_approval_router.py` | Discount % → named approver chain + cycle days | saas, enterprise-software, services, marketplace |
| `scripts/terms_redliner.py` | 10-pattern landmine scanner with counters | n/a (terms-driven) |

All three: stdlib-only, `--help`, `--sample`, `--input <json>`, `--output {human,json}`.

## References

- `references/deal_desk_canon.md` — Deal-desk operating practice: SaaStr playbooks (Jason Lemkin), Winning by Design (van der Kooij + Reichl), Forrester research, RevOps Co-op, OpenView benchmarks, Bridge Group AE comp, Salesforce Deal Desk best practices.
- `references/discount_economics.md` — Discount math + LTV impact: David Skok (For Entrepreneurs), Bessemer State of the Cloud, Tomasz Tunguz, OpenView NRR research, Pacific Crest + KeyBanc SaaS surveys, Insight Partners revenue ops. Includes worked margin math (a 30% discount on an 80% gross-margin product loses 37.5% of margin, not 30%).
- `references/contract_landmines.md` — 10+ named landmine patterns with example counter-language: YC startup library, Robert Klingberg (Founder's Guide to SaaS Agreements), Bowman + Brooke redline guides, IACCM/WorldCC commercial management research, Practical Law contracts library, Bradley Tusk on enterprise contracts, GC100 guidance.

## Assumptions

- The skill assumes the **commercial policy already exists** (discount bands, payment-terms norms, indemnity caps). It applies the policy; it does not design it. See the `commercial-policy` sibling skill for policy design.
- Industry profiles bake in *customary* thresholds. If your company has a documented discount matrix, pass it via `policy_thresholds` in the input JSON to override.
- The terms redliner detects the 10 most common landmines. It is **not** a substitute for General Counsel review on the full contract.
- Scoring weights (margin 30%, risk 20%, strategic 15%, commercial 20%, term 15%) reflect a CFO-leaning bias. RevOps-led shops may want to reweight; the weights are constants at the top of `score_deal()` and are easy to tune.

## Anti-patterns

- **Auto-approving deals.** This skill never says "approved". Every verdict (including `APPROVE`) names the human(s) who must sign. The output is a recommendation.
- **Skipping the redline scan** because the score is high. A high composite with `UNCAPPED_INDEMNITY` is still a DECLINE — critical signals override composite.
- **Using this for legal review of arbitrary contract text.** This skill takes a *structured* terms JSON. For prose redlining, use `c-level-advisor/skills/general-counsel-advisor/scripts/contract_risk_scanner.py`.
- **Treating the discount router as a discount calculator.** It routes a discount the AE/customer has already proposed; it does not calculate the right discount. Pricing logic lives in `commercial/skills/pricing-strategist`.
- **Routing every deal to CFO.** The router stops at the lowest-authority hop that can sign the deal. Over-escalation slows the funnel and trains AEs to over-discount.
- **Hand-editing the chain to skip a hop.** Modifiers (enterprise floor, SMB fast-lane) are explicit; hidden skips defeat the audit trail.

## Distinct from

| Sibling | Scope | Difference |
|---|---|---|
| `commercial/skills/pricing-strategist` | Sets the pricing **model** (per-seat vs usage vs tiered, list prices, packaging) | Operates at the strategy layer — not per deal |
| `business-growth/contract-and-proposal-writer` | **Authors** proposals, SOWs, MSAs | Output is a document; deal-desk is the gate **before** signing |
| `commercial/skills/commercial-policy` (sibling) | Designs the discount matrix and approval thresholds | Deal-desk **applies** that policy to one deal at a time |
| `c-level-advisor/skills/general-counsel-advisor` | Deep legal redline + term-sheet analysis | Operates on full contract prose; deal-desk uses structured terms JSON |
| `c-level-advisor/skills/cfo-advisor` | Burn rate, unit economics, fundraising models | Strategic finance; deal-desk is one-deal granularity |

## Quick examples

```bash
# Score a deal
python3 scripts/deal_scorer.py --sample
python3 scripts/deal_scorer.py --input my_deal.json --profile enterprise-software

# Route the discount
python3 scripts/discount_approval_router.py --sample
python3 scripts/discount_approval_router.py --input my_deal.json --profile saas

# Flag the redlines
python3 scripts/terms_redliner.py --sample
python3 scripts/terms_redliner.py --input my_deal_terms.json --output json
```

The sample (a 28%-discount enterprise SaaS deal with uncapped indemnity + MFN) correctly DECLINEs at 52.7 / 100 composite — the 28% discount destroys 35.9% of the deal's margin dollars under fixed COGS — and routes to AE → Deal Desk → VP Sales → CFO → CRO → General Counsel.

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time by `/cs:grill-commercial` or the Commercial orchestrator. Recommended answer + canon citation per question. Never bundled.

1. **"What's the gross margin at full discount, AND what does next quarter's pipeline look like at the same terms?"**
   Recommended: model both. Refuse to approve until the AE can articulate the precedent risk.
   Canon: David Skok (For Entrepreneurs — discount math), Tomasz Tunguz benchmarks. Anti-pattern: one 40% precedent reshapes 3 quarters of pipeline.

2. **"Is this discount inside or outside the standard discount matrix?"**
   Recommended: if outside, surface the policy exception explicitly and route to the named exception approver.
   Canon: OpenView discount benchmarks, RevOps Co-op playbooks.

3. **"What's the strategic value beyond ARR — logo, reference, expansion path?"**
   Recommended: require a named, verifiable expansion or reference commitment in writing.
   Canon: SaaStr (Jason Lemkin) on logo discounts; Winning by Design on commitment language.

4. **"Has the customer signed an indemnity cap, a liability cap, and a DPA (if EU data)?"**
   Recommended: required. Uncapped indemnity is a critical-signal override that blocks APPROVE regardless of margin.
   Canon: WorldCC (formerly IACCM) commercial management research, GC100 contract guidance.

5. **"What payment terms — NET-30, NET-45, or NET-60+?"**
   Recommended: prefer NET-30; NET-45+ is a cash flow drag worth quantifying.
   Canon: KeyBanc SaaS Survey, Pacific Crest data — every 15 days of payment terms costs ~2% of effective deal value.

6. **"Is the term multi-year with annual prepay, or annual auto-renew?"**
   Recommended: multi-year prepay > annual prepay > annual auto-renew. Auto-renew without 60-day notice is a redline.
   Canon: Salesforce Deal Desk best practices, OpenView NRR studies.

7. **"Who is the named human approver at each hop of the discount chain?"**
   Recommended: surface the name, not just the role. "VP Sales" is not an approver; "Maria Singh, VP Sales" is.
   Canon: Bridge Group SaaS AE compensation research — named approval reduces precedent drift by 50%+.

Walk depth-first. Lock 1-4 before opening 5-7. After all 7 are answered, invoke `deal_scorer.py` → `discount_approval_router.py` → `terms_redliner.py` in sequence.
