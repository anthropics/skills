---
name: rfp-responder
description: "Use when an RFP, RFI, RFQ, security questionnaire, vendor questionnaire, or proposal request arrives and the team needs a structured response — parsing multi-section buyer-dictated requirements (MANDATORY vs WEIGHTED vs NICE-TO-HAVE), building a Shipley-method proof-point matrix mapping each requirement to a verifiable proof point, articulating 3-5 win-themes that ladder up across requirements, and producing a Shipley-derived winrate estimate that informs a bid / no-bid / partner-bid recommendation. For Bid Managers, Proposal Leads, Directors of Sales, and Sales Engineers at the response-strategy moment. Surfaces GAP requirements explicitly — never invents claims. NOT free-form proposal narrative authoring, NOT contract redline, NOT marketing collateral."
context: fork
version: 2.8.0
author: claude-code-skills
license: MIT
tags: [commercial, rfp, rfi, rfq, shipley, win-theme, proof-points, structured-response, bid-management]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# rfp-responder

## Purpose

Help Bid Managers, Proposal Leads, and Directors of Sales answer five questions at the response-strategy moment:

1. **What is this RFP actually asking?** (parse sections, tag every requirement MANDATORY / WEIGHTED / NICE-TO-HAVE, extract scoring criteria, surface deadlines and format constraints)
2. **What is our true fit?** (proof-point matrix per requirement: STRONG / PARTIAL / GAP, each backed by a verifiable source — case study, certification, customer quote, technical attestation, benchmark)
3. **What is our win-theme strategy?** (Shipley method: 3-5 themes that ladder up across requirements, not generic value-prop bullets)
4. **What is our realistic winrate?** (Shipley-derived factor model: fit, incumbent, relationship strength, decision-criteria alignment, late-entry, competitor count, deal size — produces estimate + confidence band)
5. **Should we bid?** (deterministic verdict: BID / PARTNER-BID / NO-BID with named factors driving the call)

The skill surfaces GAPs explicitly. Leadership decides whether to close them, partner around them, or no-bid. **It never invents claims.**

## When to use

- A 30+ page RFP / RFI / RFQ has landed with a 7-14 day response deadline
- A security questionnaire (SIG, CAIQ, custom-buyer) needs structured Q&A — not prose
- The team is preparing a bid / no-bid review and needs a defensible winrate estimate
- Sales Engineering has a proof-point library but no system to map proofs to requirements
- Leadership wants to see fit % (STRONG / PARTIAL / GAP) before committing pursuit budget
- A late-entry opportunity needs honest assessment of the relationship deficit

**Do not use for:**
- Free-form proposal narrative authoring → `business-growth/contract-and-proposal-writer`
- Contract redline AFTER award → `c-level-advisor/general-counsel-advisor`
- Marketing collateral / category content → `marketing-skill/*`
- Discount approval on the awarded deal → `commercial/deal-desk`
- Pricing-model design for a new product → `commercial/pricing-strategist`

## Workflow

### Step 1 — Parse the RFP

Drop the RFP markdown / text into `scripts/rfp_parser.py`. Output: structured JSON listing every requirement, tagged MANDATORY / WEIGHTED / NICE-TO-HAVE based on cue words (must / shall = MANDATORY; should / weighted scoring numbers = WEIGHTED; may / preferred / desired = NICE-TO-HAVE). Captures section structure, scoring criteria if disclosed, deadline, submission format constraints.

```bash
python scripts/rfp_parser.py --input rfp.md --output json > parsed.json
```

### Step 2 — Score fit per requirement

Fill `assets/rfp_intake_template.md` with your proof-point library (each proof tagged with type + verifiable source + which requirement-tags it covers) and proposed win-themes. Feed parsed RFP + intake into `scripts/response_drafter.py`. Output: proof-point matrix per requirement with STRONG / PARTIAL / GAP, win-theme injection, GAP audit.

```bash
python scripts/response_drafter.py --input draft_input.json --output markdown > matrix.md
```

**Hard rule:** GAP requirements are surfaced, never invented around. Leadership reads the GAP audit and decides: close the gap, partner-bid, or no-bid.

### Step 3 — Apply win-theme strategy

Shipley method: 3-5 themes that span requirements. Each theme answers "why us over the incumbent / competitor on the criteria the buyer named." `response_drafter.py` shows which themes thread through which requirements — a theme appearing in <2 requirements is decorative, not strategic, and gets flagged.

### Step 4 — Estimate winrate

Feed deal context (fit %, incumbent strength, relationship, decision-criteria alignment, late-entry, competitor count, deal size vs. average) into `scripts/winrate_predictor.py`. Output: Shipley-derived estimate 0-100% + confidence band + factor breakdown + BID / PARTNER-BID / NO-BID verdict.

```bash
python scripts/winrate_predictor.py --input deal_context.json --profile enterprise-software --output markdown
```

**No-bid threshold:** estimate < 20% triggers automatic no-bid recommendation.

### Step 5 — Decide

Take parsed RFP + proof-point matrix + GAP audit + winrate estimate into the go / no-go review. Skill does not commit pursuit budget — leadership does.

## Scripts

- `scripts/rfp_parser.py` — section + requirement extractor (regex + cue-word heuristics, stdlib only)
- `scripts/response_drafter.py` — proof-point matrix + win-theme injection + GAP audit
- `scripts/winrate_predictor.py` — Shipley-derived factor model + bid/no-bid verdict, industry-profile-tuned

All scripts: stdlib only (argparse, json, sys, pathlib, re, collections, statistics). `--help` and `--sample` work on all three.

## References

- `references/shipley_method_canon.md` — Shipley Proposal Guide v6, Shipley Capture Guide, APMP BoK, Tom Sant, Tom Searcy + Henry DeVries, Strategic Proposals research, Larry Newman
- `references/rfp_strategy_canon.md` — FAR, GSA, Forrester, Gartner, Bain, McKinsey, B2B International on RFP win-rates and buyer behavior
- `references/rfp_anti_patterns.md` — Shipley failure modes, APMP cases, Strategic Proposals research, federal loss reviews, MIT Sloan, Bain commercial-discipline, Gartner

## Assumptions

- **The RFP is the ground truth.** If the buyer asked it, answer it — in the order they asked, in the format they specified. Re-organizing for narrative flow is for proposals, not RFPs.
- **Proof points must be verifiable.** A claim is only as strong as the case study, certification, customer reference, or technical attestation backing it. Unsourced claims become GAPs.
- **Win-themes are buyer-side, not seller-side.** "We're the leader in X" is a marketing claim; "Your operations team reduces incident MTTR by 60% with the same headcount" is a win-theme. Shipley canon, not optional.
- **Winrate estimates are directional.** The model is a discipline tool to force honest pursuit-qualification — not an oracle. Confidence band always wider than the point estimate suggests.
- **Industry profiles tune base rates** — government RFPs reward compliance discipline; enterprise SaaS rewards reference accounts; healthcare rewards regulatory + security depth.
- **Late entry is a structural disadvantage.** Entering after the RFP issued, with no relationship history, drops base rate ~15%. The skill names this, doesn't hide it.

## Anti-patterns

- **Inventing a proof point to fill a GAP.** Hard rule violation. GAPs surface for leadership decision, not for prose-laundering. See `references/rfp_anti_patterns.md`.
- **Responding to every RFP.** Without a qualified bid / no-bid gate, the team burns capacity on <20% winrate pursuits and loses the 50%+ pursuits to lack of focus. Bain commercial-discipline research.
- **Generic response with no win-theme.** A proposal that could be sent verbatim by any competitor is decorative. Shipley failure mode #1.
- **Missing a mandatory disqualifier late.** FedRAMP / HIPAA / ISO 27001 / SOC 2 / on-shore data residency caught on Day 12 of a 14-day response = wasted pursuit. Parser surfaces these on Day 1.
- **Answering the question YOU wanted asked.** RFP responder discipline: answer what they asked, in their words, in their order. Re-framing belongs in cover letters, not in the compliance matrix.
- **No compliance matrix.** Every requirement should map to a response section + page number. Evaluators score on a matrix; respondents who don't provide one self-disqualify on traceability.
- **Late-entry without acknowledging the relationship deficit.** Entering cold against an incumbent with a 3-year relationship and no champion = sub-20% winrate. Pretending otherwise wastes Sales Engineering capacity.
- **Treating WEIGHTED requirements like MANDATORY.** Score-weighted requirements reward depth on the high-weight items, not uniform mediocrity across all. Shipley capture method.

## Distinct from

- **`business-growth/contract-and-proposal-writer`** — free-form narrative proposals where YOU set the structure (executive briefs, capability statements, unsolicited proposals). RFP-responder handles **buyer-dictated structured Q&A** where the buyer set the questions, sections, scoring criteria, and format. Different artifact, different decision logic.
- **`c-level-advisor/general-counsel-advisor`** — contract redline and IP/risk review AFTER award. RFP-responder operates BEFORE award, on the response strategy.
- **`marketing-skill/*`** — external marketing assets (web copy, content, ASO, SEO, brand voice) for many-to-many audiences. RFP-responder produces a **single-buyer artifact** with deterministic compliance requirements.
- **`commercial/deal-desk`** — per-deal discount routing on a closing opportunity. RFP-responder is pursuit-stage; deal-desk is close-stage.
- **`commercial/pricing-strategist`** — pricing-model design for a new product. RFP-responder consumes existing pricing as input to the commercial-terms section.

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time before any script runs. Recommended answer + canon citation per question. Never bundled.

1. **"What's your STRONG / PARTIAL / GAP split on the MANDATORY requirements?"**
   Recommended: STRONG ≥ 70% on MANDATORY before bidding. PARTIAL/GAP on any MANDATORY = either close the gap pre-submission or no-bid.
   Canon: Shipley *Proposal Guide v6* — capture-management discipline, "Pgw (probability of win) is bounded by your weakest MANDATORY."

2. **"Is there an incumbent, and how strong is their position?"**
   Recommended: strong incumbent (3+ years, no displacement event) drops base winrate ~30%. Don't bid without a named displacement trigger.
   Canon: Forrester B2B-RFP research — incumbents win 70-80% of renewal RFPs absent a named failure event.

3. **"Did you enter the conversation before or after the RFP issued?"**
   Recommended: late-entry (after RFP issued, no prior engagement) drops winrate ~15% and signals the RFP was scoped to someone else's strengths.
   Canon: Tom Searcy + Henry DeVries *How to Win Big Business* — "If you didn't help write the RFP, you're column fodder."

4. **"What are your 3-5 win-themes, and does each thread through ≥2 requirements?"**
   Recommended: themes that appear in only one requirement are decorative. Themes must ladder up across MANDATORY + WEIGHTED sections.
   Canon: Shipley *Capture Guide* — win-themes are the buyer-side answer to "why us" across the evaluation criteria, not seller-side feature lists.

5. **"For every claim in the response, can you name the verifiable source?"**
   Recommended: every claim → case study / certification / customer reference / technical attestation / benchmark. Unsourced claims = GAPs.
   Canon: APMP BoK — "Substantiation: every assertion in a proposal must be backed by evidence the evaluator can independently verify."

6. **"What's the bid / no-bid threshold you committed to BEFORE seeing this RFP?"**
   Recommended: pre-committed threshold (e.g., winrate ≥ 25%, STRONG ≥ 70% on MANDATORY, named champion). Post-hoc rationalization is how teams end up bidding 5% pursuits.
   Canon: Bain RFP-win-rate studies — disciplined bid/no-bid gates lift win-rate from ~15% to ~35%.

7. **"What does the buyer's evaluation team actually score on?"**
   Recommended: if the RFP discloses scoring criteria, weight your response effort proportionally. If undisclosed, ask. If you can't ask, that itself is a relationship-deficit signal.
   Canon: Strategic Proposals proposal-management research — evaluators score on the rubric they were given, not on your narrative.

Walk depth-first. Lock 1-3 before opening 4-7. After all 7 are answered, invoke `rfp_parser.py` → `response_drafter.py` → `winrate_predictor.py` in sequence. If question 6 lands on "we don't have a threshold," set one now or no-bid.
