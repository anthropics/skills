---
name: research-ops-skills
description: Use when planning, funding, scoping, or synthesizing enterprise research across workstreams — clinical study design, R&D program finance, market sizing/surveys, or product/user research. Triggers on "design this clinical study", "what sample size", "R&D budget", "burn rate", "capitalize or expense", "TAM SAM SOM", "market sizing", "survey design", "segment the market", "plan user interviews", "usability test", "synthesize research insights". Forks context to route to one of four Research-Operations sub-skills (clinical-research, research-finance, market-research, product-research) and returns a digest. Distinct from ra-qm-team (regulatory submission), finance (corporate close/valuation), research/grants (funding discovery), product-team (persona/journey/live experiments), and marketing-skill (campaign analytics).
context: fork
version: 2.9.0
author: claude-code-skills
license: MIT
tags: [research-ops, clinical-research, research-finance, market-research, product-research, rd, orchestrator]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# Research Operations — Domain Orchestrator

The Research Operations surface is **how the enterprise plans, funds, scopes, and synthesizes research** across four workstreams: clinical R&D, R&D finance, market research, and product research. This orchestrator forks its context, routes your inquiry to one of four sub-skills, then returns a digest. Heavy intake (protocol drafts, program ledgers, survey exports, interview transcripts) stays in the forked context.

This is the enterprise counterpart to the academic `research/` domain. If your question is about **finding** literature, grants, or patents, use `research/`. If it is about **planning, funding, scoping, or synthesizing** research as an operational discipline, you are in the right place.

## When to invoke

| Symptom | Sub-skill |
|---|---|
| "We're designing a Phase 2 trial — what's the endpoint and sample size?" | `clinical-research` |
| "What's our R&D program burn, and is this cost CapEx or OpEx?" | `research-finance` |
| "What's the TAM for this product, and how do we survey the segment?" | `market-research` |
| "How many users do we interview, and how do we synthesize the findings?" | `product-research` |

## Routing logic (deterministic)

Same two-signal threshold pattern as `commercial-skills`. Single-signal → clarifying question. Mixed signals → highest-confidence first, chain second in a follow-up turn. Never silently chain.

### Signal table

| Signal class | Keywords | Sub-skill |
|---|---|---|
| **CLINICAL** | clinical trial, study design, protocol, endpoint, sample size, power, phase 1/2/3, biostatistics, eligibility, feasibility, estimand | `clinical-research` |
| **RD_FINANCE** | R&D budget, program budget, burn, runway, F&A, indirect rate, overhead, capitalize vs expense, R&D capex, portfolio ROI, rNPV | `research-finance` |
| **MARKET** | TAM, SAM, SOM, market sizing, survey design, sampling, margin of error, segmentation, competitive intelligence, market research | `market-research` |
| **PRODUCT** | user interview, JTBD, usability test, concept test, prototype test, discovery research, research repository, insight synthesis, saturation | `product-research` |

## Workflow (Matt Pocock grill discipline)

Derived from Matt Pocock's `grill-with-docs` pattern: **explore-then-ask, one question per turn with a recommended answer, walk the decision tree depth-first, track dependencies, anchor every challenge in the research canon** (`references/` of each sub-skill).

### Step 1 — Explore before asking

Check the user's working directory first:
- Is there a protocol draft, program ledger, TAM model, or interview guide already in the workspace?
- Does the inquiry already disambiguate the lane (e.g., "what sample size for a two-arm trial" — that's `clinical-research`, no question needed)?
- Is there an artifact filename that resolves the lane (`protocol.json` → clinical; `program-budget.json` → finance; `tam-model.json` → market; `interview-guide.md` → product)?

If the workspace resolves the lane, **route silently**.

### Step 2 — If still ambiguous, ONE forcing question with a recommended answer

Matt's rule: never bundle. Always recommend.

Pattern:
```
Q1/1: [precise question naming the two candidate lanes]
Recommended: [Lane X, because <signal-table rationale>]

(Confirm, or override?)
```

### Step 3 — Decision-tree walk for multi-lane inquiries

If the inquiry legitimately crosses two lanes (e.g., "design this trial AND budget it" = CLINICAL + RD_FINANCE), walk depth-first:

1. Highest-confidence lane first → run sub-skill in forked context → digest
2. Ask: "Now run [second lane]? Recommended: yes, because [dependency]."
3. Confirm before chaining.

Never silently chain.

### Step 4 — Invoke sub-skill in forked context

Forward original prompt + structured inputs (protocol JSON, program ledger CSV, market model, observation export).

### Step 5 — Return digest with cited canon challenge

≤ 200 words: analyzed, top 3 findings (anchored to a canon citation), top 3 next actions (named human owner where applicable), artifact path, and **one grill challenge** for the user. Examples:

- "Your power calc assumes a 0.5 effect size with no published anchor. ICH E9 requires a justified, clinically meaningful difference. Where did 0.5 come from?"
- "Your TAM is a single top-down number (1% of a $40B market). Bessemer market-sizing discipline requires a bottoms-up cross-check. What's units × price × adoption?"

## Forcing-question library (grill-with-docs pattern)

Grill the user on lane-defining decisions before invoking the sub-skill. One per turn, recommended answer, canon citation:

- **CLINICAL lane**: "Is your primary endpoint a clinical outcome or a surrogate — and if surrogate, is it validated for this indication? Recommended: clinical outcome unless the surrogate is on FDA's validated table. Canon: FDA Surrogate Endpoint Table; BEST glossary."
- **RD_FINANCE lane**: "Is this spend in the research phase or the development phase, and can you evidence technical feasibility? Recommended: research = expense; development = capitalize-candidate only with feasibility evidence, routed to a named finance owner. Canon: IAS 38; ASC 730."
- **MARKET lane**: "Is your TAM top-down or bottoms-up — and have you computed it both ways to triangulate? Recommended: both; reconcile the delta. Canon: Bessemer / a16z market-sizing; Fermi estimation."
- **PRODUCT lane**: "Is this study generative (discover problems) or evaluative (test a solution)? Recommended: name it first; the method follows. Canon: Rohrer's landscape of UX research methods (NN/g)."

Never run a sub-skill until the lane-defining decision is locked.

## Onboarding-first (per sub-skill)

Before invoking a sub-skill for the first time in a workspace, point the user at that skill's onboarding questionnaire so the tools run pre-configured to their context:

```bash
python3 skills/<sub-skill>/scripts/onboard.py          # interactive Q&A
python3 skills/<sub-skill>/scripts/onboard.py --show    # questions + current config
```

Each sub-skill has its **own** question set (clinical: area/alpha/power/dropout/owners · finance: area/F&A/runway/standard/owner · market: profile/confidence/MoE/method · product: profile/insight-threshold/method/stakes). Answers persist to `~/.config/research-ops/<sub-skill>.json` (or `./.research-ops/<sub-skill>.json` with `--scope project`) and are consumed automatically by every tool in that skill. Customization is mandatory discipline here, not decoration — surface the onboarding step when a user starts a fresh research workstream.

## Autoresearch handoff (isolated, opt-in)

Each sub-skill ships its own `skills/<sub-skill>/scripts/ar_evaluator.py` — an **isolated** bridge to `engineering/autoresearch-agent`. Invoke autoresearch **only when the user explicitly asks** to "optimize", "improve", or "run a loop". The handoff is per-skill (no shared coupling): the loop edits the skill's input file and the evaluator scores it (clinical → `feasibility_composite` higher; finance → `runway_months` higher; market → `tam_divergence` lower; product → `validated_insights` higher). Never auto-start a loop; never let the loop edit the evaluator.

## Assumptions

1. User has research authority OR is preparing analysis for someone who does.
2. User wants **deterministic decision support**, not the final answer — a clinician approves the protocol, a controller books the entry, the human picks the market number.
3. Inputs may be partial — every sub-skill ships a templated sample so the user can see the shape before filling in their own.

## Non-goals

- Not an EDC, clinical-trial-management system, accounting system, survey platform, or research repository.
- Does not give clinical, accounting, or legal advice as fact. Every output is **a recommendation + named human owner**.
- Does not store research history across sessions.

## Distinct from

- **`research/` (academic)** — that domain **finds** literature, grants, and patents. This domain **plans, funds, scopes, and synthesizes** research.
- **`ra-qm-team`** — that's **regulatory/QM submission** (ISO 13485/14971, MDR, FDA 510(k)/PMA/QSR). clinical-research designs the **study**; it routes submission out to ra-qm-team.
- **`finance/financial-analysis`** — that's **corporate close + valuation**. research-finance manages **R&D program/portfolio spend**.
- **`research/grants`** — that's **funding discovery**. research-finance manages **money already won**.
- **`product-team`** — that's **persona/journey artifacts, discovery sprints, and live A/B experiments**. product-research is the **method + repository discipline**.
- **`marketing-skill`** — that's **campaign analytics and demand-gen**. market-research is **upstream methodology**.

## Output artifacts

| Sub-skill | Artifact |
|---|---|
| clinical-research | `protocol_synopsis.md` + `sample_size.json` |
| research-finance | `rd_program_budget.md` + `capex_opex_routing.json` |
| market-research | `market_sizing.md` + `sample_plan.json` |
| product-research | `research_plan.md` + `insight_synthesis.json` |

## Anti-patterns (do not)

- ❌ Present a clinical power/endpoint output as fact — it is an **estimate** with a named clinical owner
- ❌ Auto-decide capitalize-vs-expense — route to a **named finance owner**
- ❌ Report a market size as a single unsourced number — show **method + both-ways triangulation + assumptions**
- ❌ Assert a product insight from a single participant — flag it as an **anecdote**
- ❌ Run all 4 sub-skills "to be thorough" — pick one, digest, chain if needed

## References

- Clinical canon: ICH E8(R1)/E9/E9(R1), CONSORT, SPIRIT, FDA Multiple Endpoints
- R&D finance canon: IAS 38, ASC 730, 2 CFR 200, Cooper stage-gate
- Market canon: Cochran, Dillman, Kotler, Bessemer market-sizing
- Product canon: Nielsen, Guest et al., Christensen JTBD, ResearchOps/Polaris
- Path-B build pattern: `documentation/implementation/research-ops-expansion-plan.md`
