---
name: research-finance
description: Use when managing the money for an internal R&D program or portfolio — building a multi-period program budget with the F&A (indirect) split, tracking burn rate and runway against value-inflection milestones, or routing R&D cost items to a capitalize-vs-expense determination. Every budget output surfaces its assumptions block; capitalize-vs-expense is decision-support only and routes to a named finance owner — it never books an entry or decides accounting treatment. Distinct from finance/financial-analysis (corporate DCF, close, valuation) and research/grants (funding discovery — this manages money already won).
version: 2.9.0
author: claude-code-skills
license: MIT
tags: [research-ops, research-finance, rd-budget, burn-rate, runway, fa-rate, capitalize-vs-expense, portfolio]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# research-finance

Financial management of internal R&D programs and portfolios: program budgeting with F&A, burn/runway tracking, and capitalize-vs-expense routing. Every number ships with its **assumptions block**, and accounting-treatment calls **route to a named finance owner** — this skill never books an entry.

## Purpose

R&D finance partners, program controllers, and operations leads manage money that has already been allocated or raised — not the corporate close, not the next funding round, not finding a grant. This skill structures three recurring decisions:

Three deterministic tools:

1. `program_budget_planner.py` — Builds a multi-period budget from work-package line items, applies the F&A (indirect) rate to an MTDC-style eligible base, and rolls up direct / F&A / fully-loaded cost per period with an explicit assumptions block.
2. `burn_runway_tracker.py` — Computes average + trailing burn, runway in periods/months, and whether each value-inflection milestone is reachable before cash runs out. Flags accelerating burn and below-threshold runway.
3. `capex_vs_opex_router.py` — Scores each R&D cost item against the IAS 38 development-phase criteria (or flags US GAAP ASC 730 expense-as-incurred) and routes it to **CAPITALIZE-CANDIDATE / EXPENSE / FINANCE-OWNER-REVIEW** with a named owner. Never auto-decides.

## When to use

Invoke this skill when:

- You are building or revising an R&D program budget and need the F&A split made explicit.
- A program's runway is in question and you need a milestone-vs-cash read.
- Finance asks whether a development cost can be capitalized and you need a defensible first routing.
- You are preparing a portfolio review and need per-program burn consistency.

**Do NOT use this skill to**: run corporate DCF / valuation / close (use `finance/financial-analysis`), discover or position grants (use `research/grants`), or make the final accounting determination (that is the controller's + auditor's call — this tool only routes).

## Workflow

1. **Lay out the program** — Fill `assets/rd_program_budget_template.md` with work-package lines, categories, and per-period amounts.
2. **Build the budget** — Run `program_budget_planner.py --input program.json --profile {pharma-rd|biotech|medtech|deep-tech|software-rd|university-lab} --fa-rate <negotiated rate>`. Read direct / F&A / fully-loaded rollups + assumptions.
3. **Track burn & runway** — Run `burn_runway_tracker.py --input ledger.json --threshold-months 6`. Read runway + milestone verdicts + flags.
4. **Route accounting treatment** — Run `capex_vs_opex_router.py --input costs.json --standard {ifrs|usgaap}`. Read the per-item routing; send CAPITALIZE-CANDIDATE and FINANCE-OWNER-REVIEW items to the named owner.
5. **Assemble the review** — Combine into a program-finance packet. Every number carries its assumptions; treatment calls carry a named owner.

## Scripts

| Script | Purpose | Profiles |
|---|---|---|
| `scripts/program_budget_planner.py` | Multi-period budget + F&A split + assumptions | pharma-rd, biotech, medtech, deep-tech, software-rd, university-lab |
| `scripts/burn_runway_tracker.py` | Burn, runway, milestone-vs-cash alignment | n/a (ledger-driven) |
| `scripts/capex_vs_opex_router.py` | IAS 38 / ASC 730 routing to named finance owner | pharma-rd, biotech, medtech, deep-tech, software-rd, university-lab |

All three: stdlib-only, `--help`, `--sample`, `--output {human,json}`.

## Onboarding & customization

Run the onboarding questionnaire **once before you start** — it captures your defaults so every tool in this skill is pre-configured. Customization is the point: the answers actually change tool behavior.

```bash
python3 scripts/onboard.py            # interactive (also: --defaults, --set key=value, --reset)
python3 scripts/onboard.py --show     # see the questions + current effective config
```

Answers are saved to `~/.config/research-ops/research-finance.json` (global) or `./.research-ops/research-finance.json` (`--scope project`) and are read automatically by `config_loader.py`. They set the default R&D-area **profile**, the default **F&A rate**, the **runway alert threshold**, the **accounting standard**, and the named **finance owner** printed on capitalize-vs-expense routing. CLI flags always override saved config; `RESEARCH_OPS_NO_CONFIG=1` ignores it.

**The five questions:** R&D area · F&A rate · runway threshold · accounting standard · finance owner.

## Optimize with autoresearch (opt-in)

This skill ships an **isolated, opt-in** bridge to `engineering/autoresearch-agent`. Only when you ask to "optimize" / "extend runway" / "run a loop" does an autoresearch experiment iteratively improve a program plan against this skill's runway metric. `scripts/ar_evaluator.py` is the ground-truth evaluator; it prints `runway_months: <float>` (higher is better).

```bash
/ar:setup --domain custom --name extend-runway \
  --target ledger.json \
  --eval "python3 ar_evaluator.py --target ledger.json" \
  --metric runway_months --direction higher
/ar:loop custom/extend-runway
```

Isolated: no hard dependency — autoresearch runs only on demand, and the loop edits `ledger.json`, never the evaluator.

## References

- `references/rd_program_finance_canon.md` — IAS 38 (research vs development); ASC 730 + ASC 985-20; Uniform Guidance 2 CFR 200 (F&A); FASB/IFRS capitalization criteria; NICRA basics.
- `references/burn_and_portfolio.md` — Cooper stage-gate; rNPV / real-options for R&D; risk-adjusted portfolio ROI; burn-rate / runway frameworks; milestone-based budgeting.
- `references/indirect_rate_modeling.md` — F&A pool composition (facilities + administration); MTDC base; de minimis 10%; fringe/overhead loading; CAS primer.

## Assumptions

- The F&A rate is the most error-prone input. The planner applies whatever rate you pass; it warns you to confirm it is a negotiated NICRA, not a guess.
- Burn/runway uses the trailing (recent-weighted) burn as the forward run-rate and assumes flat forward spend unless your ledger encodes a ramp.
- The capex router asserts criteria from your input; asserting "technical feasibility" does not make it true — the named finance owner and auditor validate it.
- Profiles annotate context (e.g., "most drug R&D is expensed") but do not change the accounting test.

## Anti-patterns

- **Stating a budget number without its assumptions.** F&A rate, escalation, and base must travel with the number.
- **Auto-deciding capitalize-vs-expense.** This tool routes; the controller (and auditor where required) decides.
- **Using lifetime-average burn for runway.** Recent burn is the honest forward run-rate; averages hide a slowdown or a ramp.
- **Applying F&A to the full base.** Capital equipment, large subaward portions, and certain categories are MTDC-exempt.
- **Confusing this with corporate finance.** Valuation, close, and fundraising live in `finance/`.

## Distinct from

| Sibling / neighbor | Scope | Difference |
|---|---|---|
| `finance/financial-analysis` | Corporate DCF, ratios, close, rolling forecast, SaaS metrics | That is **company-level**; this is **R&D-program-level** |
| `research/grants` | NIH funding discovery + positioning | That **finds funding**; this **manages money already won** |
| `clinical-research` (sibling) | Study design + feasibility + budget gate-check | That **scopes** the study; this **funds + tracks** the program |
| `ra-qm-team` | Regulatory/QM submission | Unrelated — no financial scope |

## Quick examples

```bash
python3 scripts/program_budget_planner.py --sample
python3 scripts/program_budget_planner.py --input program.json --profile university-lab --fa-rate 0.585
python3 scripts/burn_runway_tracker.py --sample --output json
python3 scripts/capex_vs_opex_router.py --sample --standard ifrs
```

The sample budget excludes the sequencer (capital equipment) and CRO subaward from the F&A base; the capex router routes exploratory screening to EXPENSE, a fully-criteria'd pilot line to CAPITALIZE-CANDIDATE, and a partial-criteria software build to FINANCE-OWNER-REVIEW.

## Forcing-question library (Matt Pocock grill discipline)

Walked one at a time by `/cs:grill-research-ops` or the orchestrator. Recommended answer + canon citation per question. Never bundled.

1. **"Is this spend in the research phase or the development phase — and can you evidence technical feasibility?"**
   Recommended: research = expense; development = capitalize-candidate only with feasibility evidence, routed to a named finance owner.
   Canon: IAS 38.54-57; ASC 730.

2. **"What F&A / indirect rate are you applying, and is it your negotiated NICRA, a de minimis 10%, or an assumption?"**
   Recommended: use the negotiated rate; if assumed, flag it explicitly.
   Canon: 2 CFR 200 (Uniform Guidance); NICRA basics.

3. **"What's runway in months at current burn, and does it clear the next value-inflection milestone?"**
   Recommended: runway must cover the milestone plus a buffer; surface the gap.
   Canon: Cooper stage-gate; SaaS/startup efficiency frameworks (a16z, Bessemer).

4. **"Is portfolio ROI risk-adjusted (rNPV / probability-of-success weighted) or raw NPV?"**
   Recommended: risk-adjusted; raw NPV overstates R&D value.
   Canon: rNPV drug-development valuation; real-options literature.

5. **"Who is the named finance / controller owner who signs the capitalize-vs-expense treatment?"**
   Recommended: name them — this tool recommends, it never books the entry.
   Canon: ASC 730 / IAS 38 governance; auditor sign-off requirements.

Walk depth-first. Lock 1-2 before opening 3-5. After all are answered, invoke `program_budget_planner.py` → `burn_runway_tracker.py` → `capex_vs_opex_router.py`.
