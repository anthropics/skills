---
name: macro-panel
description: Convene the macro-economist panel — run a market, asset, or portfolio question through multiple thinker-lenses at once and surface their AGREEMENT and DISAGREEMENT instead of one view. The panel is Lyn Alden (fiscal dominance/debasement/BTC), Ray Dalio (debt cycles/world order/all-weather), Stanley Druckenmiller (liquidity/timing/sizing), Lacy Hunt (deflation dissent), Michael Pettis (trade/capital-flows/China), Russell Napier (financial repression), and Warren Buffett (bubble-discipline/quality-value). Use when the user asks "what does the panel think", "run the macro team on this", "convene the economists", "get multiple macro views", "where do the economists agree/disagree", or wants a debated, multi-perspective macro/asset call rather than a single lens. Routes to the individual analytics-* skills; this skill is the conductor, not a replacement for them. Educational, not advice.
license: MIT
compatibility: opencode
metadata:
  audience: macro-investors
  domain: macro-and-asset-strategy
  role: panel-conductor
  source: composes the analytics-* thinker skills (assembled 2026-06-07)
---

# Macro Panel — Convene the Team

Run a question through several thinker-lenses and report the **debate**, not a single answer. The value
is the *disagreement*: when seven independent frameworks converge, that's signal; where they split, that
names the real risk. This skill is the **conductor** — it routes to the individual `analytics-*` skills,
which hold the actual frameworks and primary sources.

## The panel (seven seats, chosen for non-overlapping return-drivers)

| Seat | Skill | The lens it brings | Bias / tell |
|---|---|---|---|
| Debasement / monetary-system | `analytics-lyn-alden` | Fiscal dominance, broad money, eurodollar, BTC-as-hurdle, energy | Structurally inflationist; pro scarce assets/BTC |
| Cycle architect / portfolio | `analytics-ray-dalio` | Big debt cycle, changing world order, all-weather/risk-parity | Late-cycle; balance risk, hold gold; can be early |
| Tactician / timing & sizing | `analytics-stanley-druckenmiller` | Liquidity drives markets; position 12-24mo out; bet big/rarely | Liquidity-first; turns views into trades |
| **Deflation dissent** | `analytics-lacy-hunt` | Debt → low velocity → disinflation; long bonds | **The designed contrarian**; bond bull (reversed 2026) |
| Trade / China | `analytics-michael-pettis` | S−I=CA, capital account drives trade, China rebalancing | Imbalances = distribution; China-bear, early |
| Financial repression | `analytics-russell-napier` | Govts control money via bank credit; structural 4-6% inflation | Inflationist via repression; flips early |
| Bubble-discipline / value | `analytics-warren-buffett` | Circle of competence, moats, margin of safety, cash-as-option | Bottom-up; hold cash when rich; ignores macro |

## How to convene (procedure)

1. **Pick the relevant seats — don't always run all seven.** Map the question to lenses (table below).
   Most questions need 3-5 seats; running an irrelevant lens adds noise. Always include at least one
   seat likely to *disagree* (the panel's whole point).
2. **Load each chosen skill's SKILL.md + the matching reference**, and produce that thinker's view in
   1-3 sentences, grounded in their framework (not a caricature). Keep each seat in its own voice.
3. **Build the consensus/divergence map.** Explicitly state: where do they AGREE (convergence = higher
   confidence), and where do they SPLIT — and *why* (which assumption differs). Name the load-bearing
   disagreement.
4. **Give the synthesis,** but preserve the dissent — do not average them into mush. State what you'd
   conclude, what would change your mind, and which seat you'd watch for the early warning.
5. **Time-stamp tactical claims.** Each thinker's "current" view decays — flag and re-check against
   their `05-current-views.md` / latest newsletter.

## Routing — which seats for which question

| Question is about… | Convene |
|---|---|
| Inflation vs deflation, rates, "is the debasement trade right" | Alden + Napier vs **Hunt** (+ Dalio) — the core inflation debate |
| Should I buy/size BTC or a risk asset today | Druckenmiller (timing/liquidity) + Alden (BTC-hurdle) + Buffett (cash/discipline) |
| US debt / deficits / "can the US go broke" | Dalio + Alden + Napier vs **Hunt** |
| The dollar, reserve status, de-dollarization | Pettis + Alden + Dalio |
| China, tariffs, trade war, global imbalances | **Pettis** (lead) + Dalio (world order) |
| Is this an equity bubble / what to do with cash | **Buffett** (lead) + Dalio (cycle) + Druckenmiller (liquidity) |
| Portfolio construction / how to position a large book | Dalio (all-weather) + Buffett (cash) + Alden (scarce assets) + Hunt (duration dissent) |
| Generational market bottom / when to deploy | Napier (anatomy of the bear) + Druckenmiller (turn) + Buffett (greedy-when-fearful) |

## Example

<example>
User: "Run the panel: is now a good time to add long-term Treasuries?"

Panel (convene Hunt, Napier, Alden, Dalio, Druckenmiller):
- **Hunt (dissent/bond bull):** historically yes — debt crushes growth and velocity, long yields track
  trend nominal GDP downward... BUT note he himself reversed in May 2026 (cut duration <1yr, >4% CPI
  call), which is the tell.
- **Napier:** no — financial repression means negative real rates *by policy*; the long-bond holder is
  the captive creditor being inflated away.
- **Alden:** no — debasement regime; underweight long-duration developed-market sovereigns, own scarce
  assets.
- **Dalio:** no — late big-debt-cycle, the risk to Treasuries is devaluation; hold balanced risk + gold.
- **Druckenmiller:** only as a *tactical* trade if liquidity is about to ease into a slowdown — not a
  structural hold; he's been bearish long bonds on the fiscal thesis.

**Consensus:** 4 of 5 say no to a *structural* long-Treasury position; even the bond bull (Hunt) just
capitulated. **Divergence:** the only case *for* is Druckenmiller's tactical 'liquidity-easing-into-
recession' trade and Hunt's (now abandoned) secular view — i.e. duration is a *trade*, not an
*investment*, in this regime. **Synthesis:** avoid as a core holding; if you want it, size it small and
tactical with a liquidity trigger. Watch Hunt's reversal — if even the deflationist is now inflation-
worried, the structural case for long bonds is at its weakest. (Time-stamped 2026-06; re-check each
seat's current view.)
</example>

## Honesty rules

- **Preserve disagreement; never average it away.** A split panel is a feature — report it as risk.
- **Each lens is a lens, not gospel;** carry each thinker's caveats (they have all been wrong/early).
- **Don't strawman a seat** to manufacture consensus — give each its strongest form.
- **Ground each view** in that skill's reference + primary source; time-stamp every "current" claim.
- This skill **composes** the `analytics-*` skills and complements `fundamental-analysis` /
  `hedge-fund-13f-analysis`; it informs `regime-detection` / `portfolio-construction`. It does not
  replace the backtest/valuation gate or your own judgment.

## Done when

The output (1) convenes the *relevant* seats (incl. at least one likely dissenter), (2) gives each its
grounded view in its own voice, (3) maps explicit agreement vs disagreement with the reason for the
split, (4) synthesizes without erasing the dissent, and (5) time-stamps tactical claims.
