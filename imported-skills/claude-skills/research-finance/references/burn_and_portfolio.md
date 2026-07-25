# Burn, Runway, and R&D Portfolio Management

Reference for burn/runway tracking and risk-adjusted portfolio decisions. Pairs with `burn_runway_tracker.py`.

## Burn and runway done honestly

**Burn rate** is cash spent per period; **runway** is cash-on-hand ÷ forward run-rate. The honest forward run-rate is the **trailing** (recent-weighted) burn, not the lifetime average — averages mask both an accelerating spend and a funded ramp. The tracker uses trailing burn and flags when trailing exceeds 115% of the lifetime average (an acceleration signal). Runway must be measured against **value-inflection milestones**: cash that runs out one month before analytical validation is materially worse than the same runway that clears it, because reaching the milestone changes the program's financing options and valuation.

## Stage-gate portfolio management

Robert Cooper's **Stage-Gate** model structures R&D as a sequence of stages separated by go/kill **gates**. Each gate is a real-options decision: spend the next tranche, or kill and redeploy. The discipline is that money is committed one stage at a time, against pre-defined criteria — not as a lump sum at kickoff. This is why milestone-vs-cash alignment is the core runway question.

## Risk-adjusted valuation

Raw NPV systematically overstates R&D value because it ignores attrition. **Risk-adjusted NPV (rNPV)** weights each phase's cash flows by the cumulative probability of success of reaching it — in drug development, the product of per-phase success rates (which compound to single-digit percentages from preclinical to approval). **Real-options** valuation goes further, pricing the optionality of being able to abandon. For portfolio ROI, always state whether the number is raw NPV or risk-adjusted; the difference is often an order of magnitude.

## Efficiency benchmarks

Startup/SaaS efficiency frameworks (a16z's burn multiple, Bessemer's efficiency score) translate to R&D portfolios as "value created per dollar burned." They are blunt but useful for cross-program comparison when paired with milestone progress.

## Sources

1. Cooper, R.G., *Winning at New Products: Creating Value Through Innovation*, 5th ed. (2017) — Stage-Gate.
2. Stewart, Allison & Johnson, *Putting a price on biotechnology* — Nature Biotechnology 2001 (rNPV in drug development).
3. Trigeorgis, L., *Real Options: Managerial Flexibility and Strategy in Resource Allocation* (MIT Press).
4. DiMasi, Grabowski & Hansen, *Innovation in the pharmaceutical industry: New estimates of R&D costs* — J Health Econ 2016 (attrition / phase success rates).
5. a16z, *The burn multiple* and Bessemer State of the Cloud efficiency benchmarks.
6. Chan & Thornhill, *R&D portfolio management* — R&D Management literature.
