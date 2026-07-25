# Product Operating Model, Metrics & Prioritization Brackets

The strategy layer behind the orchestrator's STRATEGY/ANALYTICS/PRIORITIZE forcing
questions. Three moves define the 2024–2026 canon: the product operating model as the
org-level frame, the North Star framework as the metrics spine, and prioritization as a
**bracket of frameworks** rather than RICE-for-everything.

## The product operating model (Cagan, *Transformed*, 2024)

The transformation agenda in three principles: **empowered teams** (problems to solve,
not features to build), **outcomes over output**, **innovation over predictability** —
elaborated as 20 first principles across how you build / solve problems / decide what to
work on. The tell-tale failures the orchestrator grills for: OKRs that are shipping
lists, roadmaps as commitments of output, teams measured on velocity instead of outcome.

## North Star framework (Amplitude)

A valid North Star Metric is (a) a **leading indicator** of sustainable business results,
(b) a measure of **value exchange** with the customer, (c) not revenue and not a vanity
count. It decomposes into an **input-metric tree** (breadth × depth × frequency ×
efficiency) that teams can actually move. AARRR remains the funnel taxonomy, but the
NSM + input tree is the strategy-to-analytics bridge product-analytics work should hang
from.

## PLG benchmark bands

Verdicts need bands, not vibes (medians from ProductLed/OpenView benchmark corpora,
2024–2025): signup→activation median ≈ 17% (best-in-class 33–50%+); free→paid median
≈ 9% (PQL-driven motions 25–30%). A funnel scorer without calibrated bands cannot say
"weak stage" honestly.

## Prioritization: bracket RICE, don't replace it

| Situation | Framework | Why |
|---|---|---|
| Steady-state backlog | **RICE** | Reach/impact/confidence/effort — cheap, comparable |
| Time sensitivity dominates (deadlines, market windows) | **WSJF / Cost of Delay** (Reinertsen) | RICE is time-blind; CoD/duration surfaces value erosion |
| Underserved-needs hunting | **Opportunity scoring** (Ulwick ODI) | importance + max(importance − satisfaction, 0) ranks unmet outcomes |

Two disciplines regardless of framework: (1) **name which framework and why** before
scoring; (2) **sensitivity-check the ranking** — perturb each estimate one step and flag
items whose rank flips (the documented WSJF false-precision failure; SAFe's own critics'
point). `rice_prioritizer.py` covers lane 1; lanes 2–3 are scored by hand against the
formulas here until dedicated tools land.

## Event taxonomy governance (PostHog/Amplitude-era)

Analytics rot starts at instrumentation: enforce snake_case, present-tense verb
allowlists, object_verb ordering, compact event sets, and tracking-plan review before
new events ship. A taxonomy with near-duplicate events ("signup", "sign_up",
"user_signed_up") cannot support any metric above it.

## Sources

1. Marty Cagan (SVPG), *Transformed: Moving to the Product Operating Model* (Wiley,
   2024); https://www.svpg.com/the-product-operating-model-an-introduction/
2. Amplitude, *The North Star Playbook* —
   https://amplitude.com/books/north-star/about-north-star-framework
3. ProductLed, "Product-Led Growth Benchmarks" —
   https://productled.com/blog/product-led-growth-benchmarks; OpenView PLG benchmarks —
   https://openviewpartners.com/blog/your-guide-to-product-led-growth-benchmarks/
4. Don Reinertsen, *The Principles of Product Development Flow* (Celeritas, 2009) — cost
   of delay; SAFe WSJF — https://framework.scaledagile.com/wsjf
5. Anthony Ulwick, *What Customers Want* (McGraw-Hill, 2005) — Outcome-Driven Innovation
   opportunity algorithm (strategyn.com)
6. Jason Yip, "Problems I have with SAFe-style WSJF" —
   https://jchyip.medium.com/problems-i-have-with-safe-style-wsjf-772df2beaf02
7. PostHog, product analytics best practices —
   https://posthog.com/docs/product-analytics/best-practices
