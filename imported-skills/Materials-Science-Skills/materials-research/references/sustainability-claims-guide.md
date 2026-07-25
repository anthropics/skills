# Sustainability Claims Guide

Use this guide when a manuscript mentions sustainability, low carbon, recycled materials, waste utilization, service-life extension, or environmental benefits. The goal is to make claims useful without overstating evidence.

## Decision Tree

1. Can the study perform a complete LCA?
   - Yes: follow ISO 14040/14044 logic, define software/database, functional unit, system boundary, allocation, impact categories, and uncertainty.
   - No: use a simplified mass-balance or literature-factor comparison, and label it as a screening estimate.
   - Not enough data: remove quantitative sustainability claims and keep only a cautious limitation/future-work sentence.

2. Is there a functional performance baseline?
   - Yes: compare environmental cost per functional unit, not per kilogram only.
   - No: do not say "greener" or "more sustainable"; say the material route has potential only if performance/service life is verified.

3. Does the modifier increase embodied carbon?
   - Yes: state the tradeoff explicitly and connect any benefit to service life, maintenance reduction, lower dosage, or waste diversion.
   - No evidence: flag `[needs carbon factor or LCA evidence]`.

## Minimum Evidence For Each Claim

| Claim | Minimum support | Safe wording |
|---|---|---|
| Low-carbon material | Functional unit, carbon factor source, system boundary, baseline | "may reduce carbon impact within the defined boundary" |
| Waste utilization | Waste source, replacement ratio, processing energy, performance retention | "uses waste-derived material while maintaining..." |
| Sustainable tack coat | 1 m2 application rate, material inventory, bonding performance, service-life logic | "may improve life-cycle performance if service-life extension is confirmed" |
| Recyclability | recycling process, recovered fraction, performance after reuse | "shows potential for recycling under..." |
| Service-life benefit | durability test, failure criterion, maintenance interval logic | "suggests possible maintenance reduction" |

## Simplified Screening Framework

Use this when full LCA software or database access is unavailable.

1. Define a functional unit, for example: `1 m2 of tack coat applied at 0.5 L/m2 and achieving >=0.5 MPa pull-off strength`.
2. List material inventory by dry mass or application volume: base asphalt, emulsifier, water, waterborne epoxy resin, curing agent, additives.
3. Record source and assumption for each emission factor. If the factor comes from literature or database examples, cite it and avoid inventing exact values.
4. Calculate mass share and carbon share separately. A low dosage material can dominate carbon share if its emission factor is high.
5. Compare against conventional emulsified asphalt under the same functional unit.
6. Add limitation language: database geography, transport excluded/included, curing energy, service-life uncertainty, and lab-to-field gap.

## Waterborne Epoxy Emulsified Asphalt Notes

- Waterborne epoxy can improve bonding, moisture resistance, and curing network formation, but epoxy resin normally increases embodied carbon relative to conventional emulsified asphalt.
- A credible sustainability argument should connect the higher material footprint to longer interlayer service life or reduced maintenance frequency.
- Do not claim environmental superiority from "waterborne" alone. Waterborne systems can reduce solvent-related concerns, but carbon and durability still need evidence.
- If only lab bonding data are available, frame sustainability as a hypothesis: improved bonding may reduce maintenance demand, but life-cycle verification is required.

## Manuscript Templates

Conservative screening statement:

> A simplified material-inventory comparison was conducted to screen the environmental implication of adding waterborne epoxy resin. The functional unit was defined as [functional unit]. Emission factors were obtained from [source], and transport, construction energy, and service-life extension were not included. Therefore, the analysis should be interpreted as a preliminary screening rather than a full life cycle assessment.

Tradeoff statement:

> The addition of waterborne epoxy resin increases the estimated material carbon footprint because epoxy resin has a higher emission factor than base emulsified asphalt. However, the improved bonding and moisture-conditioned strength suggest a potential service-life benefit. A full pavement life-cycle assessment is needed to confirm whether the performance gain offsets the higher initial material impact.

When to remove the claim:

> The present study does not include sufficient life-cycle inventory data to support a quantitative sustainability claim. The discussion has therefore been revised to focus on bonding performance and durability, while identifying life-cycle assessment as future work.

## Reviewer-Risk Checks

- If the word "green" appears, verify that the manuscript has a functional unit and quantified boundary.
- If the word "sustainable" appears, verify that tradeoffs and limits are stated.
- If recycled or waste material is used, verify that processing energy and performance loss are not ignored.
- If service-life extension is claimed, verify that durability evidence and failure criteria exist.
- If no LCA or screening calculation exists, replace strong sustainability claims with cautious future-work language.
