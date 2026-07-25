# Materials Figure Atlas

This atlas groups materials-science figures by research job, not by plotting
script. Use it before choosing individual plotting utilities.

## property-performance

Research job: show how a material variable changes an engineering property.

Typical metrics:

- strength
- viscosity
- thermal conductivity
- modulus
- water absorption

Recommended panels: grouped bar with error bars, line trend with confidence
band, stress-strain curve, conductivity-density scatter, retention plot.

Claim boundary: state the property, condition, and comparison group. Do not infer
mechanism unless a mechanism-evidence panel supports it.

## process-structure-property

Research job: connect processing parameter -> microstructure -> performance.

Required panel logic:

- processing parameter: dosage, curing temperature, sintering schedule, fiber
  orientation process, foaming condition
- microstructure: SEM, pore structure, XRD phase, fiber orientation, dispersion
- performance: strength, modulus, bonding, thermal conductivity, durability

Claim boundary: the figure may claim a process-structure-property association
only when all three elements appear in the storyboard.

## mechanism-evidence

Research job: show a mechanism evidence chain rather than a decorative mechanism
cartoon.

Accepted evidence anchors:

- FTIR
- XRD
- SEM
- DSC
- TGA

Common panel order: characterization signal -> microstructure or phase evidence
-> mechanism schematic -> property link.

Claim boundary: use "supports", "is consistent with", or "suggests" unless
direct causal controls are present.

## durability-aging

Research job: show property retention under service stress.

Typical stressors and metrics:

- aging
- freeze-thaw
- hygrothermal
- UV
- fatigue retention

Recommended panels: retention-vs-cycle curve, before/after microstructure,
water uptake, fatigue S-N trend, property radar after aging.

Claim boundary: identify the protocol, cycle count, humidity, temperature, UV
dose, or fatigue load ratio.

## comparison-window

Research job: identify a usable material-design window.

Typical formats:

- dosage window
- performance radar
- integrated scoring

Recommended panels: heatmap, radar, desirability score, Pareto window,
multi-objective trade-off plot.

Claim boundary: report the scoring weights and avoid calling the window
"optimal" outside the measured property set.

## review-evidence-map

Research job: synthesize literature evidence for a review or introduction.

Typical formats:

- research gap heatmap
- evidence-grade matrix
- screening flow

Recommended panels: PRISMA-like flow, taxonomy map, evidence certainty matrix,
gap heatmap, method-property map.

Claim boundary: distinguish evidence coverage from evidence certainty, and keep
caption claims aligned with the literature screening criteria.
