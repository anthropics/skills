# Ceramics — Writing Guide

Loaded automatically when the domain is ceramic materials (structural ceramics, functional ceramics, refractories, bioceramics).

## Domain narrative arc

The strongest arc for ceramics manuscripts follows a **processing-structure-property-performance** logic:

1. Application context: why ceramics are chosen (high-temperature stability, wear resistance, biocompatibility, dielectric/piezoelectric function).
2. Material limitation: brittleness, processing cost, difficulty in fabricating complex shapes, or property trade-offs (strength vs. toughness, density vs. porosity).
3. Design strategy: composition design, sintering optimization, additive/dopant selection, or processing route (SPS, HP, slip casting, 3D printing).
4. Processing evidence: sintering curve, densification behavior, phase evolution.
5. Microstructure evidence: grain size, grain boundary phase, porosity, second phase (SEM, TEM, XRD).
6. Property evidence: mechanical, thermal, electrical, or biological performance.
7. Boundary: reproducibility, scaling, or in vivo / in-service validation needs.

## Key evidence chain

Powder/forming → sintering (T, t, atmosphere, ramp) → density/porosity → phase → microstructure → mechanical/functional properties

Sintering conditions (temperature, dwell time, heating rate, atmosphere) must be reported with precision. Density is the most fundamental quality indicator.

## Section guidance

### Introduction
- Frame the ceramic class by its application function, not its chemistry alone.
- The limitation should be processing-related or property-related.
- Gap: what composition or processing window has not been explored.

### Methods
- Report raw material purity, particle size, and source.
- Forming method: pressure, binder, green density.
- Sintering: furnace type, heating rate, target temperature, dwell time, cooling rate, atmosphere.
- Density measurement method (Archimedes, geometric) and theoretical density reference.
- Mechanical test standards, specimen geometry, loading conditions, number of specimens.

### Results
- Density and phase (XRD) first—without dense ceramics, property data is meaningless.
- Microstructure: grain size, porosity distribution, grain boundary phase.
- Mechanical: hardness, strength, toughness (with Weibull statistics for brittle ceramics).
- Functional: dielectric, thermal, optical, or biological properties in logical order.

### Discussion
- Connect sintering parameters to densification and microstructure evolution.
- Explain property trends through microstructural mechanisms.
- Compare with literature values for similar compositions processed differently.

### Conclusion
- State the composition, processing window, and achieved density-property combination.
- Note limitations: specimen size effect, surface finish influence, long-term performance.
- Avoid: "promising candidate for application" without specifying the performance threshold required.

## Reviewer-sensitive points in ceramics

- ⚠️ Mechanical properties reported without density or porosity data.
- ⚠️ Weibull modulus claimed without sufficient specimen numbers (minimum 10, preferably 30).
- ⚠️ Sintering temperature reported without heating rate or dwell time.
- ⚠️ Phase identification by XRD without reference pattern or Rietveld quantification.
- ⚠️ "High toughness" claimed for a ceramic without valid KIC measurement method.

## Common pitfalls

| Pitfall | Example | Fix |
|---|---|---|
| Ignoring porosity | comparing strength without reporting relative density | Always report density alongside properties |
| Insufficient statistics | 3 specimens for Weibull analysis | Minimum 10 specimens per condition |
| Mislabeling sintering | "sintered at 1500°C" without ramp/dwell details | Report full sintering profile |
| Overclaiming bioactivity | "bioactive" based on in vitro test only | Specify test conditions and cell type |
