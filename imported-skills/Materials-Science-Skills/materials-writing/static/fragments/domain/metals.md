# Metals and Alloys — Writing Guide

Loaded automatically when the domain is metallic materials (ferrous alloys, non-ferrous alloys, high-temperature alloys, additive metals).

## Domain narrative arc

The strongest arc for metals manuscripts follows a **composition-processing-microstructure-property** logic:

1. Application context: where this alloy class is used and what performance is demanded.
2. Material limitation: the classical trade-off (strength vs. ductility, strength vs. weldability, corrosion resistance vs. cost).
3. Design strategy: microalloying, thermomechanical processing, heat treatment, or additive manufacturing parameter selection.
4. Microstructure evidence: grain size, phase fraction, precipitate distribution, texture (OM, SEM, EBSD, TEM, XRD).
5. Mechanical/environmental performance: tensile, impact, fatigue, creep, corrosion, wear.
6. Boundary: scalability, cost, welding/joining requirements, or service environment limits.

## Key evidence chain

Composition/processing → microstructure (grain, phase, precipitate, texture) → mechanical properties → application performance → environmental durability

Microstructure characterization (minimum OM + SEM) is essential for any mechanism claim in metals.

## Section guidance

### Introduction
- Establish the alloy class and its current performance envelope.
- Identify the specific microstructural limitation (coarse grain, unwanted phase, precipitate-free zone).
- The gap should be: "the effect of [variable] on [microstructural feature] under [condition] is not understood."

### Methods
- Report full processing history: composition (wt%), melting/casting method, deformation ratio, heat treatment (temperature, time, cooling rate).
- For AM metals: build parameters (laser power, scan speed, layer thickness, hatch spacing, build orientation).
- Specify test standards and specimen orientation relative to processing direction.

### Results
- Microstructure first (grain, phase, precipitate), then mechanical properties, then application-specific tests.
- Report both strength and ductility—never strength alone.
- Include fracture surface analysis (SEM fractography) for mechanical tests.

### Discussion
- Connect processing parameters to microstructure evolution, then microstructure to properties.
- Use established strengthening models where applicable (Hall-Petch, Orowan, solid solution).
- Compare with standard grades and explain why your results differ.

### Conclusion
- State the composition, processing window, and resulting microstructure-property combination.
- Include limitations: scaling from lab to industry, welding concerns, anisotropy.
- Do not claim "industrial applicability" without addressing cost or scalability.

## Reviewer-sensitive points in metals

- ⚠️ Strength improvement without ductility or toughness data.
- ⚠️ "Grain refinement" claimed without quantitative grain size measurement.
- ⚠️ Fracture mechanism claimed without fractography.
- ⚠️ Corrosion improvement without standard test method or exposure conditions.
- ⚠️ Heat treatment reported without cooling rate (the most critical parameter).

## Common pitfalls

| Pitfall | Example | Fix |
|---|---|---|
| Strength-only reporting | "UTS improved by 30%" without elongation change | Report full tensile curve |
| Missing anisotropy | testing only along rolling direction | Test transverse and longitudinal |
| Texture ignored | property anisotropy observed but no EBSD/XRD texture data | Include texture measurement or at least acknowledge |
| Overclaiming "novel alloy" | minor composition variation called a new alloy | Compare with existing grades; specify improvement margin |
