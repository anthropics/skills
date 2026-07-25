# Ceramics Figure Atlas

A curated library of reusable figure archetypes for ceramics manuscripts. Each entry includes the recommended figure type, data requirements, caption pattern, and reviewer-safe notes.

## Index

| # | Figure type | Typical panel | Data needed | Script |
|---|---|---|---|---|
| 1 | XRD pattern overlay | Phase identification | 2θ, intensity, reference patterns | plot_xrd_pattern.py |
| 2 | Sintering curve | Density vs temperature | Temperature, density, atmosphere | plot_sintering_curve.py |
| 3 | Shrinkage curve | Linear shrinkage vs T | Temperature, shrinkage % | plot_sintering_curve.py |
| 4 | SEM micrograph panel | Grain morphology | Image files, scale bars, grain size | plot_sem_analysis.py |
| 5 | Grain size distribution | Histogram + lognormal fit | Grain diameters (≥100) | plot_sem_analysis.py |
| 6 | Weibull probability plot | Strength reliability | Strength values, specimen count | plot_weibull.py |
| 7 | Bar chart — mechanical | Strength/toughness/hardness | Grouped by composition | plot_ceramic_strength.py |
| 8 | Thermal conductivity plot | κ vs temperature or porosity | Temperature, κ values, density | ✅ in atlas |
| 9 | Thermal expansion (dilatometry) | dL/L0 vs temperature | Temperature, expansion % | ✅ in atlas |
| 10 | TGA/DTG + DSC combo | Thermal stability + transitions | Temperature, mass %, heat flow | ✅ in atlas |
| 11 | Stress-strain (compression) | Mechanical response | Strain, stress | ✅ in atlas |
| 12 | Impedance (Nyquist) plot | Grain + grain boundary | Z', Z", frequency, T | ✅ in atlas |
| 13 | SEM micrograph panel | Grain morphology | Image files, scale bars | (requires SEM assets) |
| 14 | Bar chart — mechanical | Strength/toughness/hardness | Grouped by composition | (uses plot_ceramic_strength.py) |
| 15 | Dielectric properties | ε′ and tan δ vs frequency | Frequency, ε′, tan δ | (requires impedance data) |
| 16 | Porosity distribution | Pore size (MIP) | Pore diameter, log intrusion | (uses plot_particle_size_distribution.py) |
| 17 | Multi-panel summary | Processing → Structure → Properties | Combined data | (requires composition) |

## Evidence standards

| Figure type | Minimum supporting data | Common reviewer flags |
|---|---|---|
| XRD | Reference pattern (ICDD), 2θ range, peak labels | Missing reference; comparing intensity without normalization |
| SEM | Scale bar, accelerating voltage, magnification | Single image not representative; missing scale bar |
| Weibull | n ≥ 10 specimens (preferably 30) | n < 10; no confidence bounds |
| Sintering | Heating rate, dwell, atmosphere | Missing ramp rate; no atmosphere specified |
| Conductivity | Measurement method, temperature, density | Missing density; comparing across different measurement T |
| Impedance | Frequency range, T, equivalent circuit fit | No fit; missing temperature |

## Domain-specific figure contract

For each figure, define:
- **Panel label**: A–F with clear narrative order
- **Evidence type**: direct / inferred / supporting
- **Certainty tier**: definitive / strong / supporting / suggestive
- **Caption boundary**: what the data show AND what they do not prove
- **Reviewer risk**: overclaim / missing control / insufficient statistics
