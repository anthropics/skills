# Functional / Electronic Materials Source Screening and Quality Standards

Use this reference when screening semiconductor, dielectric, piezoelectric, ferroelectric, photonic, optoelectronic, and electrochemical materials literature for citation mapping, review construction, or evidence auditing.

## Evidence layers for functional materials

| Layer | What it covers | Typical sources |
|---|---|---|
| Synthesis/fabrication | Thin-film deposition, doping, device processing, lithography | Advanced Functional Materials, ACS Applied Materials & Interfaces |
| Structural/compositional | XRD, XPS, SIMS, EDX, stoichiometry, defect chemistry | Advanced Materials, Chemistry of Materials |
| Electronic properties | Carrier density, mobility, conductivity, bandgap, doping type | Applied Physics Letters, IEEE Electron Device Letters |
| Dielectric/piezoelectric | Permittivity, loss, P-E loops, d33, electromechanical coupling | Journal of Applied Physics, Applied Physics Letters |
| Optical/optoelectronic | Absorption, PL, EQE, responsivity, band-edge behavior | Advanced Optical Materials, Nature Photonics |
| Device performance | Solar cell PCE, transistor metrics, sensor response, LED efficiency | Nature Energy, Advanced Energy Materials |
| Stability/reliability | Aging, bias-temperature stress, cycling, degradation kinetics | Advanced Energy Materials, ACS Energy Letters |

## Source quality tiers

| Tier | Definition | Examples |
|---|---|---|
| **Primary experimental** | Original data from controlled synthesis/fabrication with full processing and characterization | Research article with deposition conditions, device stack, measurement protocol |
| **Review evidence** | Synthesis of multiple primary sources | Review article, topical review, book chapter |
| **Method/standard** | Test standard or widely accepted protocol | ASTM F76 (Hall effect), IEEE 1620 (organic transistor), JIS for piezoelectric |
| **Weak background** | Conference abstract, patent claim without data, unverified press release | — |

## Reviewer-safe screening rules

### Material synthesis and device fabrication
- ✅ Deposition/growth method, substrate, temperature, atmosphere, film thickness/device area all reported → `high`
- ⚠️ Method reported but key parameters (e.g., temperature, thickness) missing → `screening needed`
- ❌ Only material name/approach without processing detail → `low`

### Electronic properties
- ✅ Measurement geometry, temperature, frequency, instrument, and environmental conditions reported → `high`
- ⚠️ Property value reported without measurement conditions → `screening needed`
- ❌ Carrier type or mobility inferred from composition only → `low`

### Device performance
- ✅ Active area, illumination/bias conditions, measurement direction, device statistics (n ≥ 3) → `high`
- ⚠️ Single best-device value reported without statistics → `screening needed`
- ❌ Performance claimed without defining measurement conditions → `low`

### Hysteresis and sweep direction
- ✅ Hysteresis checked and sweep direction/stabilization time reported (for J-V, P-E, etc.) → `high`
- ⚠️ Hysteresis mentioned but not characterized → `screening needed`
- ❌ No awareness of hysteresis in devices with known hysteretic behavior → `low`

### Stability
- ✅ Stability test conditions (atmosphere, bias, temperature, duration) and degradation metric defined → `high`
- ⚠️ Short-term stability reported without conditions → `screening needed`
- ❌ Stability claimed from a single snapshot measurement → `low`

## Claim-source mapping rules

| Claim type | Minimum evidence | Move to |
|---|---|---|
| Device performance record | Certified measurement or in-house full protocol + statistics + conditions | Citation matrix |
| Structure-property relationship | Processing + structural characterization + property data | Mechanism table + Figure plan |
| Interface/contact effect | Interface characterization + control experiments + device physics | Mechanism table |
| Degradation mechanism | Accelerated test + in-situ/operando characterization + post-mortem analysis | Mechanism table + Figure plan |
| Application potential | Property threshold + stability/limitations clearly stated | Review discussion only |
