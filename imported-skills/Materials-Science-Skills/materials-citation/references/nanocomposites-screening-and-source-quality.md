# Polymer and Ceramic Matrix Nanocomposites Source Screening

Use this reference when screening nanocomposite literature where nanoparticles, nanofibers, or nanoplates reinforce or functionalize a matrix.

## Evidence layers

| Layer | Typical sources | Key markers |
|---|---|---|
| Matrix/filler | Composites Part A/B, Polymer | Matrix grade, filler type, surface treatment, loading fraction |
| Dispersion | SEM, TEM, X-ray CT, optical microscopy | Agglomerate size, distribution, percolation evidence |
| Interface | FTIR, XPS, DMA, rheology | Functionalization, interfacial adhesion, coupling agent |
| Processing | Extrusion, casting, 3D printing, sintering | Parameters, shear, solvent, curing |
| Mechanical | Tensile, flexural, impact, fracture | Modulus, strength, toughness, failure mode |
| Functional | Thermal, electrical, barrier, fire | Conductivity, Tg shift, permeation, flame retardancy |

## Reviewer-safe screening rules

### Dispersion
- ✅ Representative microscopy + quantitative dispersion metric or filler size distribution → `high`
- ⚠️ Microscopy shown without quantification or low-magnification only → `screening needed`
- ❌ Dispersion claimed without imaging → `low`

### Loading fraction
- ✅ Filler mass/volume fraction + matrix density + verification method → `high`
- ⚠️ Loading reported as weight but compared to volume fraction elsewhere → `screening needed`
- ❌ Loading inferred from feed ratio without measurement → `low`

### Property enhancement
- ✅ Baseline matrix data + composite series + statistics + mechanism link → `high`
- ⚠️ Single loading compared without matrix control or statistics → `screening needed`
- ❌ Enhancement attributed to filler without matrix control or dispersion evidence → `low`

## Claim-source mapping

| Claim | Minimum evidence | Destination |
|---|---|---|
| Mechanical reinforcement | Loading series + dispersion + mechanical data + fractography | Citation matrix + Mechanism table |
| Percolation/conductivity | Loading series + filler geometry + network imaging | Mechanism table + Figure plan |
| Barrier improvement | Permeation data + tortuosity model + dispersion | Citation matrix |
| Flame retardancy | Cone calorimetry/TGA-FTIR + char morphology + loading | Citation matrix + Figure plan |
