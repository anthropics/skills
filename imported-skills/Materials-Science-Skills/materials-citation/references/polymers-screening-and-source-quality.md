# Polymers / Composites Source Screening and Quality Standards

Use this reference when screening polymer, resin, rubber, elastomer, and polymer-matrix composite literature for citation mapping, review construction, or evidence auditing.

## Evidence layers for polymers and composites

| Layer | What it covers | Typical sources |
|---|---|---|
| Synthesis/processing | Polymerization, curing, compounding, molding, extrusion | Polymer, Polymer Testing, Composites Part A |
| Chemical structure | Monomer/oligomer composition, functional groups, molecular weight | Macromolecules, Polymer Chemistry |
| Thermal properties | Tg, Tm, Td, TGA, DSC, DMA | Polymer Testing, Thermochimica Acta |
| Mechanical properties | Tensile, flexural, impact, fracture toughness, fatigue | Composites Part B, Polymer Testing |
| Rheology | Melt viscosity, gelation, cure kinetics | Rheologica Acta, Polymer Engineering and Science |
| Microstructure | Morphology, filler dispersion, interface, SEM/TEM/AFM | Composites Part A, Polymer |
| Aging/environmental | UV, oxidation, hydrolysis, thermal aging | Polymer Degradation and Stability |

## Source quality tiers

| Tier | Definition | Examples |
|---|---|---|
| **Primary experimental** | Original data from controlled synthesis/processing with full formulation and characterization | Research article with formulation, curing profile, molecular weight, thermal/mechanical data |
| **Review evidence** | Synthesis of multiple primary sources | Review article, book chapter, encyclopedia entry |
| **Method/standard** | Test standard or widely accepted protocol | ASTM D638 (tensile), ASTM D790 (flexural), ISO 1133 (MFI), ASTM D256 (Izod impact) |
| **Weak background** | Conference abstract, patent without data, thesis without peer review, supplier datasheet | — |

## Reviewer-safe screening rules

### Formulation and processing
- ✅ Base polymer, additives/fillers, mass fractions, curing agent, processing conditions all reported → `high`
- ⚠️ Base polymer and filler type reported but loading fraction missing → `screening needed`
- ❌ Only commercial product name given without composition → `low`

### Molecular weight / architecture
- ✅ Mn, Mw, PDI measured and reported (for synthesized polymers) → `high`
- ⚠️ Only one molecular weight average reported → `screening needed`
- ❌ No molecular characterization for a synthesized polymer → `low`

### Thermal properties
- ✅ DSC/TGA method + heating rate + atmosphere + sample mass + Tg/Tm/Td values → `high`
- ⚠️ Tg/Tm reported without scan rate or method → `screening needed`
- ❌ Thermal claim based only on nominal resin data → `low`

### Mechanical properties
- ✅ Standard test method + specimen type + strain rate + n ≥ 5 with statistics → `high`
- ⚠️ Standard method + n = 3-5 without statistics → `medium`
- ❌ Non-standard geometry or no specimen count → `low`

### Filler/matrix interface
- ✅ Dispersion characterized (SEM/TEM) + interfacial treatment described + property link shown → `high`
- ⚠️ Dispersion mentioned but not quantified → `screening needed`
- ❌ Property improvement attributed to interface without imaging or treatment detail → `low`

## Claim-source mapping rules

| Claim type | Minimum evidence | Move to |
|---|---|---|
| Property improvement from filler | Formulation + dispersion + mechanical/thermal test + statistics | Citation matrix |
| Cure/phase-transition mechanism | DSC/DMA + conversion data + kinetic analysis | Mechanism table + Figure plan |
| Toughness/strength trade-off | Fractography + mechanical test + micromechanical model | Mechanism table + Figure plan |
| Long-term durability | Accelerated aging + property retention + microstructural evidence | Citation matrix |
| Processing-property link | Rheology/cure kinetics + processing window + property data | Mechanism table |
