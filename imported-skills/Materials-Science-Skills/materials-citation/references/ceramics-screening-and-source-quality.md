# Ceramics Source Screening and Quality Standards

Use this reference when screening ceramics literature for citation mapping, review construction, or evidence auditing.

## Evidence layers for ceramics

| Layer | What it covers | Typical sources |
|---|---|---|
| Processing | Powder synthesis, forming, sintering, post-processing | Acta Materialia, JACerS, Ceramics International |
| Phase composition | XRD, Rietveld, phase transformation | JACerS, JEurCerSoc, Journal of the ACS |
| Microstructure | Grain size, grain boundary, porosity, SEM/TEM | Journal of the American Ceramic Society |
| Mechanical | Strength, toughness, hardness, Weibull | JACerS, JEurCerSoc, Acta Materialia |
| Thermal | Conductivity, expansion, thermal shock | JACerS, Journal of the European Ceramic Society |
| Functional | Dielectric, piezoelectric, ionic conductivity | JACerS, Journal of Materials Chemistry A |
| Bioceramics | Bioactivity, degradation, biocompatibility | Acta Biomaterialia, Biomaterials |

## Source quality tiers

| Tier | Definition | Examples |
|---|---|---|
| **Primary experimental** | Original data from controlled experiments with full processing + characterization | Research article with sintering profile, density, XRD, SEM, mechanical |
| **Review evidence** | Synthesis of multiple primary sources | Review article, book chapter, monograph |
| **Method/standard** | Test standard or widely accepted protocol | ASTM C1161 (flexural strength), ASTM C373 (density), ISO 6872 |
| **Weak background** | Conference abstract, thesis without peer review, non-English without translation, industry brochure | — |

## Reviewer-safe screening rules

### Processing claims
- ✅ Sintering T + ramp + dwell + atmosphere all reported → `high`
- ⚠️ Only sintering T reported, ramp/dwell missing → `screening needed`
- ❌ No sintering conditions reported → `low`

### Phase identification
- ✅ XRD with reference pattern (ICDD/JCPDS) + peak labels → `high`
- ✅ XRD + Rietveld (R < 10%) → `high`
- ⚠️ XRD without reference pattern → `screening needed`
- ❌ Phase claimed from composition only → `low`

### Mechanical properties
- ✅ Standard test method + specimen geometry + n ≥ 10 + Weibull → `high`
- ⚠️ Standard test method + n ≥ 5, no Weibull → `medium`
- ❌ No standard, no specimen count → `low`

### Fracture toughness
- ✅ KIC method stated (SENB, SEPB, IF, CNB) + n ≥ 5 → `high`
- ⚠️ KIC reported without method → `screening needed`
- ❌ Toughness claimed from strength alone → `low`

### Density
- ✅ Archimedes or geometric method + theoretical density reference → `high`
- ⚠️ Density reported without method → `screening needed`
- ❌ No density data → `low`

## Claim-source mapping rules

| Claim type | Minimum evidence | Move to |
|---|---|---|
| Processing-property link | At least one processing variable linked to property | Citation matrix |
| Phase-transformation mechanism | XRD before/after + thermal evidence (DSC/DTA) | Mechanism table |
| Toughening mechanism | Fractography + KIC + microstructural evidence | Mechanism table + Figure plan |
| Performance benchmark | Comparison with literature values under comparable test conditions | Citation matrix |
| Application potential | Property threshold relevant to application + limitation acknowledged | Review discussion only |
