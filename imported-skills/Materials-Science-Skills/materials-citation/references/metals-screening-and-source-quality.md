# Metals and Alloys Source Screening and Quality Standards

Use this reference when screening metals, alloys, steels, aluminum, titanium, superalloys, and metallic materials literature for citation mapping, review construction, or evidence auditing.

## Evidence layers for metals and alloys

| Layer | What it covers | Typical sources |
|---|---|---|
| Processing | Melting, casting, thermomechanical processing, heat treatment, additive manufacturing | Acta Materialia, Metallurgical and Materials Transactions A |
| Microstructure | Grain size, phases, precipitates, texture, EBSD, SEM/TEM | Acta Materialia, Scripta Materialia |
| Mechanical properties | Tensile, yield, hardness, toughness, fatigue, creep | Materials Science and Engineering A, Metallurgical and Materials Transactions A |
| Physical properties | Density, electrical/thermal conductivity, magnetic properties | Journal of Alloys and Compounds |
| Corrosion/environmental | Polarization, weight loss, pitting, oxidation, hydrogen embrittlement | Corrosion Science, Electrochimica Acta |
| Fracture and damage | Fractography, crack growth, damage tolerance | Engineering Fracture Mechanics, International Journal of Fatigue |

## Source quality tiers

| Tier | Definition | Examples |
|---|---|---|
| **Primary experimental** | Original data from controlled processing and characterization with full alloy composition and heat treatment | Research article with composition, processing, microstructure, property data |
| **Review evidence** | Synthesis of multiple primary sources | Review article, book chapter, handbook entry |
| **Method/standard** | Test standard or widely accepted protocol | ASTM E8/E8M (tensile), ASTM E23 (Charpy), ASTM G59 (polarization), ISO 6892 |
| **Weak background** | Conference abstract, thesis without peer review, unverified trade literature | — |

## Reviewer-safe screening rules

### Composition and processing
- ✅ Full composition (major + key minor elements), processing route, heat treatment all reported → `high`
- ⚠️ Composition or heat treatment partially reported → `screening needed`
- ❌ Only alloy designation without composition or processing → `low`

### Microstructure
- ✅ Sample preparation + imaging condition + quantitative microstructural parameters (grain size, phase fraction) → `high`
- ⚠️ Representative images without quantification → `screening needed`
- ❌ Microstructure claim without image or composition link → `low`

### Mechanical properties
- ✅ Standard test + specimen orientation + strain rate + n ≥ 3 with statistics → `high`
- ⚠️ Standard test + n = 3 without statistics → `medium`
- ❌ No standard or specimen orientation for textured/anisotropic material → `low`

### Heat treatment
- ✅ Solutionizing + aging T/time/atmosphere or TTT/CCT reference → `high`
- ⚠️ Only aging condition reported → `screening needed`
- ❌ Property compared across conditions without reporting heat treatment → `low`

### Corrosion/oxidation
- ✅ Electrolyte/composition + temperature + exposure time + surface area/volume + evaluation method → `high`
- ⚠️ Medium described but no temperature or exposure time → `screening needed`
- ❌ Corrosion resistance inferred from composition only → `low`

## Claim-source mapping rules

| Claim type | Minimum evidence | Move to |
|---|---|---|
| Processing-microstructure-property link | Composition + processing + microstructure + property data | Citation matrix + Mechanism table |
| Strengthening/toughening mechanism | Microscopy + property data + model/quantification | Mechanism table + Figure plan |
| Fatigue/creep performance | Standard test + microstructure + fracture surface | Citation matrix |
| Corrosion resistance | Electrochemical or exposure test + surface characterization | Mechanism table |
| Alloy design recommendation | Multiple validated properties + application requirements + trade-offs | Review discussion only |
