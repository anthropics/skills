# Civil / Construction Materials Source Screening and Quality Standards

Use this reference when screening civil and construction materials literature for citation mapping, review construction, or evidence auditing.

## Evidence layers for civil materials

| Layer | What it covers | Typical sources |
|---|---|---|
| Materials characterization | Mix design, gradation, binder content, additive dosage | Cement and Concrete Research, Construction and Building Materials |
| Mechanical performance | Compressive/tensile/flexural strength, modulus, fatigue | Cement and Concrete Composites, Materials and Structures |
| Durability | Freeze-thaw, carbonation, chloride ingress, sulfate attack | Cement and Concrete Research, Journal of Building Engineering |
| Microstructure | Hydration products, ITZ, pore structure, SEM/BSE/CT | Cement and Concrete Research |
| Rheology/workability | Slump, flow, viscosity, setting time | Construction and Building Materials |
| Field performance | Long-term monitoring, pavement distress, service life | Transportation Research Record, Road Materials and Pavement Design |
| Sustainability | CO₂ footprint, recycled content, LCA | Journal of Cleaner Production, Resources, Conservation and Recycling |

## Source quality tiers

| Tier | Definition | Examples |
|---|---|---|
| **Primary experimental** | Original data from controlled lab or field experiments with full mix/processing and test methods | Research article with mix design, curing, test standards, statistical replication |
| **Review evidence** | Synthesis of multiple primary sources | Review article, book chapter, state-of-the-art report |
| **Method/standard** | Test standard or widely accepted protocol | ASTM C39 (compressive strength), ASTM C496 (split tensile), EN 206, GB/T 50081 |
| **Weak background** | Conference abstract without full data, thesis without peer review, industry brochure, non-English without translation | — |

## Reviewer-safe screening rules

### Mix design and proportioning
- ✅ Binder type/content, water-to-binder ratio, aggregate gradation, admixture dosage all reported → `high`
- ⚠️ Partial mix design reported (e.g., only binder content) → `screening needed`
- ❌ No mix design or only trade-name products without composition → `low`

### Curing and conditioning
- ✅ Curing regime (T, RH, duration) and specimen age at testing clearly stated → `high`
- ⚠️ Only curing duration reported → `screening needed`
- ❌ No curing/conditioning information → `low`

### Mechanical properties
- ✅ Standard test method + specimen geometry + n ≥ 3 with statistics → `high`
- ⚠️ Standard test method + n = 3, no statistics → `medium`
- ❌ Non-standard test or no specimen count → `low`

### Durability claims
- ✅ Exposure regime (concentration, T, duration) + measured degradation metric → `high`
- ⚠️ Exposure described but degradation metric unclear → `screening needed`
- ❌ Durability inferred from composition only → `low`

### Field vs. lab correlation
- ✅ Field condition documented + lab test correlated to field performance → `high`
- ⚠️ Lab data presented as proxy for field performance without validation → `screening needed`
- ❌ Lab result directly claimed as field performance → `low`

## Claim-source mapping rules

| Claim type | Minimum evidence | Move to |
|---|---|---|
| Strength improvement from additive | Mix design + curing + standard mechanical test + statistics | Citation matrix |
| Durability enhancement | Accelerated exposure + measured property change + microstructural support | Mechanism table + Figure plan |
| Microstructural mechanism | Imaging/spectroscopy + quantitative image analysis where possible | Mechanism table |
| Sustainability claim | LCA boundary + functional unit + data sources + limitations | Review discussion only |
| Field performance prediction | Lab-field correlation or long-term monitoring data | Citation matrix |
