# Metals and Alloys Phrase Bank

Use this bank for ferrous alloys, nonferrous alloys (Al, Cu, Mg, Ti),
high-temperature alloys, and additively manufactured metals.

---

## phrase-bank

### microstructure and phases

- `The microstructure of [alloy] consists of [phase A] and [phase B] with [grain size/morphology/distribution], as observed by [optical/SEM/EBSD/TEM].`
- `EBSD analysis reveals a [random/textured/bimodal] grain structure with [percentage]% of [grain type/twin boundaries/low-angle boundaries].`
- `The precipitate identified as [phase] by [TEM-EDS/SAED/XRD] has a size distribution of [range] and [coherent/semi-coherent/incoherent] interface with the matrix.`

### mechanical behavior

- `The [yield/tensile/fatigue] strength of [alloy] was [value] MPa ([standard]), representing a [percentage] improvement over [reference/baseline condition].`
- `The [elongation/reduction in area] of [value]% indicates [ductile/brittle/mixed] fracture behavior, consistent with [fractography/microstructure/texture] observations.`
- `Strain hardening behavior follows [Hollomon/Ludwick/Voce] relationship with [parameters], reflecting [dislocation density/twinning/phase transformation] contribution.`

### strengthening mechanisms

- `The strength increase is attributed to [solid-solution/precipitation/grain-boundary/dislocation] strengthening, with estimated contributions of [value] MPa from each mechanism.`
- `Hall-Petch analysis yields [σ₀] and [k_y] values consistent with [grain size range], suggesting [grain-boundary] strengthening dominates at [condition].`
- `The Orowan stress for [precipitate size/spacing] is estimated at [value] MPa, which accounts for [percentage]% of the observed strength increment.`

### corrosion behavior

- `The [pitting/general/intergranular/stress corrosion] resistance of [alloy] was assessed by [potentiodynamic polarization/EIS/salt spray/immersion], yielding [corrosion current/pitting potential/impedance] of [value].`
- `The formation of [passive film/composition/deposit] is suggested by [XPS/SEM-EDS/EIS] evidence, but the long-term stability under [service condition] requires further evaluation.`
- `The synergistic effect of [environment/stress/microstructure] on corrosion rate is difficult to separate without [controlled experiment/in situ monitoring].`

### heat treatment

- `After [solution treatment/aging/quenching/tempering] at [temperature]°C for [time] h, [alloy] showed [precipitate refinement/grain refinement/residual stress relief] and [property change].`
- `The aging response, characterized by [hardness evolution/precipitate coarsening/mechanical property change], indicates [peak under-aged/over-aged] condition at [time/temperature].`
- `The heat treatment window for [property optimization] is [temperature range] and [time range], beyond which [grain coarsening/over-aging/dissolution] degrades performance.`

### additive manufacturing

- `The [LPBF/SLM/DED/WAM] processed [alloy] achieved [relative density]% with [process parameters], and the microstructure shows [columnar/equiaxed/bimodal] grain morphology.`
- `Anisotropy in [mechanical/thermal/fatigue] response between [build direction/transverse] is consistent with [texture/melt pool boundaries/residual stress/porosity] observations.`
- `Post-processing by [HIP/heat treatment/hot isostatic pressing] reduced porosity from [value]% to [value]% and improved [fatigue/ductility/strength] by [value]%.`

### fatigue and fracture

- `The [S–N/Wöhler] curve for [alloy] shows a fatigue limit of [value] MPa at [R-ratio/frequency/environment], with failure initiating from [inclusion/porosity/surface/defect].`
- `Fractography reveals [transgranular/intergranular/mixed] crack propagation with [striations/dimples/cleavage/river patterns], consistent with [fatigue/ductile/brittle] mechanism.`
- `The Paris law exponent [m] and coefficient [C] for crack growth are [values], within the range reported for [similar alloy/condition].`

---

## reviewer-red-flags

- Reporting strength without specifying processing route, heat treatment, and test standard.
- Claiming strengthening mechanism without quantitative contribution analysis (e.g., Hall-Petch, Orowan).
- Comparing corrosion data across different electrolytes, temperatures, or test methods without normalization.
- Attributing AM anisotropy to texture without EBSD or pole figure evidence.
- Claiming fatigue limit without sufficient cycle count (typically ≥ 10⁷).
- Reporting precipitate strengthening without precipitate size, spacing, and coherency data.

---

## safe-claim-patterns

- `Within the tested [composition/heat treatment/processing] range, [alloy] achieves [property] consistent with [strengthening mechanism] contribution estimated from [model/evidence].`
- `The [corrosion/fatigue/wear] resistance improvement is attributed to [mechanism] based on [characterization], though the contribution of [alternative factor] requires further separation.`
- `The additive manufacturing route shows promise for [application], but [residual stress/porosity/surface finish/anisotropy] must be addressed through [post-processing/parameter optimization].`
