# Nanostructured Thin Films and Coatings Source Screening

Use this reference when screening nanostructured thin film, coating, and nanolayer literature.

## Evidence layers

| Layer | Typical sources | Key markers |
|---|---|---|
| Deposition | JVST, Surface & Coatings Tech., Thin Solid Films | Method, substrate, temperature, pressure, thickness |
| Thickness/morphology | Profilometer, SEM cross-section, AFM | Thickness, roughness, uniformity, columnar structure |
| Structure | XRD, GIXRD, HRTEM, RHEED | Crystallinity, texture, phase, grain size |
| Composition | XPS, EDX, SIMS, RBS | Stoichiometry, contamination, depth profile |
| Functional properties | Optical, electrical, mechanical, barrier | Transmittance, resistivity, hardness, permeation |
| Adhesion/durability | Scratch test, tape, cyclic exposure | Adhesion rating, wear rate, corrosion protection |

## Reviewer-safe screening rules

### Thickness and uniformity
- ✅ Cross-sectional SEM or profilometer + reported average and variation → `high`
- ⚠️ Thickness estimated from deposition rate/time without calibration → `screening needed`
- ❌ Thickness assumed from nominal recipe → `low`

### Structure-property link
- ✅ Structure + composition + property measured on same sample → `high`
- ⚠️ Property compared across batches without structural verification → `screening needed`
- ❌ Property attributed to nanostructure without imaging → `low`

### Barrier/protective performance
- ✅ Test method (permeation, corrosion, wear) + conditions + control substrate → `high`
- ⚠️ Performance reported without control or standard reference → `screening needed`
- ❌ Lifetime extrapolated from short test without acceleration model → `low`

## Claim-source mapping

| Claim | Minimum evidence | Destination |
|---|---|---|
| Thickness-property optimization | Thickness series + structure + property | Mechanism table + Figure plan |
| Barrier enhancement | Permeation/corrosion test + defect characterization | Citation matrix |
| Mechanical durability | Hardness/adhesion/wear + thickness + structure | Citation matrix |
| Transparent conductor | Sheet resistance + transmittance + film thickness | Mechanism table + Figure plan |
