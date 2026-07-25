# Nanoparticles and Colloidal Nanomaterials Source Screening

Use this reference when screening nanoparticle, quantum dot, and colloidal nanomaterial literature.

## Evidence layers

| Layer | Typical sources | Key markers |
|---|---|---|
| Synthesis | Langmuir, Chem. Mater., ACS Nano | Precursors, capping agents, solvent, temperature, purification |
| Size/shape | TEM, SEM, DLS, AFM | Size distribution histogram, aspect ratio, dispersity |
| Crystal structure | XRD, HRTEM, SAED | Phase, crystallite size, facet exposure |
| Surface chemistry | XPS, FTIR, zeta potential | Ligand identity, functional groups, colloidal stability |
| Optical/electronic | UV-Vis, PL, EIS | Absorption edge, PL QY, bandgap, surface traps |
| Performance | Catalysis, sensing, bioassay | Reaction conditions, loading, controls, recyclability |

## Reviewer-safe screening rules

### Size distribution
- ✅ TEM/SEM histogram with n ≥ 100 + DLS as complementary → `high`
- ⚠️ Representative image without histogram → `screening needed`
- ❌ Size claim based only on DLS for non-spherical particles → `low`

### Colloidal stability
- ✅ Zeta potential + solvent + pH/ionic strength + storage condition → `high`
- ⚠️ Stability mentioned without quantitative data → `screening needed`
- ❌ Dispersion inferred from visual clarity alone → `low`

### Quantum yield / catalytic activity
- ✅ Reference dye or calibrated setup + excitation/reaction conditions + normalization → `high`
- ⚠️ Activity reported without normalization to surface area or mass → `screening needed`
- ❌ Performance compared at different conditions without normalization → `low`

## Claim-source mapping

| Claim | Minimum evidence | Destination |
|---|---|---|
| Size-dependent property | Statistics + property data + structure | Mechanism table + Figure plan |
| Surface functionalization effect | Surface characterization + stability/property comparison + controls | Mechanism table |
| Catalytic activity | Conditions + normalization + recyclability + controls | Citation matrix + Figure plan |
| Biomedical application | Cell/organism model + dose + time + viability + controls | Citation matrix |
