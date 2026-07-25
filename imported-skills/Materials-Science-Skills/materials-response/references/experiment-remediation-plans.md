# Experiment Remediation Plans

> **Domain context**: The `domain` axis has loaded domain-specific experiment guidance. The plans below are universal templates; the domain guide lists domain-specific test methods and standards.

Use this reference when reviewers request additional experiments. Each plan separates what can be done, what resources are needed, and what must be framed as a limitation.

**Evidence gate**: Only use completed or planned experiment language when the user/source confirms the status. Otherwise mark `[AUTHOR_INPUT_NEEDED: confirm experiment status/timeline]` and frame the item as a possible revision path.

## 1. Mechanism Evidence Experiments

### 1.1 FTIR/Fourier Transform Infrared Spectroscopy

**Purpose**: Identify functional groups, chemical bonds, and reaction products.

**When reviewer asks**: "Mechanism not supported," "Chemical structure unclear," "Reaction products not identified."

**Plan**:
1. Prepare samples at key processing stages or conditions.
2. Collect FTIR spectra (4000-400 cm⁻¹, resolution 4 cm⁻¹, 32+ scans).
3. Identify characteristic peaks and assign to functional groups.
4. Compare spectra across conditions to show chemical changes.
5. Quantify peak area ratios if applicable (e.g., carbonyl index).

**Time estimate**: 1-2 days for measurement, 1-2 days for analysis.

**Limitation if unavailable**: State that FTIR is planned for future work; soften mechanism claims to "suggested by" rather than "confirmed by."

### 1.2 SEM/Scanning Electron Microscopy

**Purpose**: Visualize surface morphology, microstructure, and interface quality.

**When reviewer asks**: "Morphology not shown," "Interface quality unclear," "Dispersion not demonstrated."

**Plan**:
1. Prepare samples (fracture surfaces, polished cross-sections, or thin films).
2. Coat with conductive layer if needed (Au, Pt, or carbon).
3. Image at multiple magnifications (100x, 500x, 2000x, 5000x+).
4. Include EDS if elemental composition is relevant.
5. Compare morphology across key conditions.

**Time estimate**: 1-2 days for sample prep, 1 day for imaging.

**Limitation if unavailable**: Use optical microscopy if available; otherwise, describe morphology qualitatively and add as future work.

### 1.3 XRD/X-ray Diffraction

**Purpose**: Identify crystalline phases, crystal structure, and phase composition.

**When reviewer asks**: "Phase identification missing," "Crystal structure not confirmed," "Reaction products not characterized."

**Plan**:
1. Prepare powdered or flat samples.
2. Collect XRD patterns (2θ range depends on material, typically 5-80°).
3. Identify phases using ICDD/JCPDS database.
4. Quantify phase fractions if applicable (Rietveld refinement).
5. Compare patterns across conditions.

**Time estimate**: 1-2 days for measurement, 1-2 days for analysis.

### 1.4 TG/DTG/Thermogravimetric Analysis

**Purpose**: Measure thermal stability, decomposition behavior, and composition.

**When reviewer asks**: "Thermal stability not shown," "Composition not verified," "Decomposition behavior unclear."

**Plan**:
1. Prepare 5-15 mg samples in appropriate crucibles.
2. Heat at 10°C/min (or standard rate) from room temperature to 800°C.
3. Record mass loss and derivative (DTG) curves.
4. Identify decomposition stages and temperatures.
5. Compare thermal behavior across conditions.

**Time estimate**: 1 day for measurement, 1 day for analysis.

## 2. Performance Evidence Experiments

### 2.1 Mechanical Testing (Tensile, Compressive, Flexural)

**Purpose**: Quantify mechanical performance and compare across conditions.

**When reviewer asks**: "Mechanical properties insufficient," "Performance not quantified," "Comparison with literature weak."

**Plan**:
1. Prepare specimens per relevant standard (ASTM, ISO, GB/T).
2. Test at minimum 5 replicates per condition.
3. Report mean, standard deviation, and coefficient of variation.
4. Include stress-strain curves if relevant.
5. Compare with literature values using the same test method.

**Time estimate**: 2-3 days for specimen preparation, 1-2 days for testing.

**Limitation if unavailable**: Report available data with reduced claims; add limitation about sample size.

### 2.2 Durability Testing (Aging, Freeze-Thaw, Moisture)

**Purpose**: Demonstrate long-term performance and environmental resistance.

**When reviewer asks**: "Durability not shown," "Aging behavior unknown," "Environmental resistance not tested."

**Plan**:
1. Select aging protocol (TFOT, RTFOT, PAV, UV, water immersion, freeze-thaw).
2. Test at multiple time points (e.g., 1, 3, 7, 14, 28 days).
3. Measure property retention (strength, mass, dimensional stability).
4. Compare with unaged control.
5. Report retention ratios.

**Time estimate**: 1-4 weeks depending on aging duration.

**Limitation if unavailable**: State that long-term durability is beyond current scope; report short-term data if available; add as future work.

### 2.3 Bonding/Adhesion Testing

**Purpose**: Quantify interface strength and adhesion quality.

**When reviewer asks**: "Bonding strength not measured," "Interface quality not demonstrated," "Adhesion mechanism unclear."

**Plan**:
1. Prepare bonded specimens per relevant standard.
2. Test using pull-off, shear, or peel method as appropriate.
3. Minimum 5 replicates per condition.
4. Report failure mode (adhesive, cohesive, or mixed).
5. Include photographs of failure surfaces.

**Time estimate**: 2-3 days for specimen preparation, 1-2 days for testing.

### 2.4 Rheological Testing

**Purpose**: Measure flow behavior, viscosity, and viscoelastic properties.

**When reviewer asks**: "Rheology not reported," "Flow behavior unknown," "Viscosity not measured."

**Plan**:
1. Select appropriate geometry (parallel plate, cone-plate, concentric cylinder).
2. Perform steady-state shear (viscosity vs. shear rate).
3. Perform oscillatory tests (G', G" vs. frequency or strain).
4. Test at relevant temperatures.
5. Report yield stress, zero-shear viscosity, or other relevant parameters.

**Time estimate**: 1-2 days for measurement, 1 day for analysis.

## 3. Statistical Evidence Experiments

### 3.1 Replicate Testing

**Purpose**: Provide statistical basis for claims.

**When reviewer asks**: "Sample size too small," "Statistics insufficient," "Error bars missing."

**Plan**:
1. Determine minimum replicates (typically n≥5 for materials testing).
2. Test additional specimens to reach target sample size.
3. Calculate mean, standard deviation, standard error, confidence interval.
4. Perform appropriate statistical tests (t-test, ANOVA) if comparing groups.
5. Add error bars to all figures.

**Time estimate**: 1-3 days depending on test type and number of additional specimens.

### 3.2 Design of Experiments (DOE)

**Purpose**: Systematically optimize parameters and identify key factors.

**When reviewer asks**: "Optimization not systematic," "Factor interactions not considered," "Only one-factor-at-a-time."

**Plan**:
1. Identify key factors and levels.
2. Select DOE approach (factorial, Taguchi, response surface).
3. Run the designed experiments.
4. Analyze results (ANOVA, main effects, interactions).
5. Report optimal conditions and factor significance.

**Time estimate**: 1-2 weeks depending on design complexity.

**Limitation if unavailable**: Acknowledge that systematic optimization is beyond current scope; report one-factor-at-a-time results with appropriate caveats.

## 4. Characterization Evidence Experiments

### 4.1 Particle Size Distribution

**Purpose**: Quantify particle size and distribution.

**When reviewer asks**: "Particle size not reported," "Size distribution unknown," "Dispersion quality unclear."

**Plan**:
1. Prepare samples in appropriate dispersant.
2. Measure using laser diffraction (Malvern, Horiba) or DLS.
3. Report D10, D50, D90, and span.
4. Include size distribution curves.
5. Compare across conditions if relevant.

**Time estimate**: 1 day for measurement, 0.5 day for analysis.

### 4.2 Surface Area and Porosity (BET)

**Purpose**: Measure specific surface area and pore structure.

**When reviewer asks**: "Surface area not reported," "Porosity not characterized," "Pore structure unknown."

**Plan**:
1. Degass samples at appropriate temperature.
2. Measure nitrogen adsorption-desorption isotherms.
3. Calculate BET surface area, pore volume, and pore size distribution.
4. Report isotherm type and hysteresis if relevant.
5. Compare with literature values.

**Time estimate**: 1-2 days for measurement, 1 day for analysis.

### 4.3 Spectroscopic Characterization (Raman, UV-Vis, PL)

**Purpose**: Provide spectroscopic evidence for structure, composition, or optical properties.

**When reviewer asks**: "Spectroscopic evidence missing," "Optical properties not characterized," "Structure not confirmed."

**Plan**:
1. Select appropriate spectroscopic method for the material.
2. Collect spectra under standard conditions.
3. Identify characteristic peaks/bands.
4. Compare with reference spectra or literature.
5. Quantify if applicable (peak intensity ratios, band gaps).

**Time estimate**: 1-2 days for measurement, 1-2 days for analysis.

## 5. Comparison and Benchmarking Experiments

### 5.1 Control/Baseline Experiments

**Purpose**: Provide reference point for comparison.

**When reviewer asks**: "No control sample," "Baseline missing," "Improvement not demonstrated."

**Plan**:
1. Prepare control sample (unmodified, standard condition, or commercial reference).
2. Test control under identical conditions.
3. Compare treatment vs. control with statistical analysis.
4. Report improvement percentage or ratio.
5. Discuss significance of improvement.

**Time estimate**: 2-3 days for preparation and testing.

### 5.2 Literature Benchmarking

**Purpose**: Compare with published results.

**When reviewer asks**: "Comparison with literature weak," "Context not provided," "Performance not benchmarked."

**Plan**:
1. Identify 5-10 relevant literature studies with similar materials/methods.
2. Create comparison table with key variables.
3. If test methods differ, compare trends rather than absolute values.
4. Discuss reasons for differences (material, method, condition).
5. Position your results within the literature landscape.

**Time estimate**: 1-2 days for literature search and table creation.

## 6. Decision Framework

When a reviewer requests additional experiments, use this framework:

| Step | Question | Action |
|------|----------|--------|
| 1 | Is the experiment feasible with available resources? | If yes → Recommend as a revision path; author/editor decision required. If no → Step 2. |
| 2 | Can the experiment be done within revision timeline? | If yes → Prioritize only after author confirmation. If no → Step 3. |
| 3 | Does the experiment address a fundamental concern? | If yes → Request timeline extension or partial data. If no → Step 4. |
| 4 | Can the claim be softened to remove the need? | If yes → Revise claims and add limitation. If no → Step 5. |
| 5 | Can the experiment be framed as future work? | If yes → Add to future work section. If no → Step 6. |
| 6 | Is the experiment truly necessary for publication? | If yes → Flag as publication-critical for author decision. If no → Discuss with editor. |

## 7. Response Templates

### Template A: Experiment completed

> [Use only when confirmed.] To address the reviewer's concern about [specific issue], we conducted [experiment name] following [standard/method]. The results show [key finding]. These data are now presented in [Figure/Table X] and discussed in Section [Y].

### Template B: Experiment planned but not yet completed

> We agree that [experiment] would strengthen the manuscript. If the authors choose this revision path, [experiment] can be added to address [specific concern]. [AUTHOR_INPUT_NEEDED: confirm timeline and whether work has started.]

### Template C: Experiment beyond scope

> We acknowledge that [experiment] would provide valuable additional evidence. However, this experiment is beyond the current scope because [reason]. We have revised the relevant claims to be more cautious and added this as future work in Section [X].

### Template D: Experiment not feasible

> We appreciate the reviewer's suggestion for [experiment]. Due to [resource/equipment/time limitation], this experiment cannot be completed within the current revision timeline. We have [alternative action: softened claims / added limitation / cited supporting literature] to address the underlying concern.
