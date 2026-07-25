# Acta Materialia Review Simulation

Simulated peer review for a manuscript submitted to *Acta Materialia*.
Manuscript topic: "Mechanical behavior and deformation mechanisms of a novel CoCrFeNiMn-based high-entropy alloy: dislocation substructure evolution and twinning-mediated plasticity."

---

## Reviewer A

**Overall assessment:** Major Revision

**Focus:** Novelty, mechanism depth, journal fit

**Scores**

| Dimension | Score (0-5) |
|---|---|
| Innovation | 3 |
| Methodology | 4 |
| Evidence | 2 |
| Writing | 3 |
| Figure quality | 4 |
| Journal fit | 3 |

### Major comments

1. **[severity: high] [location: Introduction S1] Novelty claim is insufficiently differentiated from prior art.**
   The manuscript positions the studied alloy as "novel" based on the addition of 2 at.% Al to the equiatomic CoCrFeNiMn system. However, Al-containing variants of Cantor-type alloys have been extensively documented (e.g., CoCrFeNiMnAl_x, x = 0.1-0.5, by multiple groups since 2016). The manuscript does not clearly articulate what is fundamentally new about this specific composition beyond compositional space exploration.
   *Evidence needed:* A dedicated comparison table listing key mechanical properties (yield strength, UTS, elongation, strain hardening exponent) and deformation mechanisms for all published CoCrFeNiMnAl variants. The authors must identify at least one property-mechanism combination that is qualitatively different from existing reports.

2. **[severity: high] [location: Discussion S4.2] Twinning mechanism evidence is circumstantial.**
   The claim that deformation twinning is the dominant plasticity mechanism at 77 K rests on (i) TEM bright-field images showing planar features and (ii) a single selected-area electron diffraction (SAED) pattern indexed to the {111} twin plane. Acta Materialia requires conclusive crystallographic evidence for twinning, not merely suggestive planar contrast.
   *Evidence needed:* (a) Dark-field TEM imaging using at least two non-coplanar {111} reflections to confirm the twin variant; (b) STEM-HAADF imaging of the twin boundary at atomic resolution to resolve the Shockley partial sequence; (c) misorientation analysis from EBSD or nano-beam diffraction to quantify twin volume fraction as a function of strain. A single SAED pattern is not sufficient for a twinning-dominated mechanism claim in this journal.

3. **[severity: high] [location: Discussion S4.3] SFE calculation lacks rigor.**
   The stacking fault energy (SFE) is estimated using a thermodynamic model (Oliver et al.) and reported as a single value (18 mJ/m^2). Acta Materialia expects SFE to be discussed as a composition- and temperature-dependent quantity with uncertainty bounds. Moreover, the model parameters for Al in this 5-component system are not validated against experimental measurements.
   *Evidence needed:* (a) Sensitivity analysis showing how SFE varies within the compositional uncertainty of the actual alloy (measured by EPMA); (b) comparison with experimental SFE from weak-beam TEM (dissociation width of screw dislocations) or from DFT calculations for the exact composition; (c) error bar on the thermodynamic SFE value.

4. **[severity: moderate] [location: Results S3.1] Strain rate sensitivity analysis is superficial.**
   The manuscript reports strain rate sensitivity exponent m at three strain rates but does not perform a strain-rate-change test (SRCT) or extract activation volumes. For a mechanism-focused paper in Acta Materialia, the m-value alone is insufficient to distinguish between thermally activated dislocation glide and twinning nucleation as rate-controlling processes.
   *Revision path:* Either perform SRCT to extract activation volumes and compare with literature values for fcc HEAs, or reframe the strain rate discussion as phenomenological and explicitly state that the rate-controlling mechanism cannot be identified from constant-strain-rate tests alone.

### Minor comments

- Figure 6: The KAM maps in panel (c) use an inconsistent color scale compared to panels (a) and (b).
- The term "heterogeneous deformation" (Abstract, line 8) should be defined operationally -- does it refer to grain-level, twin-level, or phase-level heterogeneity?
- Reference [41] (Zhang et al., 2019) reports a different twinning sequence for the same alloy system; the discrepancy should be explicitly discussed.

**Recommendation:** Major Revision. The experimental dataset is extensive and the TEM work is commendable, but the novelty must be more sharply differentiated from the large body of Cantor-alloy literature, and the twinning mechanism claims require crystallographically conclusive evidence before they meet Acta Materialia standards.

---

## Reviewer B

**Overall assessment:** Major Revision

**Focus:** Experimental rigor, statistics, reproducibility

**Scores**

| Dimension | Score (0-5) |
|---|---|
| Innovation | 3 |
| Methodology | 3 |
| Evidence | 2 |
| Writing | 3 |
| Figure quality | 3 |
| Journal fit | 3 |

### Major comments

1. **[severity: high] [location: Methods S2.1] Tensile specimen geometry and test protocol are incompletely reported.**
   The manuscript states that "dog-bone specimens were tested in tension" but does not report: (a) gauge length and cross-section dimensions; (b) strain measurement method (extensometer vs. DIC vs. crosshead displacement); (c) strain rate values for the three test conditions; (d) number of replicates per condition. Acta Materialia requires full reproducibility of mechanical testing parameters.
   *Evidence needed:* Complete test matrix table: specimen dimensions (gauge length x width x thickness), strain measurement technique, strain rates (with units), number of replicates (minimum n = 3 per condition), and testing temperature tolerance (e.g., +/-2 K for cryogenic tests).

2. **[severity: high] [location: Results S3.2] No error bars or statistical analysis on mechanical properties.**
   All stress-strain curves are presented as single representative curves. Yield strength, UTS, and elongation values in Table 2 are reported without standard deviation or confidence intervals. For a journal of Acta Materialia's caliber, statistical reporting is non-negotiable, especially when the authors claim that the new alloy "significantly outperforms" the base Cantor alloy.
   *Evidence needed:* (a) Mean +/- SD for YS, UTS, and elongation at each temperature; (b) number of replicates; (c) statistical test (e.g., Student's t-test or ANOVA) comparing the present alloy with the baseline CoCrFeNiMn data from the literature; (d) coefficient of variation to demonstrate test reliability.

3. **[severity: high] [location: Methods S2.3] TEM sample preparation may introduce artifacts.**
   The manuscript uses twin-jet electropolishing at -40 deg C in a 10% perchloric acid + 90% ethanol solution. For HEAs with complex chemistry, electropolishing can preferentially dissolve certain elements, creating artificial contrast that may be misinterpreted as deformation substructure. No control experiment or EDS verification of the thin foil composition is presented.
   *Evidence needed:* (a) EDS spectrum from the TEM foil confirming no preferential dissolution; (b) FIB lift-out cross-section from a region adjacent to the electropolished foil to verify that the observed dislocation substructure is not an electropolishing artifact; (c) at minimum, acknowledge this as a potential limitation.

4. **[severity: moderate] [location: Results S3.4] EBSD analysis parameters are not reported.**
   The EBSD maps (Figures 5 and 7) do not report: step size, detector type, indexing confidence index threshold, number of grains analyzed, or whether surface preparation included final ion polishing. These parameters critically affect KAM resolution and twin detection reliability.
   *Evidence needed:* Full EBSD acquisition parameters and a brief description of surface preparation protocol. State the CI threshold used for grain detection and whether pseudo-symmetry correction was applied for the fcc structure.

5. **[severity: moderate] [location: Results S3.3] XRD peak broadening analysis is qualitative.**
   The manuscript attributes XRD peak broadening to "dislocation accumulation" but does not perform Williamson-Hall or Warren-Averbach analysis to extract dislocation density. Without quantitative dislocation density, the correlation between dislocation density and flow stress (Taylor hardening) cannot be evaluated.
   *Revision path:* Perform Williamson-Hall analysis to extract average dislocation density at each strain level, or rephrase the peak broadening discussion as qualitative and do not use it as quantitative evidence for dislocation accumulation.

### Minor comments

- Table 1: The actual composition measured by ICP-OES or EPMA should be reported alongside the nominal composition. As-cast HEAs often show microsegregation that affects local deformation behavior.
- Figure 3: The strain hardening rate curves (d sigma / d epsilon vs. true strain) should include error bands from replicate tests, not just a single curve.
- The cryogenic testing setup should specify the temperature stabilization time before testing and whether the specimen was fully immersed or gas-cooled.
- Supplementary information is mentioned but not provided -- all raw data for the Hall-Petch plot (Fig. S2) should be available.

**Recommendation:** Major Revision. The study addresses an interesting alloy system, but the mechanical data lack statistical rigor, the TEM sample preparation needs artifact verification, and several key characterization parameters are missing. These issues must be resolved before the results can be considered reproducible and the conclusions trustworthy.

---

## Cross-Review Synthesis

### Agreed issues

Both reviewers flagged:
- **Mechanism evidence is insufficient for Acta Materialia standards** (Reviewer A #2, Reviewer B #5): The twinning mechanism claim relies on suggestive rather than conclusive evidence. Reviewer A demands dark-field TEM and STEM-HAADF; Reviewer B identifies the XRD dislocation density analysis as missing. Both agree that the deformation mechanism narrative overreaches the available evidence.
- **SFE discussion is underdeveloped** (Reviewer A #3, Reviewer B implicitly): The stacking fault energy is central to the twinning argument but is treated as a single-point estimate without uncertainty quantification.
- **Statistical reporting is absent** (Reviewer A #4, Reviewer B #2): Both reviewers note that mechanical properties lack error bars and replicate statistics.
- **Novelty differentiation is weak** (Reviewer A #1, Reviewer B implicitly): The manuscript does not sufficiently distinguish this work from the large body of Cantor-alloy literature.

### Disagreed issues

- Reviewer A rates methodology as strong (score 4), while Reviewer B identifies multiple methodological gaps (score 3), particularly in tensile testing protocol reporting and TEM artifact control. Resolution: the methodology score should be revised downward until the testing parameters and TEM validation are fully reported -- Reviewer A's score of 4 appears to reflect the TEM imaging quality rather than the overall methodological completeness.
- Reviewer A requests SRCT / activation volume analysis; Reviewer B does not specifically request this. Resolution: this is a high-bar requirement. If the authors cannot perform SRCT, they should explicitly acknowledge it as a limitation and reframe the strain rate discussion as phenomenological. Both reviewers would accept this path if the claim language is appropriately calibrated.
- Reviewer B requests FIB validation of TEM artifacts; Reviewer A does not. Resolution: at minimum, EDS verification of the foil composition should be provided. FIB cross-section validation is strongly recommended but may be waived if the authors provide compelling EDS evidence and acknowledge the limitation.

### Combined recommendation

**Major Revision.** Priority actions:

1. Build a comprehensive comparison table differentiating this alloy from all published CoCrFeNiMnAl variants -- mechanical properties, deformation mechanisms, and SFE values.
2. Provide crystallographically conclusive evidence for deformation twinning: dark-field TEM with multiple reflections, STEM-HAADF of twin boundaries, and twin volume fraction quantification.
3. Report complete tensile testing parameters (specimen geometry, strain measurement, strain rates, n >= 3 replicates) and add mean +/- SD for all mechanical properties with statistical comparison to baseline Cantor alloy.
4. Quantify SFE with uncertainty bounds: sensitivity analysis for composition variation, comparison with experimental (weak-beam) or DFT values.
5. Verify TEM foil integrity via EDS from the thin foil region; acknowledge electropolishing artifact risk.
6. Report full EBSD acquisition parameters and perform Williamson-Hall or Warren-Averbach analysis for quantitative dislocation density, or rephrase as qualitative observations.
7. If SRCT cannot be performed, reframe the strain rate discussion and add a limitations paragraph.
