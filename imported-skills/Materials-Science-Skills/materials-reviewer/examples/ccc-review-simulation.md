# CCC Review Simulation

Simulated peer review for a manuscript submitted to *Cement and Concrete Composites*.
Manuscript topic: "Hydration mechanism of ternary blended cement incorporating fly ash and limestone powder: multiscale characterization and kinetic modeling."

---

## Reviewer A

**Overall assessment:** Minor Revision

**Scores**

| Dimension | Score (0–5) |
|---|---|
| Innovation and contribution | 4 |
| Methodology soundness | 4 |
| Evidence completeness | 3 |
| Writing quality | 4 |
| Figure/table quality | 4 |
| Journal fit | 5 |

### Major comments

1. **[severity: moderate] [location: Results §3.2] XRD quantification method not specified.**
   The manuscript reports phase evolution from XRD but does not state whether Rietveld refinement or the reference intensity ratio (RIR) method was used. CCC expects quantitative phase analysis (QPA) to be methodologically explicit, especially for ternary systems where carbonate participation affects AFm / C-S-H balances.
   *Evidence needed:* State the QPA method, Rwp value if Rietveld, and whether an internal standard was used.

2. **[severity: moderate] [location: Discussion §4.1] Mechanism narrative overreaches single-technique evidence.**
   The claim that "limestone accelerates early fly ash dissolution through pH buffering" is supported only by FTIR peak shifts. This is a multi-step mechanism that requires at least two orthogonal techniques (e.g., solution chemistry + ²⁹Si NMR, or isothermal calorimetry + TGA).
   *Revision path:* Either add supporting evidence from a second technique or rephrase as "FTIR data are consistent with the hypothesis that limestone modifies the early dissolution environment of fly ash."

### Minor comments

- Figure 5: The DTG peaks should be labeled with temperature values.
- The term "synergistic effect" (Abstract, line 12) should be replaced with a more precise description of what specifically is synergistic.
- Equation 3: the Avrami exponent n is discussed but the fitting range is not stated.

**Recommendation:** Minor Revision. The multiscale approach is well suited to CCC, and the experimental design is sound. The main issues are methodological transparency and mechanism claim calibration.

---

## Reviewer B

**Overall assessment:** Major Revision

**Scores**

| Dimension | Score (0–5) |
|---|---|
| Innovation and contribution | 3 |
| Methodology soundness | 3 |
| Evidence completeness | 3 |
| Writing quality | 3 |
| Figure/table quality | 3 |
| Journal fit | 5 |

### Major comments

1. **[severity: high] [location: Methods §2.3] Kinetic modeling lacks validation.**
   The kinetic model (Section 2.3) is fitted to heat release data, but no validation dataset is used. CCC expects kinetic models to be cross-validated against at least one independent measurement (e.g., bound water from TGA, or degree of reaction from backscattered SEM).
   *Evidence needed:* Compare model-predicted degree of reaction with an independent measurement at 1, 3, 7, and 28 days.

2. **[severity: high] [location: Results §3.4] Carbonate participation not decoupled from filler effect.**
   The manuscript attributes enhanced early strength to "chemical participation of limestone" but does not distinguish between the chemical effect (carboaluminate formation) and the physical filler effect (nucleation sites). A control mix with inert filler (e.g., quartz powder at equivalent particle size) is needed to decouple these contributions.
   *Revision path:* If a quartz control is unavailable, acknowledge this as a limitation and soften the claim to "the presence of limestone is associated with earlier carboaluminate detection, which may reflect both chemical and nucleation contributions."

3. **[severity: moderate] [location: Results §3.3] NMR deconvolution protocol.**
   The ²⁹Si MAS NMR deconvolution shows Qⁿ species distribution but the fitting constraints (number of peaks, linewidth range, chemical shift ranges) are not reported. These significantly affect the resulting Qⁿ fractions.
   *Evidence needed:* Report fitting parameters and, ideally, show the residual fit.

### Minor comments

- Table 3: The "total porosity" values from MIP should include the measurement pressure range.
- Figure 7: The calorimetry plot needs a legend distinguishing all curves.
- The abbreviation "FA" is ambiguous (fly ash vs. fatty acid)—define at first use and consider using "Class F FA" or similar.

**Recommendation:** Major Revision. The topic is excellent for CCC, but the kinetic model validation and limestone decoupling are essential for the mechanism claims to be convincing.

---

## Cross-Review Synthesis

### Agreed issues

Both reviewers flagged:
- **Mechanism claims need stronger multi-technique support** (Reviewer A #2, Reviewer B #2): The limestone participation narrative requires either additional evidence or claim downgrade.
- **Methodological transparency** (Reviewer A #1, Reviewer B #3): Both XRD quantification and NMR fitting protocols need more detail.

### Disagreed issues

- Reviewer A rates the methodology as sound (score 4), while Reviewer B identifies the kinetic model as unvalidated (score 3). Resolution: add cross-validation data or clearly state the validation scope and limitations.
- Reviewer B requests a quartz control mix; Reviewer A does not. Resolution: if the control is unavailable, acknowledge as a limitation—both reviewers would accept this if the claim is appropriately softened.

### Combined recommendation

**Minor-to-Major Revision** (leaning toward Minor if the authors can address the mechanism claim calibration). Priority actions:

1. Soften the limestone mechanism claim or add a second orthogonal technique to support it.
2. Report XRD QPA method details (Rietveld Rwp or RIR protocol).
3. Cross-validate the kinetic model against at least one independent measurement.
4. Report NMR deconvolution fitting constraints.
5. If no quartz control exists, add a limitations paragraph and adjust the limestone participation language.
