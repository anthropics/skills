# Experiment Revision and Remediation Guide

This reference guide outlines strategies for responding to reviewer requests for additional experiments. It details the preferred remediation when data can be acquired, and the mitigation strategy (scientific limitation framing) when experiments are not feasible.

**Evidence gate**: Do not write that an experiment, figure, table, p-value, citation, or page/line location exists unless the user/source has provided it. Use `[AUTHOR_INPUT_NEEDED: ...]` for missing status, data, or locations.

---

## 1. Mechanism Evidence Remediation

### 1.1 Chemical/Phase Structure (FTIR, XRD)
- **Reviewer Concern**: "Mechanism speculative," "Chemical bonding not verified," "Mineral phase evolution unclear."
- **Strong Revision (If possible)**:
  - Collect FTIR spectra at key reaction/aging stages. Use peak-area ratios (e.g., carbonyl index) to quantify changes.
  - Collect XRD patterns. If mineral phase fractions are claimed, perform TGA or isothermal calorimetry to support XRD phase assignments.
- **Mitigation if Unavailable (No equipment/materials)**:
  - Acknowledge that the proposed mechanism remains an inference.
  - Soften claims in the manuscript from "proven by" to "consistent with" or "suggested by."
  - Reference established literature on similar systems to justify the proposed reaction path.
  - *Template*: "While direct [method] evidence would be valuable, it is currently constrained by [confirmed reason]. We have therefore softened our mechanism claims in Section [X] (Page [P], Lines [L-L]) to present this pathway as a hypothesis consistent with [available evidence], and cited [verified literature] to support the transition. [AUTHOR_INPUT_NEEDED: verify location and citation.]"

### 1.2 Microstructure & Interface Morphology (SEM/EDS, TEM)
- **Reviewer Concern**: "Interfacial quality not shown," "Dispersion quality of modifier is questionable."
- **Strong Revision (If possible)**:
  - Prepare polished cross-sections or liquid-nitrogen fractured surfaces.
  - Take SEM micrographs at multiple magnifications. Add EDS mapping if elemental distribution at the interface is critical.
- **Mitigation if Unavailable**:
  - Provide optical microscopy if available.
  - If no micro-imaging can be done, rely on macroscopic physical markers (e.g., density, absorption, mechanical failure mode shift) to infer interface quality.
  - *Template*: "We agree that direct [imaging method] evidence would clarify [specific concern]. Due to [confirmed constraint], we could not acquire new images. To address the underlying concern, we have used [available alternative evidence] in Section [X] (Page [P], Lines [L-L]) and noted the missing micro-scale mapping as a limitation. [AUTHOR_INPUT_NEEDED: verify alternative evidence and location.]"

---

## 2. Performance Evidence Remediation

### 2.1 Environmental Durability (Aging, Freeze-Thaw, Acid Attack)
- **Reviewer Concern**: "Durability not verified," "Long-term performance under moisture conditioning is questionable."
- **Strong Revision (If possible)**:
  - Perform standard durability conditioning (e.g., AASHTO T 283 for moisture, freeze-thaw cycles, or oven aging).
  - Measure property retention ratios (strength, mass, or modulus retention) and report with replicates ($n \ge 5$).
- **Mitigation if Unavailable**:
  - Narrow the scope of the conclusions to short-term/ambient performance.
  - Add a dedicated durability limitation paragraph in the discussion.
  - *Template*: "We acknowledge that long-term environmental durability is important for field implementation. The current study bounds its scope to [confirmed scope]. We have modified the Introduction and Section [X] (Page [P], Lines [L-L]) to explicitly limit our conclusions to [scope boundary] and added [future work/limitation statement]. [AUTHOR_INPUT_NEEDED: verify scope and location.]"

### 2.2 Viscoelastic/Flow Behavior (Rheological, MSCR, Amplitude Sweep)
- **Reviewer Concern**: "Rheological properties not reported," "Binder viscosity not measured."
- **Strong Revision (If possible)**:
  - Perform dynamic shear rheometer (DSR) temperature-frequency sweeps.
  - Report MSCR parameters ($J_{nr}$, $R$) at standard pavement temperatures.
- **Mitigation if Unavailable**:
  - Use conventional binder indicators (e.g., penetration, softening point, ductility) to approximate shear resistance, citing empirical correlations from literature.
  - *Template*: "We agree that [requested method] would provide complementary evidence for [property]. Because [confirmed constraint], we used [available alternative evidence] and clearly state its limits in Section [X] (Page [P], Lines [L-L]). [AUTHOR_INPUT_NEEDED: verify method constraint, alternative evidence, and standard/citation.]"

---

## 3. Statistical and Benchmarking Evidence

### 3.1 Replicate Count & Variability
- **Reviewer Concern**: "Sample size too small," "No error bars," "Statistical significance not proven."
- **Strong Revision (If possible)**:
  - Increase replicate count to $n \ge 5$ for mechanical tests or $n \ge 3$ for micro-characterization.
  - Add standard deviation error bars to all performance plots. Summarize means, standard deviations, and coefficients of variation in a table.
- **Mitigation if Unavailable (No samples left)**:
  - Report standard deviation for existing replicates. If $n$ is small (e.g., $n=3$), acknowledge the statistical limitation.
  - Perform a t-test on existing data to see if a significant trend exists despite the small sample size, and report the p-value with a warning.
  - *Template*: "We apologize for the omission of variability indicators. We have updated Figure/Table [X] to include [SD/SE/CI] based on the confirmed replicate count ($n=[N]$). Where the sample size is limited, we now describe the result as [trend/preliminary evidence] and avoid unsupported significance claims. [AUTHOR_INPUT_NEEDED: verify replicate count and statistical test output.]"

### 3.2 Literature Benchmarking
- **Reviewer Concern**: "How does this modifier compare with commercial benchmarks?"
- **Strong Revision (If possible)**:
  - Test a commercial benchmark (e.g., SBS-modified or styrene-butadiene rubber modified binders) under the exact same conditions.
  - Add a comparison row to all performance tables.
- **Mitigation if Unavailable**:
  - Compile a literature comparison table containing reported values for similar binders tested under equivalent standards, noting differences in base binder or modifier dose.
  - *Template*: "To address this, we have incorporated a literature comparison table (Table [X]) in Section [Y]. This table compares [metric] with verified studies using comparable methods. While we could not test [benchmark] due to [confirmed reason], the literature comparison places our results within the reported performance range. [AUTHOR_INPUT_NEEDED: verify references, metrics, and location.]"
