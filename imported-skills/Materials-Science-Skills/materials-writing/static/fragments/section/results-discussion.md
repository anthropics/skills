# Results and Discussion

> **Domain context**: The `domain` axis has loaded domain-specific writing guidance for [detected domain]. The structure below is general; the domain guide contains field-specific characterization expectations and mechanism evidence standards. Use both together.

Each results/discussion paragraph should move through the evidence chain in this order:

1. **Observation** — describe what was seen or measured.
2. **Quantified result** — report the number with units, replicate count, and uncertainty where available.
3. **Mechanism evidence** — interpret the result using characterization data. Do not jump into mechanism language before the result is clear.
4. **Alternative explanation** — acknowledge a competing interpretation and explain why the evidence favors the preferred one.
5. **Boundary** — state the condition, scale, or measurement limit that bounds the claim.

## Hard rules

- Do not discuss mechanism before the result is clear.
- Do not infer mechanism from performance alone. Link each performance trend to characterization evidence.
- Keep claims near the data that support them; do not stack claims at the top and leave evidence at the bottom.
- Every paragraph carries one message only: result, comparison, mechanism, or Limitation.

## Domain characterization reminders

- **Civil materials**: FTIR, SEM, fluorescence microscopy, rheology, TGA/DSC.
- **Ceramics**: XRD, SEM/TEM, EDS, density/porosity, Weibull analysis.
- **Metals**: OM, SEM, EBSD, TEM, XRD, fractography, hardness.
- **Polymers**: DSC, TGA, DMA, FTIR, SEM, rheology.
- **Functional**: XRD, Raman, XPS, TEM, UV-vis, electrochemical impedance.
- **Nanomaterials**: TEM (with size statistics), SEM, XRD (Scherrer), DLS, UV-vis, Raman.

## Domain checklist

- [ ] Does each key result have a corresponding characterization evidence?
- [ ] Are error bars or confidence intervals reported for all quantitative data?
- [ ] Is a competing explanation addressed (not just the preferred mechanism)?
- [ ] Is the comparison with literature fair (same material system, test condition, scale)?

## Record-driven Results drafting

If `experiment-record.yaml` is available, use `results-from-record.md` to generate a first draft of the Results section. Map each run in `design.runs` to a data statement, and leave `[needs quantitative result]` placeholders where measured values are missing.
