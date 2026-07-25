# Example: True Negative Result (GATA4 / VSD)

**Variant**: chr8:11703860:G>T **Phenotype**: Ventricular Septal Defect
(Alleged) **Verdict**: **Likely Benign / No Functional Effect**

## Why this is a good example

This analysis demonstrates a **True Negative** result where:

1.  **Statistical Artefacts**: The Discovery Scan reported high quantiles
    (~0.99) for Heart RNA-seq, which can be misleading.
2.  **Magnitude Check**: The Raw Scores were negligible (~0.01 or <1% change),
    revealing the "significance" was likely due to low variance in the model
    background rather than true biological impact.
3.  **Visual Confirmation**:
    -   **Whole-Gene Plot**: Shows identical REF/ALT expression profiles.
    -   **Detail Plot**: Shows preserved chromatin accessibility (DNASE) at the
        variant site.
    -   **ISM**: Shows minimal motif disruption logic.

## Key Takeaway

Always verify *statistically significant* hits (High Quantile) with
**Magnitude** (Raw Score) and **Visual Inspection**. If the raw score is low and
the plot shows no change, the Quantile is a false alarm.
