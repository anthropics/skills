# Example: Model Limitation (RNA Secondary Structure)

**Variant**: chr2:121530927:G>A **Gene**: *RNU4ATAC* (U4atac snRNA)
**Phenotype**: Roifman Syndrome **Mechanism**: **RNA Secondary Structure /
Stability (Post-Transcriptional)**

## Why this is a Critical Example

This analysis illustrates a specific **Blind Spot** of the model:

1.  **The Signal**: The variant has **High Quantiles (0.998)** but **Low Raw
    Scores (~0.01)**.
2.  **The Reality**: A high quantile with a near-zero raw score typically
    reflects low variance in the model's background predictions for that
    track—it is a statistical artifact, not a meaningful biological signal.
    Furthermore, the model does **not** simulate the physical folding of the RNA
    molecule.
3.  **True Mechanism**: Variants in snRNAs often affect **secondary
    structure/folding**, preventing proper spliceosome assembly. This is a
    **post-transcriptional physics** problem, not a DNA-to-RNA transcription
    problem.

## Key Takeaway

**AlphaGenome is a DNA-to-Expression model, not an RNA Folding model.**

-   If the agent is analyzing an **ncRNA** (snRNA, tRNA, rRNA), it must
    acknowledge that AlphaGenome predicts transcription from DNA, but does
    **not** simulate post-transcriptional RNA folding or secondary structure
    stability.
-   **Strict Rule**: A pattern of **High Quantile + Low Raw Score** should be
    reported as **"No Significant Molecular Effect Predicted by AlphaGenome"**.
    Do not invent proxy mechanisms (e.g., "structural importance") based on
    statistical artifacts.
-   Do not over-interpret "Regulatory" scores for mechanisms that occur *after*
    transcription. The true pathogenic mechanism (e.g., RNA folding defect) is
    likely invisible to the model.
