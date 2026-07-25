# Example: True Negative Result (TGFB3 / ARVC)

**Variant**: chr14:75958692:G>A **Gene**: *TGFB3* **Phenotype**: Arrhythmogenic
Right Ventricular Cardiomyopathy (ARVC) **Verdict**: **Likely Benign Regulatory
Effect / Protein-Coding Mechanism?**

## Why this is a good example

This analysis demonstrates a **True Negative for Regulatory Disruption** where:

1.  **Low Signal**: Discovery scores were universally low (<0.1), unlike the
    GATA4 example which had high quantiles but low magnitude. Here, both were
    low.
2.  **Visual Confirmation**:
    -   **Whole-Gene Plot**: Shows identical expression profiles.
    -   **Detail Plot**: Shows stable chromatin.
    -   **ISM**: Empty matrices for ATAC, indicating no sensitive enhancer logic
        at this site.

## Key Takeaway

When a known disease gene (*TGFB3*) shows **zero regulatory impact** in relevant
tissue models (Heart), consider:

1.  **Protein-Coding Effect**: Is it a missense variant? (AlphaGenome only
    scores regulatory potential).
2.  **Missing Context**: Is it a cryptic splicing event not captured? (Splicing
    scores were also low here).
3.  **Benign**: It might just be a benign variant in a disease gene.
