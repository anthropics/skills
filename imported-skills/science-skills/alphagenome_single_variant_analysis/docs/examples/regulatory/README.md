# Regulatory Analysis Examples

This directory contains verified examples of successful regulatory variant
analyses (Promoters, Enhancers).

## Examples

### 1. Promoter Variant (Expression gain/loss) - *APOA1*

-   **Report**: [apoa1_promoter/report.md](apoa1_promoter/report.md)
-   **Plots**:
    -   [Liver Tracks (Clinical)](apoa1_promoter/plot_liver_APOA1_effects.png)
    -   [Heart Tracks (Top Hit)](apoa1_promoter/plot_heart_left_ventricle_APOA1_effects.png)
    -   [Liver ISM](apoa1_promoter/ism_liver_RNA_SEQ.png)
-   **Key Features**:
    -   **Promoter Zoom**: Minimal zoom (~200bp) to show local chromatin
        changes.
    -   **Modality Integration**: Concordant RNA-seq and DNASE/ChIP changes.
    -   **Tissue Specificity**: Comparing Clinical Target (Liver) vs Top
        Discovery Hit (Heart).
    -   **ISM**: Identifying disrupted motifs.

## Best Practices

-   **Local Zoom**: Use tight 200bp windows for DNASE/ChIP to see local shape.
-   **Separate Plots**: Do not combine RNA-seq (gene-scale) and DNASE
    (local-scale) on the same X-axis unless they align perfectly; separate files
    are often cleaner.
-   **ISM**: Always run ISM for strong regulatory hits to identify the
    transcription factor involved.
