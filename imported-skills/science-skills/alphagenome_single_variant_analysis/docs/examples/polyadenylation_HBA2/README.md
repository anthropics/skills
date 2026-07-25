# Example: Polyadenylation Signal Disruption (HBA2 / Alpha-Thalassemia)

**Variant**: chr16:173692:A>G **Gene**: *HBA2* (3' UTR) **Phenotype**:
Hemoglobin H Disease / Alpha-Thalassemia **Mechanism**: **Disruption of PolyA
Signal (`AATAAA` -> `AATAAG`)**

## Why this is a good example

This analysis demonstrates a textbook **3' End Processing Defect**:

1.  **Discovery Signal**: The strongest hits (+1.07) are in **Splice Junctions**
    tracks (K562). In the 3' UTR context, this indicates **failure to
    terminate** or read-through, rather than splicing of introns.
2.  **ISM Smoking Gun**: The ISM analysis for RNA-seq/Splicing unequivocally
    identifies the **`AATAAA` hexamer** as the critical motif (Score 2.45) which
    is destroyed by the variant.
3.  **Visuals**: The Regulatory plots show the disruption at the transcript end.

## Key Takeaway

When analyzing 3' UTR variants:

-   Look for **Splice Junction** scores (indicating read-through).
-   Look for **RNA-seq** changes (stability).
-   Use **ISM** to check for `AATAAA` or `ATTAAA` motifs. This is often the
    "smoking gun" for regulatory pathology in 3' UTRs.
