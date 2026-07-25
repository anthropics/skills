# Splicing Analysis Examples

This directory contains verified examples of successful splicing analyses and
reports.

## Examples

### 1. Exon Skipping (Donor Disruption) - *DLG1*

-   **Report**: [dlg1_report.md](dlg1_report.md)
-   **Plot**: [dlg1_exon_skipping.png](dlg1_exon_skipping.png)
-   **Key Feature**: **Hybrid Zoom**. Notice how the plot zooms out (~9kb) to
    show the full skipping event and its anchor exons, rather than just the
    variant's immediate vicinity. This is critical for visualizing skipping.

### 2. Exon Extension (Cryptic Donor) - *COL6A2*

-   **Report**: [col6a2_report.md](col6a2_report.md)
-   **Plot**: [col6a2_exon_extension.png](col6a2_exon_extension.png)
-   **Key Feature**: **Site Shift**. The Sashimi arcs and Splice Site tracks
    clearly show the donor site moving 60bp downstream.

## Best Practices Checklist

-   **Deduplication**: Ensure redundant RNA-seq tracks (Total vs PolyA) are
    filtered.
-   **Raw Counts**: Sashimi plots should show raw integer counts (not
    normalized) for clarity.
-   **Strand Aware**: Always verify the gene strand and filter tracks
    accordingly.
-   **Dynamic Zoom**: Use the "Hybrid Span" logic (Junctions + Anchors) for
    skipping events, but tighter zooms for local shifts (extensions).
