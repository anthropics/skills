# Report Templates

This file provides simplified templates for reporting AlphaGenome variant
analysis results. Follow the structure below to ensure all critical sections are
covered.

> [!IMPORTANT] **DO NOT** use the agent's default artifact directory for this
> report. Save it as a regular file named `report.md` directly in the variant's
> output directory (e.g., `analysis_chr1_12345_A_G/report.md`) in the workspace.
> Use relative paths for embedded plots (`filename.png`).

--------------------------------------------------------------------------------

## 1. Standard Analysis Report Template

Use this template for variants that show significant functional effects.

```markdown
# Analysis Report: {variant_str} ({gene_name})

## 1. Summary of Findings
[Detailed biological narrative, not generic. State gene function, specific mechanism (e.g., "Pseudo-exon", "Enhancer Disruption"), and effect with raw scores. Quantify effect in biological terms (e.g., fold-change) rather than just citing raw scores or quantiles.]

## 2. Genomic Context
- **Variant**: {variant_str}
- **Gene**: {gene_name} ({ENSG_ID})
- **Location**: [e.g., Promoter, 5' UTR, Exon, Intron, 3' UTR]
- **Disease**: {disease_name} (if applicable)

## 3. Discovery Hits & Disease-Relevant Scores
[Table of top hits from discovery scan, limited to top 15-20. Include disease-relevant tissues even if they are not top hits.]

| Biosample Name | Gene Name | Output Type | Raw Score | Quantile Score |
| :--- | :--- | :--- | :--- | :--- |
| [Tissue] | [Gene] | [Modality] | [Score] | [Quantile] |

*Note: Discuss any disease-relevant tissues that were not in the top hits but show significant effects.*

## 4. Plots and Visual Analysis
[Embed all plots generated using standard markdown syntax: `![caption](filename.png)`. Every ISM plot must have a specific interpretation caption. If visual inspection is ambiguous for AI agents, state the reliance on quantitative scores.]

![Main View](plot_{tissue}_{gene}_effects.png)
*Fig 1: Main view showing [modality] tracks.*

![Detail View](plot_{tissue}_{gene}_detail.png)
*Fig 2: Detail view centered on variant.*

![ISM Plot](ism_{tissue}_{modality}.png)
*Fig 3: ISM SeqLogo showing [motif description].*

## 5. Hypothesis Evaluation
[Explicitly state whether the hypothesis is SUPPORTED, REFUTED, or PARTIALLY SUPPORTED by the model scores.]

## 6. Primary Molecular Mechanism
[Synthesize the causal pathway: e.g., Variant disrupts X motif → causes chromatin closure → reduces expression of Y gene.]

## 7. Limitations
[State model blind spots (e.g., secondary structure, protein folding) and any unresolved questions or data gaps (e.g., missing modalities, proxy tissues used).]

## 8. Conclusion
[Narrative synthesis addressing primary finding, mechanism, biological impact, and confidence.]
```

--------------------------------------------------------------------------------
