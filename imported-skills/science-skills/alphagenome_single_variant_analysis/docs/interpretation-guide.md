# Interpretation Guide

This guide covers biological interpretation, signal patterns, motif analysis,
and the pre-report reasoning checklist. Read this before writing any report.

--------------------------------------------------------------------------------

## Signal Patterns Reference

Use this table to identify mechanisms from model outputs.

### Expression & Regulatory

Some example mechanisms (non-exhaustive, use your reasoning ability):

| Mechanism       | Location          | Key Signals        | ISM Check        |
| :-------------- | :---------------- | :----------------- | :--------------- |
| **TF Binding    | Promoter/TSS or   | DNASE loss (narrow | Disrupted TF     |
: Loss**          : Enhancer          : peak) + RNA-seq    : motif (Strong    :
:                 :                   : loss               : REF)             :
| **TF Binding    | Promoter/TSS or   | DNASE gain (narrow | Created TF motif |
: Site Creation** : Enhancer          : peak) + RNA-seq    : (Strong ALT)     :
:                 :                   : gain               :                  :
| **Enhancer      | Distal            | DNASE loss         | Disrupted TF     |
: Disruption**    :                   : (distal) + RNA-seq : motif (Strong    :
:                 :                   : loss (linked       : REF)             :
:                 :                   : gene).             :                  :
:                 :                   : H3K27ac/p300 loss  :                  :
:                 :                   : confirms.          :                  :
| **Enhancer      | Distal            | DNASE gain         | Created TF motif |
: Creation**      :                   : (distal) + RNA-seq : (Strong ALT)     :
:                 :                   : gain (linked       :                  :
:                 :                   : gene).             :                  :
:                 :                   : H3K27ac/p300 gain  :                  :
:                 :                   : confirms.          :                  :
| **TSS Shift**   | 5' UTR            | RNA-seq shape      | —                |
:                 :                   : change (5' end) or :                  :
:                 :                   : CAGE peak shift    :                  :
| **uORF          | 5' UTR            | Context-dependent: | —                |
: Creation**      :                   : may show weak      :                  :
:                 :                   : Expression score.  :                  :
:                 :                   : Verify ATG         :                  :
:                 :                   : creation in 5'     :                  :
:                 :                   : UTR.               :                  :
| **mRNA          | 3' UTR (Note:     | RNA-seq loss       | —                |
: Stability**     : Model does not    : WITHOUT            :                  :
:                 : explicitly model  : chromatin/splicing :                  :
:                 : this, unlikely to : defects. Possible  :                  :
:                 : reliably pick up) : miRNA binding site :                  :
:                 :                   : alteration.        :                  :
| **Statistical   | Any               | High Quantile      | Empty/noise      |
: Artifact**      : (low-expression   : (>0.999) + Zero    :                  :
:                 : genes)            : Plot Difference.   :                  :
:                 :                   : Caused by variance :                  :
:                 :                   : stabilization in   :                  :
:                 :                   : low-signal         :                  :
:                 :                   : regions.           :                  :

### Splicing

| Mechanism             | Key Signals              | Junction Evidence         |
| :-------------------- | :----------------------- | :------------------------ |
| **Exon Skipping**     | Low Splice Site at       | Junction connects         |
:                       : junction + new junctions : flanking exons, bypassing :
:                       : spanning skipped exon    : variant                   :
| **Intron Retention**  | Low Splice Site + high   | —                         |
:                       : RNA-seq in intron        :                           :
:                       : (read-through)           :                           :
| **Cryptic Exon        | New Splice Site (high    | Junction starts/ends near |
: (Pseudo-exon)**       : score) + new junctions   : variant                   :
:                       : flanking cryptic exon    :                           :
| **Exon Extension**    | New donor/acceptor near  | Junction shifted by N bp  |
:                       : existing site            : from canonical            :
| **PolyA Signal Loss** | 3' UTR variant: high     | AATAAA motif in ISM       |
:                       : Splice Junctions         :                           :
:                       : (read-through) + RNA-seq :                           :
:                       : loss                     :                           :

### Splicing Interpretation Rules

-   **Specific mechanisms only**: Do NOT write "likely exon skipping or intron
    retention" if data allows you to distinguish. Use the junction coordinates.
-   **Proxy signals**: If Expression Loss (-0.999) >>> Splicing Disruption
    (0.99), the primary mechanism is likely transcriptional (promoter/enhancer
    loss), not splicing. Exception: clearly aberrant new splice junction.
-   **Complex outcome**: If multiple new cryptic sites compete with canonical
    site, describe as "complex outcome of new candidate sites."

--------------------------------------------------------------------------------

## Tissue and Location Verification

-   **Verify Tissue Lineage**: Both top hits and disease-relevant tissues are
    valuable. Do NOT ignore unexpected top hits (e.g., "Mesenchymal Stem Cell"
    for an erythroid gene), as they may reveal regulatory potential. However,
    you MUST also search for and include the expected disease-relevant tissues
    (e.g., K562/Erythroblast) to ensure the report directly addresses the
    clinical context.
-   **Verify Tissue Relevance**:
    -   **Match Disease to Organ System**: If the disease is "Cardiomyopathy",
        you MUST use "heart", "atrium", "ventricle", or "cardiomyocyte".
    -   **Avoid Generic Proxies**: Do NOT use "Smooth Muscle Cell" for Heart
        (Cardiac Muscle != Smooth Muscle). Do NOT use "Fibroblast" for Brain.
    -   **Search Strategy**: If a specific cell type query (e.g.,
        "cardiomyocyte") yields 0 hits, **search for the organ** (e.g., "heart",
        "cardiac"). While you should report unexpected top hits in other
        tissues, ensure you also include the relevant organ/tissue to address
        the clinical context.
-   **Verify Location (GTF Overlap)**: Do NOT guess "Promoter" vs "5' UTR".
    Check the GTF coordinates. A variant at -30 might be in the 5' UTR if the
    TSS is upstream. Use `lookup_gene_info.py --coord='chr:pos'` or `bedtools
    intersect` to confirm.

--------------------------------------------------------------------------------

## Score Interpretation

### Raw Score vs Quantile Score

-   **Raw score**: Effect magnitude, scorer-specific scale. Use for comparing
    tissues WITHIN the same scorer only.
-   **Quantile score**: Percentile rank vs common variants. Use to assess
    significance. Saturates at ±0.999990.
-   See [variant-scoring-info section in alphagenome-api.md](alphagenome-api.md)
    for mathematical details.

### Magnitude Rules

> [!NOTE] **Disclaimer**: The interpretation of raw scores depends heavily on
> the specific modality and assay type. The thresholds below are general rules
> of thumb, primarily derived from RNA-seq data, and should not be treated as
> absolute rules. Always validate quantitative scores by visually inspecting the
> plotted tracks.

-   **< 0.1**: Typically indicates **No Significant Effect** or background
    noise, even if the quantile score is high.
-   **0.1 - 0.5**: Often represents a subtle or weak effect. Report as a
    potential subtle change.
-   **0.5 - 1.0**: Suggests a moderate effect (roughly corresponding to a 1.4-2x
    fold change in RNA-seq).
-   **> 1.0**: Strong effect (generally >2x fold change for RNA-seq).
-   **RNA-seq raw_score ≈ log2 fold-change**: -4 ≈ 16-fold reduction, -1 ≈
    2-fold reduction, -0.35 ≈ 1.27-fold reduction.
-   **NO percentage interpretation**: Raw scores are NOT percentages. Do not
    interpret "0.09" as "9%".
-   **Relative Magnitude**: Use relative comparisons (e.g., "low magnitude
    compared to TERT's 1.5") or qualitative terms (e.g., "marginal effect").
-   **Always cite the raw score** in reports (e.g., "Raw Score -1.89").

### High Quantile + Low Raw Score

This is the most common trap. A quantile of 0.99+ with |raw_score| < 0.1 is
effectively **NO MOLECULAR EFFECT**. This occurs in low-expression genes where
variance stabilization inflates quantiles. Report as "No Significant Effect" and
explain the statistical artifact.

## Negative Results & Scientific Integrity

> [!CRITICAL] **Most variants are Benign.** Do not "stretch" to find a mechanism
> where none exists.

-   **Value of Negative Results**: Reporting "AlphaGenome predicts NO molecular
    effect" is a valuable scientific finding.
-   **Strict Anti-Speculation**: Do not invent mechanisms (e.g., "cryptic splice
    site", "enhancer disruption") unless explicitly shown by the model. If
    distinct evidence is missing, use broad terms like "predicted splicing
    disruption".
-   **Occupancy ≠ Disruption**: A variant landing in an active enhancer (e.g.,
    H3K27ac peak present) or promoter (e.g. before gene TSS) does not imply
    disruption. If REF and ALT tracks are identical and scores are near zero,
    the variant has no predicted effect. Do not claim disruption based on
    location alone.
-   **Model Limitations**: AlphaGenome is a DNA-to-molecular phenotype model but
    has limited scope of modeled molecular phenotypes. For example, it does NOT
    model:
    -   **Post-Transcriptional RNA Biology**: Beyond splicing (e.g., RNA
        secondary structure folding, macromolecular assembly, transport).
    -   **miRNA Processing**: Due to low abundance or short length of
        transcripts.
    -   **Protein Coding Effects**: Missense, nonsense, or frameshift mutations
        affecting protein structure or function.
    -   **Developmental Specificity**: Effects restricted to specific
        developmental timeframes not represented in the training data.
    -   **Environmental or Dynamic Contexts**: Effects triggered by specific
        external stimuli or dynamic cell states not captured by the static
        biosample profiles.

--------------------------------------------------------------------------------

## ISM (In-Silico Mutagenesis) Interpretation

### Reading SeqLogo Plots

-   **Tall letters at variant position**: Mutation directly disrupts an
    important motif.
-   **Positive height** = activating when present; **Negative** = repressive.
-   **REF vs ALT**: Strong REF letter → ALT disrupts binding site. Strong ALT
    letter → ALT creates new binding site.

### Motif Identification Rules

Use your base knowledge about sequences (semantic knowledge) to identify motifs
when available. For well-known canonical sequences, you can identify directly:

Motif                | Sequence        | Context Required
-------------------- | --------------- | -------------------------
TATA Box             | TATAAA / TTTATA | Verify in Promoter
PolyA Signal         | AATAAA / TTTATT | Verify in 3' UTR
Splice Donor         | GT              | Verify at intron boundary
Splice Acceptor      | AG              | Verify at intron boundary
E-box (MYC/MAX)      | CACGTG          | —
GRE (Glucocorticoid) | TGTTCT          | —

For less obvious sequences: use your knowledge of TF motifs, and if no confident
match is found, report the **consensus sequence** with "resembles" or
"potential" qualifier (e.g., "Disrupted motif resembling GATA consensus").

### Reverse Complement

ALWAYS check the reverse complement. The model sees double-stranded DNA, so the
motif may be on the minus strand (e.g., AATAAA ↔ TTTATT).

### Negative ISM

If the ISM plot shows only tiny bars (<0.1 height) or random noise, report **"No
specific motif disruption identified."** Do not force a match.

--------------------------------------------------------------------------------

## Model Limitations

AlphaGenome predicts transcription and splicing from DNA sequence. It does NOT
model:

-   **miRNA processing** (low abundance / short length)
-   **RNA secondary structure** (e.g., 3' UTR selenocysteine insertion
    sequences, snRNA stem-loops)
-   **Protein folding or stability** (missense effects)
-   **Catalytic activity** (variant may produce stable but non-functional RNA)
-   **Developmental timing** or **stress-response** contexts

**Rules:**

-   If the gene is a **non-coding RNA** (snRNA, tRNA, rRNA) and you see High
    Quantile + Low Raw Score: report "No Significant Effect" and state the
    structural limitation.
-   If the known mechanism is **protein stability**: state that benign
    regulatory scores do not rule out protein-level pathogenicity.
-   If the known mechanism is **enzymatic/catalytic**: do not rule out
    pathogenicity from neutral expression scores.

--------------------------------------------------------------------------------

## Ontology Resolution Best Practices

The `resolve_ontology_terms` script implements smart matching. Key principles:

1.  **Specificity first**: Prefer "Naive thymus-derived CD4-positive..." over
    generic "T-cell".
2.  **No silent fallbacks**: Better to return `[NOT FOUND]` than silently map
    "Kupffer cell" → "Liver".
3.  **You bridge disease → tissue**: The script matches terms, not diseases. You
    must identify that "Multiple Sclerosis" → Oligodendrocyte, T-cell, Brain,
    then query those terms.
4.  **Abbreviation handling**: Common abbreviations (lv → left ventricle, huvec
    → human umbilical vein endothelial) are built in.
5.  **Conservation of specificity**: A match is rejected if any substantive
    query token is missing from the target. Only generic stopwords ("human",
    "tissue", "sample") can be safely dropped.
6.  **Partial match flagging**: If a partial match or fallback is necessary, it
    must be explicitly flagged as `[PARTIAL MATCH]` in the output.

**Tissue selection for reports:**

-   **Match disease to organ system**: "Cardiomyopathy" → heart, atrium,
    ventricle, cardiomyocyte.
-   **Avoid generic proxies**: Do NOT use "Smooth Muscle Cell" for heart
    (cardiac ≠ smooth), "Fibroblast" for brain.
-   **Search strategy**: If specific query (e.g., "cardiomyocyte") yields 0
    hits, search for the organ ("heart", "cardiac").

--------------------------------------------------------------------------------

## Pre-Report Reasoning Checklist

Complete this BEFORE writing the report. Ground every interpretation in specific
visual observations from the plots.

> [!CAUTION] **Do not pursue only the "obvious" answer** (nearest gene,
> literature-known tissue). Focus on where the model shows the strongest signal.
> Ensure you have examined ALL significant scores, not just a convenient "top
> 5".

### 1. Cross-Tissue & Cross-Modality Patterns

-   [ ] **Analyze tissue specificity**: Determine if the effect is universal or
    tissue-restricted, and explain why.
-   [ ] **Check modality agreement**: Verify if different modalities agree
    within each tissue (concordant = strong evidence; discordant = complex
    regulation or potential model limitation).
-   [ ] **Identify largest effect**: Pinpoint which tissue shows the largest
    effect and assess its biological plausibility.

### 2. Hypothesis Validation

-   [ ] **Cite supporting plots**: Explicitly state which plots support or
    refute the proposed molecular mechanism.
-   [ ] **Cite supporting scores**: Explicitly state which variant scores
    support or refute the proposed molecular mechanism.

### 3. ISM SeqLogo

-   [ ] **Identify motif disruptions**: Detail the motif disruptions evident
    from REF vs ALT differences.
-   [ ] **Check consistency**: Determine if disruptions are consistent across
    tissues or tissue-specific.
-   [ ] **Explain magnitude differences**: Use ISM plots to explain magnitude
    differences between tissues.

### 4. Synthesis

-   [ ] **Define primary molecular mechanism**: Trace the chain of events: E.g.
    motif disruption → chromatin effect → transcriptional consequence →
    potential disease link.
-   [ ] **Avoid speculation**: If scores are low and plots are flat, report "No
    Significant Effect" instead of forcing a story.
-   [ ] **Address original query**: Ensure the report directly answers the
    user's initial question.

### 5. Report Readiness

-   [ ] **Write a narrative**: Focus on telling a biological story, not just
    dumping data.
-   [ ] **Verify references**: Ensure all plot files are present and correctly
    referenced.
-   [ ] **Embed all views**: Include ISM plots, Detail Views, and Whole-Gene
    Views where applicable.
-   [ ] **Confirm evidence**: Verify that allegations of splicing have the
    required splicing-related plots showing effects, expression changes have
    RNA-seq differences, and regulatory effects have DNASE/ChIP peak changes.

--------------------------------------------------------------------------------
