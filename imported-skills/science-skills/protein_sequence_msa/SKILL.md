---
name: protein-sequence-msa
description: >
  Performs multiple sequence alignment of proteins with EBI Clustal Omega.
  Use when you need to align multiple sequences to assess similarity, domain
  conservation, or key residue conservation. Supports up to 4000 sequences and
  a maximum file size of 4 MB. Do not use to search for homologous proteins in
  a database (use MMseqs2, BLAST), align non-protein sequences (DNA, RNA),
  perform structural alignment (use Foldseek, PyMOL), or if you only have a
  single sequence.
---

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/protein_sequence_msa_LICENSE.txt does
    not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at
    https://www.ebi.ac.uk/jdispatcher/msa/clustalo and
    https://www.ebi.ac.uk/about/terms-of-use/, then (2) create the file
    recording the notification text and timestamp.
3.  **`.env` file**: Make sure the `.env` file exists in your home directory.
    Create one if it does not exist.
4.  **`USER_EMAIL`**: Required by the wrapper script for Clustal Omega job
    tracking (recommended by the EBI). You **MUST** use the safe credentials
    protocol in the `credentials` skill to check for and request this credential
    if this skill looks relevant to the user's request.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the alignment using
    `scripts/msa_align.py` rather than writing your own curl or custom Python
    requests. The script automatically enforces the required rate limit to
    respect EBI's Terms of Use.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.
*   **Always state the method:** Every report must clearly state that the
    alignment was performed using **EBI Clustal Omega**.
-   **No Hallucinations**: Do NOT invent alignments or conservation metrics.
    Report only what is present in the alignment file.

## Goal

Take a file containing multiple protein sequences in FASTA format, perform
multiple sequence alignment using the EBI Clustal Omega API, save the resulting
alignment locally for future programmatic analysis, and interpret the results
towards addressing the user's specific research objective (e.g., assessing
similarity, identifying conserved domains, or analyzing key residues).

## Instructions

1.  **Prepare Input File:** The input must be a plain text file containing two
    or more protein sequences in FASTA format. Each sequence header must start
    with a `>` symbol. Example:

    ```
    >Sequence_1_Name
    MQIFVKTLTGKTITLEVEPSDTIENVKAKIQDKEGIPPDQ
    QRLIFAGKQLEDGRTLSDYNIQKESTLHLVLRLRGG
    >Sequence_2_Name
    MQIFVKTLTGKTITLEVEPSDTIENVKAKIQDKEGIPPDQ
    QRLIFAGKQLEDGRTLSDYNIQKESTLHLVLRLRGG
    ```

2.  **Execute Alignment:** Run the alignment script:

    ```bash
    uv run scripts/msa_align.py <INPUT_FASTA> -o <OUTPUT_FILE>
    ```

    Always specify the output file with `-o` or `--output`.

3.  **Interpret and Report Results:** Analyze the Clustal Omega alignment by
    selecting metrics and mapping strategies aligned with the research
    objective. Note that while Clustal Omega produces a Global Alignment,
    pairwise metrics can be extracted to evaluate specific relationships within
    the set:

    *   **Identity Metric Options:** The choice of denominator determines how
        insertions/deletions (gaps) affect the final percentage. Select the most
        appropriate calculation based on the biological context:
        *   **Pairwise - Sequence Coverage:** `(Identical Residue Matches) /
            (Length of Shorter Sequence)`. Use when determining if a specific
            domain or fragment is fully preserved within a larger protein. This
            ignores gaps in the longer sequence, focusing purely on the
            "content" of the shorter one.
        *   **Pairwise - Global Identity:** `(Identical Residue Matches) /
            (Total Alignment Columns)`. Use when comparing full-length sequences
            of similar expected length. This is the most conservative metric; it
            penalizes for all gaps (indels) introduced by any sequence in the
            MSA.
        *   **Pairwise - Overlap Identity:** `(Identical Residue Matches) /
            (Total Alignment Columns - Terminal Gaps)`. Use when comparing a
            fragment to a full-length protein or when sequences have long
            unaligned "tails." This focuses on similarity only where the
            sequences physically overlap.
        *   **Multisequence - Conservation Index:** `(Fully Conserved Columns) /
            (Total Alignment Columns)`. Use for quantifying the percentage of
            residues that are 100% identical across the entire alignment set.
            This identifies the core evolutionary signature of the protein
            family.
    *   **Feature Mapping:** Leverage known biological data from specific
        sequences to ground the analysis:
        *   **Knowledge Gathering:** Identify relevant known sites or regions
            (e.g., catalytic residues, binding motifs) from your input or via
            external tools.
        *   **Coordinate Projection:** Map these features onto the corresponding
            Column Indices of the alignment.
        *   **Targeted Discussion:** Use these columns to drive the assessment:
            *   **Local Conservation:** Analyze if the known functional residues
                are invariant across the set.
            *   **Region-Specific Metrics:** Calculate identity/similarity
                specifically within the mapped functional regions rather than
                the whole sequence.
            *   **Goal Contribution:** Discuss how this data contributes to your
                goal, e.g. using conservation to corroborate a prediction or
                divergence to reject a functional hypothesis.

## References

-   Multiple Sequence Alignment: https://www.ebi.ac.uk/jdispatcher/msa/clustalo
