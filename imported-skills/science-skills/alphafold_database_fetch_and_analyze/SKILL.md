---
name: alphafold-database-fetch-and-analyze
description: >
  Retrieve and analyze AlphaFold predicted structures for a protein. Use when
  the user provides a specific UniProt Accession ID and wants structural
  confidence metrics (pLDDT), domain boundary analysis, or disorder
  assessment. Do not use if the user only has a protein name, gene name,
  or amino acid sequence — ask for a UniProt ID first.
---

# AlphaFold Database: Fetch and Analyze

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If
    .licenses/alphafold_database_fetch_and_analyze_LICENSE.txt does not already
    exist in the workspace root directory then (1) prominently notify the user
    to check the terms at https://alphafold.ebi.ac.uk/, then (2) create the file
    recording the notification text and timestamp.

## Overview

Downloads AlphaFold predicted structures (mmCIF) and Predicted Aligned Error
(PAE) matrices from the AlphaFold Database for a given UniProt ID, then performs
automated heuristic analysis on structural confidence (pLDDT), intrinsically
disordered regions, rigid domain boundaries, and inter-domain flexibility.

**Do NOT use when:**

-   The user only has a protein name, gene name, or amino acid sequence (no
    UniProt ID) — ask them to look up the ID on
    [UniProt](https://www.uniprot.org).
-   The user wants to search for structural homologs (use **Foldseek**).
-   The user wants to run AlphaFold predictions on a custom sequence.
-   The user needs experimental PDB structures (use **RCSB PDB**).

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce the required rate limit gracefully.
-   Do not attempt to calculate domain boundaries or assess structural disorder
    yourself; always rely on the output provided by the script.
-   If this skill is used, ensure this is mentioned in the output.

## Utility Scripts

**1. Fetch Structure Files**

Downloads the `.cif` structure file, `_predicted_aligned_error.json`, and API
metadata JSON (`-metadata.json`) for a UniProt ID. Handles fragment fallback for
very large proteins.

Examples:

```bash
uv run scripts/fetch_structure.py P00520 -o /path/to/output/
uv run scripts/fetch_structure.py P04637 -o /path/to/custom_results/
```

Always specify `-o` with an absolute path or a path relative to the user's
project root, never a path relative to the skill directory.

**2. Analyze pLDDT Confidence**

Reads pLDDT confidence metrics from a saved AFDB metadata JSON file (produced by
`fetch_structure.py`) and prints a heuristic confidence assessment (structured,
disordered, mixed).

Example:

```bash
uv run scripts/analyze_plddt.py ./data/AF-P00520-F1-metadata.json
```

**3. Analyze PAE / Domain Boundaries**

Reads a downloaded PAE JSON file and detects rigid domain boundaries using a
sliding-window PAE heuristic.

Example:

```bash
uv run scripts/analyze_pae.py ./data/AF-P00520-F1-predicted_aligned_error_v6.json
```

## Interpreting the Output

The script prints analysis to stdout. Read it carefully and synthesize the
results for the user:

1.  **Isoform / Large Protein Warning (MANDATORY):** Check the script output for
    any `[!] WARNING` lines. If the script reports that no canonical entry was
    found and an isoform was used, or if the protein is very large (>2700 AAs),
    you **MUST** prominently relay this warning to the user. Do not omit this
    warning.
2.  **Synthesize the Structural Analysis**: Combine the "pLDDT Conclusion" and
    the "PAE Structural Conclusion" into a single, cohesive overall summary.
    Describe the protein's overall folding confidence, the presence of
    disordered regions, and its rigid domain layout.
3.  Highlight the supporting metrics:
    -   Overall Global pLDDT and the breakdown of fraction confidence
        (especially Very Low vs. Very High).
    -   Domain Boundary Analysis (number of distinct global domains and their
        specific residue ranges).
4.  **Explicit Disorder Warning:** If the analysis concludes that the protein is
    highly intrinsically disordered (e.g., high fraction of <50 pLDDT or lack of
    rigid domains), issue a separate, prominent warning. Advise the user against
    proceeding with whole-protein downstream structural analysis (like Foldseek
    or docking). If small ordered domains exist amidst the disorder, advise the
    user to restrict any future analysis strictly to those specific residue
    boundaries.
5.  Remind the user that per-residue pLDDT is embedded in the B-factor column of
    the downloaded mmCIF file.
