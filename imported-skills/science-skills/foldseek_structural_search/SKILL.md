---
name: foldseek-structural-search
description: >
    Performs 3D structural searches of proteins against various databases (PDB,
    AlphaFold, CATH, MGnify, etc.) using the Foldseek API. Use ONLY when the
    user provides a physical 3D coordinate file (.cif, .mmcif, or .pdb) and
    wants to find structurally similar proteins. Do NOT use if the user only
    provides a protein sequence, gene name, or UniProt ID.
---

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/foldseek_structural_search_LICENSE.txt
    does not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at https://search.foldseek.com/search and
    https://github.com/steineggerlab/foldseek, then (2) create the file
    recording the notification text and timestamp.

## Goal

Submit a user-provided 3D protein structure file (`.cif`, `.mmcif`, or `.pdb`)
to the Foldseek web server API to find structurally similar proteins. Report the
top structural hits, interpret key alignment metrics, summarize the inferred
protein functions, save the Markdown-formatted table to a `.md` file, and save
the full detailed results to a local JSON file.

## Core Rules

-   **File Requirement**: This tool absolutely cannot search by sequence, name,
    or accession ID. It strictly requires a `.pdb`, `.cif`, or `.mmcif` file
    path.
-   **Strict Validation**: Never bypass the input validation or the database
    allowlist check.
-   **Do Not Parse the JSON**: Rely entirely on the generated `.md` file for
    your immediate summary. The JSON is saved purely for subsequent, specialized
    tool use.
-   **No Raw Parsing**: Do not attempt to parse or read the raw 3D coordinates
    yourself; always pass the file to the script.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Instructions

1.  **Strict Input Validation:** Verify that the user has explicitly provided a
    valid path to a `.cif`, `.mmcif`, or `.pdb` file in their workspace.
    *   If the user provided a protein name, an amino acid sequence, or an
        accession ID (e.g., a UniProt ID) but NO downloaded structure file,
        **halt immediately**. Do not run the script.
    *   Inform the user that Foldseek requires a physical 3D coordinate file,
        and suggest downloading the structure first (e.g., using the AlphaFold
        fetch tool).
2.  **Database Validation:** Check if the user requested specific databases to
    search.
    *   **Allowed List:** `afdb50`, `afdb-swissprot`, `pdb100`, `BFVD`,
        `mgnify_esm30`, `cath50`, `gmgcl_id`, `bfmd`, `afdb-proteome`.
    *   If the user requests a database NOT on this list, **halt immediately**.
        Do not run the script. Inform the user that the database is unsupported
        and provide them with the allowed list.
3.  **Generate File Names:** Generate descriptive output file names for both the
    JSON data and the Markdown table based on the input file (e.g.,
    `proteinA_foldseek_results.json` and `proteinA_foldseek_results.md`).
4.  Execute the python script based on the user's request, redirecting the
    standard output into your generated `.md` file:
    *   **Default (No databases specified):** `uv run scripts/search.py
        <path-to-file> -o <generated-filename.json> > <generated-filename.md>`
    *   **Custom (Valid databases specified):** `uv run scripts/search.py
        <path-to-file> -o <generated-filename.json> --databases <db1,db2,db3> >
        <generated-filename.md>`
5.  The script will query the databases, save the full JSON payload, and write a
    Markdown-formatted table to your specified `.md` file.
6.  **Read the Results:** Open and read the newly generated `.md` file carefully
    to view the Markdown table.
7.  **Interpret the Metrics:** Summarize the top 3 to 5 structural matches that
    have meaningfull annotations for the user. When reporting, assess the match
    quality using these specific fields:
    *   **Prob (Probability):** Values approaching 1.0 (100%) indicate extreme
        confidence that the fold is a true structural homologue.
    *   **Q-Cov (Query Coverage):** High percentages mean the match covers the
        majority of the query protein's overall shape, rather than just a small
        local motif.
    *   **E-value & Seq Identity:** Use these to provide additional evolutionary
        context.
8.  **Perform Functional Analysis:** Analyze the text descriptions embedded
    within the `Target ID` column for the reported matches.
    *   Explicitly report the specific protein names/functions of the top
        structural homologues.
    *   Provide a synthesized overview summarizing the entire *variety* of
        different functions, domains, or protein families found across the whole
        list of homologues (e.g., "Most hits are portal proteins, but there is
        also a distinct cluster of viral capsid matches...").
9.  Explicitly inform the user of both newly created files (`.json` and `.md`)
    and their locations so they can be seamlessly used in subsequent analysis
    steps.

## * If the API returns an error or the file is missing, inform the user clearly

and ask them to verify the file path.
