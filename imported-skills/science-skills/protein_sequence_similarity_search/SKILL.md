---
name: protein-sequence-similarity-search
description: >
    Searches for homologous protein sequences using MMseqs2 (fast, default) or
    BLAST (comprehensive, fallback). Trigger this whenever the user provides a
    protein sequence or FASTA file and asks to find homologues, sequence
    matches, or wants to infer protein function based on sequence similarity,
    but not when the user wants to infer protein function based on structural
    similarity.
---

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If
    .licenses/protein_sequence_similarity_search_LICENSE.txt does not already
    exist in the workspace root directory then (1) prominently notify the user
    to check the terms at https://www.ebi.ac.uk/jdispatcher/sss/ncbiblast and
    https://colabfold.com, then (2) create the file recording the notification
    text and timestamp.
3.  **`.env` file**: Make sure the `.env` file exists in your home directory.
    Create one if it does not exist.
4.  **`USER_EMAIL`** (optional but recommended): Recommended by the EBI for
    BLAST job tracking, but the skill works without it. You **MUST** use the
    safe credentials protocol in the `credentials` skill to check for and
    request this credential if this skill looks relevant to the user's request.

## Goal

Take a user-provided amino acid sequence (or a path to a `.fasta` file), search
for sequence homologues using the fastest available method, generate a
Markdown-formatted table of the top hits, interpret key alignment metrics,
summarize the inferred protein functions, and save results locally for future
programmatic analysis.

## Core Rules

-   **Strict Validation**: For BLAST, only use database codes listed in the
    table below.
-   **No Hallucinations**: If a script throws an error or returns no hits,
    inform the user clearly. Do NOT invent sequence homologues.
-   **Do Not Parse Output Files**: Do not parse the JSON, a3m, or any other raw
    output files. Rely on the generated `.md` file for your summary. The JSON
    and other outputs are for subsequent tool use only.
-   **Always State the Method**: Every report must clearly state whether the
    search used the quick MMseqs2 (ColabFold API) or the slower EBI BLAST
    method.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output. Explicitly state that the corresponding program (MMSEQS2 or EBI
    BLAST) and Sequence Databases were used.

## Search Method Selection

Choose the search method based on the user's request:

If the **user says "quick search" or "fast search"**, **no specific method
requested / general homologue search**, of if you are unsure: Run MMseqs2 (fast,
default) using `mmseqs2_search.py`

If **MMseqs2 fails (exit code 2: RATELIMIT or API error)** or **User explicitly
requests "BLAST"** or **a specific BLAST database** (e.g. `uniprotkb_swissprot`,
`pdb`, `uniprotkb_human`): Run BLAST using `uniprot_blast.py`

## Instructions

1.  Identify the query from the user. It can be a raw sequence string (e.g.,
    "MKVLY...") or a path to a local file (e.g., "./data/sequence.fasta").

2.  **Determine the search method** using the list above.

### Path A: MMseqs2 Search (Default)

1.  **Generate File Names:** Generate descriptive output file names based on the
    input (e.g., `proteinA_mmseqs2.json` and `proteinA_mmseqs2.md`).
2.  Execute the MMseqs2 script:

    *   **Default:**

    ```
    uv run scripts/mmseqs2_search.py <SEQUENCE_OR_FILE> -o <generated-filename.md> -j <generated-filename.json>
    ```

    *   **With mgnify:**

    ```
    uv run scripts/mmseqs2_search.py <SEQUENCE_OR_FILE> -o <generated-filename.md> -j <generated-filename.json> --include-mgnify
    ```

3.  The script will query the ColabFold MMseqs2 API and poll for completion.
    This is typically fast (under 2 minutes).

4.  **If the script exits with code 2** (API failure, rate limit), automatically
    fall back to BLAST (Path B below). Inform the user: "MMseqs2 search failed,
    falling back to BLAST."

5.  **Read the Results:** Open and read the generated `.md` file.

### Path B: BLAST Search (Explicit or Fallback)

1.  **Database Selection & Validation:** Determine the most appropriate
    database(s) based on the user's prompt.
    *   Consult the **Available BLAST Databases** table below.
    *   If the user specifies a taxonomic group (e.g., "Find homologues in
        microbes"), select the corresponding `Database Code` (e.g.,
        `uniprotkb_bacteria`).
    *   If the user explicitly requests curated hits, use `uniprotkb_swissprot`.
    *   If no specific database is requested, do not specify `--databases`.
    *   **Validation:** Ensure the database code exactly matches an entry in the
        table. If the user requests a database not on the list, **do not
        proceed** and provide the allowed list.
2.  **Generate File Names:** (e.g., `proteinA_ebi_blast.json` and
    `proteinA_ebi_blast.md`).
3.  This API requires the user email address to be set in the USER_EMAIL
    environment variable for inclusion in request header. You **MUST** use the
    safe credentials protocol in the `credentials` skill to check for and
    request this credential if this skill looks relevant to the user's request.
4.  Execute the BLAST script:

    *   **Default (uniprotkb):**

    ```
    uv run scripts/uniprot_blast.py <SEQUENCE_OR_FILE> -o <generated-filename.md> -j <generated-filename.json>
    ```

    *   **Custom database:**

    ```
    uv run scripts/uniprot_blast.py <SEQUENCE_OR_FILE> -o <generated-filename.md> -j <generated-filename.json> --databases <db1,db2>
    ```

5.  The script will query the EBI BLAST API and poll the server. **Note:** This
    can take up to 15 minutes; wait patiently.

6.  **Read the Results:** Open and read the generated `.md` file.

### Common Steps (Both Methods)

1.  **Interpret the Metrics:** Summarize the top 3 to 5 sequence homologues.
    Assess match quality using:
    *   **Q-Cov (Query Coverage):** High percentages mean the match covers most
        of the query sequence.
    *   **E-value:** Lower E-values (e.g., `1e-50`) indicate extreme statistical
        significance.
    *   **Seq Identity:** Provides evolutionary context (highly conserved vs.
        distant homologue).
2.  **Perform Functional Analysis:**
    *   If the results table includes protein descriptions, analyze them
        directly: report specific protein names/functions of the top homologues
        and summarize the variety of functions, domains, or protein families
        found.
    *   If the results contain only UniProt accession IDs without descriptions
        (common with MMseqs2), look up the protein names and functions for the
        top 3–5 hits using the **uniprot-database** skill or other appropriate
        methods before summarizing.
3.  Inform the user of both newly created files (`.json` and `.md`) and their
    locations.

## Available BLAST Databases

*   `uniprotkb` – UniProt Knowledgebase (The UniProt Knowledgebase includes
    UniProtKB/Swiss-Prot and UniProtKB/TrEMBL): The UniProt Knowledgebase
    (UniProtKB) is the central access point for extensive curated protein
    information, including function, classification, and cross-references.
    Search UniProtKB to retrieve "everything that is known" about a particular
    sequence
*   `uniprotkb_swissprot` – UniProtKB/Swiss-Prot (The manually annotated section
    of UniProtKB): The manually curated subsection of the UniProt Knowledgebase
*   `uniprotkb_swissprotsv` – UniProtKB/Swiss-Prot isoforms (The manually
    annotated isoforms of UniProtKB/Swiss-Prot): The isoform sequences for the
    manually curated subsection of the UniProt Knowledgebase
*   `uniprotkb_reference_proteomes` – UniProtKB Reference Proteomes: Taxonomic
    subset of the UniProtKB Reference Proteomes
*   `uniprotkb_trembl` – UniProtKB/TrEMBL (The automatically annotated section
    of UniProtKB): Subsection of the UniProt Knowledgebase derived from ENA
    Sequence (formerly EMBL-Bank) coding sequence translations with annotation
    produced by an automated process
*   `uniprotkb_refprotswissprot` – UniProtKB Reference Proteomes plus
    Swiss-Prot: UniProtKB Reference Proteomes plus Swiss-Prot
*   `uniprotkb_archaea` – UniProtKB Archaea: Taxonomic subset of the UniProt
    Knowledgebase for archaea
*   `uniprotkb_arthropoda` – UniProtKB Arthropoda: Taxonomic subset of the
    UniProt Knowledgebase for arthropoda
*   `uniprotkb_bacteria` – UniProtKB Bacteria: Taxonomic subset of the UniProt
    Knowledgebase for bacteria
*   `uniprotkb_complete_microbial_proteomes` – UniProtKB Complete Microbial
    Proteomes: Taxonomic subset of the UniProt Knowledgebase for complete
    microbial proteomes
*   `uniprotkb_eukaryota` – UniProtKB Eukaryota: Taxonomic subset of the UniProt
    Knowledgebase for eukaryota
*   `uniprotkb_fungi` – UniProtKB Fungi: Taxonomic subset of the UniProt
    Knowledgebase for fungi
*   `uniprotkb_human` – UniProtKB Human: Taxonomic subset of the UniProt
    Knowledgebase for human
*   `uniprotkb_mammals` – UniProtKB Mammals: Taxonomic subset of the UniProt
    Knowledgebase for mammals
*   `uniprotkb_nematoda` – UniProtKB Nematoda: Taxonomic subset of the UniProt
    Knowledgebase for nematoda
*   `uniprotkb_rodents` – UniProtKB Rodents: Taxonomic subset of the UniProt
    Knowledgebase for rodents
*   `uniprotkb_vertebrates` – UniProtKB Vertebrates: Taxonomic subset of the
    UniProt Knowledgebase for vertebrates
*   `uniprotkb_viridiplantae` – UniProtKB Viridiplantae: Taxonomic subset of the
    UniProt Knowledgebase for viridiplantae
*   `uniprotkb_viruses` – UniProtKB Viruses: Taxonomic subset of the UniProt
    Knowledgebase for viruses
*   `uniprotkb_enzyme` – UniProtKB Enzyme: Taxonomic subset of the UniProt
    Knowledgebase for enzymes
*   `uniprotkb_covid19` – UniProtKB COVID-19: Taxonomic subset of the UniProt
    Knowledgebase for COVID-19
*   `uniref100` – UniProt Clusters 100% (UniRef100): The UniProt Reference
    Clusters (UniRef) containing sequences which are 100% identical.
*   `uniref90` – UniProt Clusters 90% (UniRef90): The UniProt Reference Clusters
    (UniRef) containing sequences which are 90% identical.
*   `uniref50` – UniProt Clusters 50% (UniRef50): The UniProt Reference Clusters
    (UniRef) containing sequences which are 50% identical.
*   `pdb` – Protein Structure Sequences (PDBe protein structure sequences):
    Protein sequences from structures described in the Brookhaven Protein Data
    Bank (PDB)
