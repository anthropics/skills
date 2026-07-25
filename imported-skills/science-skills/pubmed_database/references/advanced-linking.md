# Advanced Biological Database Linking (ELink)

## 1. Core Concepts: Database vs. Linkname

A query requires both a `target_database` and a `linkname`:

*   Target Database: The destination repository (e.g., `gene`, `nuccore`,
    `pccompound`).
*   Linkname: The specific "semantic bridge" defined by NCBI. Linknames follow
    the naming convention: `dbfrom_db_subset`. One database pair can have
    multiple linknames representing different relationships.

### Common Database and Linkname Pairs

*   **pubmed**, `pubmed_pubmed_citedin`: **Forward Citations** — Find papers
    that cite the source paper.
*   **pubmed**, `pubmed_pubmed_refs`: **Backward Citations** — Extract the
    source paper's bibliography.
*   **pubmed**, `pubmed_pubmed`: **Similar Articles** — Papers sharing MeSH
    terms or keywords.
*   **pmc**, `pubmed_pmc`: **Full Text** — Resolve a PMID to a PMCID (required
    for BioC API).
*   **pccompound**, `pubmed_pccompound`: **Chemicals** — Find specific chemicals
    or drugs mentioned (CIDs).
*   **pcassay**, `pubmed_pcassay`: **PubChem BioAssays** — Link to experimental
    results and screening data.
*   **gene**, `pubmed_gene`: **Genetics** — Identify specific NCBI Gene records
    discussed.
*   **nuccore**, `pubmed_nuccore`: **Sequence Data** — Link to
    GenBank/nucleotide sequences.
*   **protein**, `pubmed_protein`: **Proteins** — Link to RefSeq or GenPept
    protein records.
*   **clinvar**, `pubmed_clinvar`: **Clinical Variants** — Find links to the
    ClinVar database (mutations).
*   **snp**, `pubmed_snp`: **SNPs** — Find specific Single Nucleotide
    Polymorphisms.
*   **sra**, `pubmed_sra`: **Raw Data** — Find raw datasets in the Sequence Read
    Archive.
*   **structure**, `pubmed_structure`: **3D Structures** — Find molecular
    structures (PDB) for proteins/ligands.

This list covers the most common `pubmed → X` links. For the full list of all
ELink linknames across all NCBI databases, see the
[NCBI Entrez Links catalog](https://eutils.ncbi.nlm.nih.gov/entrez/query/static/entrezlinks.html).

--------------------------------------------------------------------------------

## 2. Procedural Wisdom: Handling Failure Modes

### The "Indexing Lag" Problem (Recent Papers)

NCBI links are not created instantly. There is a human-in-the-loop and automated
indexing process that results in a **4-8 week delay** for cross-database links.

**Symptom**: `find_linked_biological_data` returns `[]` for a paper published 2
weeks ago.

**Strategy**: If the paper is very recent, **pivot immediately** to semantic
search or full-text extraction. Use `get_full_text_pmc` and search for primary
identifiers in the prose (e.g., by searching for specific identifiers or
nomenclature manually).

### The "High-Citation" Timeout

For foundational papers with >10,000 citations, `pubmed_pubmed_citedin` may fail
or timeout.

**Strategy**: Instead of linking, use `search_pubmed` with the title of the
paper in quotes or a specific query like `"citations for PMID [SOURCE_PMID]"`

### Verifying Open Access Availability

Before calling `get_full_text_pmc`, it is more reliable to check the link first

**Workflow**: Call `find_linked_biological_data` with `target_database="pmc"`
and `linkname="pubmed_pmc"`. If it returns a result, the paper is definitely in
the PMC BioC database. If not, don't waste time on a full-text fetch; use
`fetch_article_abstracts` instead.

--------------------------------------------------------------------------------

## 3. Category-Specific Tips

### Chemical Entities (`pccompound`, `pcassay`)

Links to chemical databases typically return **internal identifiers** (e.g.,
PubChem CIDs) rather than common names.

**Example**: A link to a drug study might return `["4091"]`.

**Note**: To resolve these to names, you must use a separate metadata lookup or
search strategy, as the linking tool only provides the relationship, not the
entity details.

### Sequence and Genomic Data (`nuccore`, `protein`, `gene`)

These links represent formal submissions to NCBI repositories (like GenBank).

**Strategy**: If a link search returns empty for recent research, search for the
paper's title or key findings in PubMed to find the abstract. Authors often
include primary identifiers in the text before the database cross-references are
finalized.

--------------------------------------------------------------------------------

## 4. Troubleshooting Empty Results

If `find_linked_biological_data` returns `[]`:

1.  **Check Date**: Is it a recent paper? (Indexing lag).
2.  **Check Scope**: Is the topic niche? (Authors may not have submitted data to
    NCBI).
3.  **Check Database Pair**: Ensure you are using the correct `linkname` for the
    `target_database`. Using `pubmed_gene` with `target_database="nuccore"` will
    fail.

--------------------------------------------------------------------------------

## 5. Advanced Features

*   **Reverse lookups**: `find_linked_biological_data` accepts a `dbfrom`
    parameter (default: `"pubmed"`). Set it to another database to traverse
    links in the opposite direction (e.g., `gene → pubmed`).
*   **Date filtering**: Pass `mindate` and `maxdate` (YYYY/MM/DD format) to
    filter linked results by publication date. Only works when `dbfrom` and
    `target_database` are both `"pubmed"`.
*   **Link discovery**: Use `discover_available_links` with a record ID to list
    all available linknames before calling `find_linked_biological_data`.
