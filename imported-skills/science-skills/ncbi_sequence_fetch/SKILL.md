---
name: ncbi-sequence-fetch
description: >
  Retrieve protein and nucleotide sequences from NCBI databases using
  E-utilities. Supports direct accession lookup, CDS translation, gene+organism
  search, locus lookup, PubMed-linked sequences, patent protein extraction, and
  organism+length fallback search. Use when you need to fetch biological
  sequences by accession, gene name, locus tag, PubMed ID, or patent number.
---

# NCBI Sequence Fetch

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/ncbi_sequence_fetch_LICENSE.txt does not
    already exist in the workspace root directory then (1) prominently notify
    the user to check the terms at https://www.ncbi.nlm.nih.gov/ and
    https://www.ncbi.nlm.nih.gov/home/about/policies/, then (2) create the file
    recording the notification text and timestamp.
3.  **`.env` file**: Make sure the `.env` file exists in your home directory.
    Create one if it does not exist.
4.  **`NCBI_API_KEY`** (optional): Raises the NCBI rate limit from 3 to 10
    requests/second. The skill works without it, but a key is recommended if the
    user plans many queries or encounters a 429 error. You can register for a
    key for free at https://www.ncbi.nlm.nih.gov/account/settings/. You **MUST**
    use the safe credentials protocol in the `credentials` skill to check for
    and request this key if this skill looks relevant to the user's request.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce the required rate limit gracefully.
-   **API Key Support**: If the user provides an `NCBI_API_KEY` in their
    environment, the query speed limits are automatically increased
    significantly.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Overview

Wraps NCBI's Entrez E-utilities (efetch, esearch, elink, esummary) for
retrieving protein and nucleotide sequences. Provides 10 subcommands covering
the full range of sequence retrieval workflows:

-   `fetch-protein` — Direct protein accession lookup (GenPept, RefSeq)
-   `fetch-nucleotide` — Direct nucleotide accession lookup
-   `cds-translate` — Fetch CDS and translate to protein (3 methods)
-   `search` — Free-text search of any NCBI database
-   `elink` — Follow cross-database links (PubMed→Protein, etc.)
-   `gene-protein` — Search protein by gene name + organism
-   `locus-protein` — Search protein by locus tag + organism
-   `pubmed-proteins` — Find proteins linked to a PubMed article
-   `patent-search` — Extract protein sequences from patents
-   `organism-length` — Last-resort search by organism + exact AA length

## Utility Scripts

**`scripts/ncbi_fetch.py`** — Single script with subcommands.

All subcommands write structured JSON output. Use `--output FILE` to save to a
file, or omit it to print to stdout. A human-readable summary is always printed
to stdout.

### 1. Fetch Protein by Accession

Fetches protein FASTA from NCBI by accession (XP_, NP_, GenPept, etc.)

```bash
uv run scripts/ncbi_fetch.py fetch-protein XP_022033624 -o /tmp/result.json
uv run scripts/ncbi_fetch.py fetch-protein NP_001234567 ABC12345.1
```

### 2. Fetch Nucleotide by Accession

Fetches nucleotide FASTA from NCBI by accession.

```bash
uv run scripts/ncbi_fetch.py fetch-nucleotide MK034466 -o /tmp/result.json
```

### 3. CDS Translate

Fetches a CDS/nucleotide accession and translates to protein sequence. Tries
three approaches in order: 1. NCBI's pre-translated CDS protein (`fasta_cds_aa`)

2. GenBank XML CDS annotation translations 3. Raw nucleotide → 6-frame ORF
finding

```bash
uv run scripts/ncbi_fetch.py cds-translate MK034466 -o /tmp/result.json
uv run scripts/ncbi_fetch.py cds-translate HQ662330 --target-length 1043
```

If the accession is a **genomic record** (not mRNA/CDS), the tool will report
`is_genomic: true` so you can fall back to a homology-based approach instead.

### 4. Search Any Database

Free-text search using Entrez query syntax. Supports all NCBI databases.

```bash
# Search protein database
uv run scripts/ncbi_fetch.py search "WRR4B[Gene Name] AND Arabidopsis[Organism]" \
  --database protein --retmax 5 --fetch-sequences

# Search nucleotide database
uv run scripts/ncbi_fetch.py search "Rz2[Gene Name] AND Beta vulgaris[Organism]" \
  --database nuccore --retmax 10

# Search with patent filter
uv run scripts/ncbi_fetch.py search "disease resistance AND Solanum[Organism] AND patent[Properties]" \
  --database protein --fetch-sequences

# Search by sequence length
uv run scripts/ncbi_fetch.py search '"Oryza sativa"[Organism] AND 1043[SLEN]' \
  --database protein --fetch-sequences --retmax 50
```

### 5. Cross-Database Links (elink)

Follow NCBI's cross-database links (e.g., PubMed article → linked proteins).

```bash
uv run scripts/ncbi_fetch.py elink 24896089 --dbfrom pubmed --db protein \
  --fetch-sequences -o /tmp/linked.json
```

### 6. Gene + Organism Search

Searches for protein sequences by gene name and organism. Searches NCBI Protein
with `[Gene Name]` and `[Organism]` qualifiers.

```bash
uv run scripts/ncbi_fetch.py gene-protein WRR4B --organism "Arabidopsis thaliana"
uv run scripts/ncbi_fetch.py gene-protein Pikh-2 --organism "Oryza sativa" \
  --target-length 1043 -o /tmp/result.json
```

### 7. Locus Tag Search

Searches by locus tag in both NCBI Protein and Nuccore databases. Extracts CDS
translations from GenBank XML when direct protein hits aren't available.

```bash
uv run scripts/ncbi_fetch.py locus-protein At1g56540 --organism "Arabidopsis thaliana"
uv run scripts/ncbi_fetch.py locus-protein Niben101Scf02422g02015.1 \
  --organism "Nicotiana benthamiana" -o /tmp/result.json
```

### 8. PubMed-Linked Proteins

Finds protein sequences linked to a PubMed article. Searches NCBI Protein by
PMID, follows elink PubMed→Protein, and extracts CDS translations from linked
Nuccore records.

```bash
uv run scripts/ncbi_fetch.py pubmed-proteins 30692254 --identifier WRR4B
uv run scripts/ncbi_fetch.py pubmed-proteins 24896089 --identifier "K2" \
  -o /tmp/result.json
```

### 9. Patent Sequence Search

Two modes:

**By patent number** — fetches all protein sequences from a specific patent:
`bash uv run scripts/ncbi_fetch.py patent-search --patent-number US10123456 -o
/tmp/patent.json`

**By keywords** — searches NCBI Protein with `patent[Properties]` filter: `bash
uv run scripts/ncbi_fetch.py patent-search --keywords WRR4B Albugo --organism
"Arabidopsis thaliana" -o /tmp/patent.json`

> [!IMPORTANT] **Patent convention**: In molecular biology patents, SEQ ID NO: 1
> is typically the DNA sequence and SEQ ID NO: 2 is the primary protein. Higher
> SEQ ID NOs are variants or related sequences. Prefer Sequence 2 when selecting
> the primary protein of interest.

### 10. Organism + Length Search

Last-resort search when only organism and expected protein length are known.
Uses NCBI's `[SLEN]` filter for exact length matching.

```bash
uv run scripts/ncbi_fetch.py organism-length \
  --organism "Arabidopsis thaliana" --length 1048 --retmax 50 \
  -o /tmp/result.json
```

> [!NOTE] This often returns multiple candidates. Use the JSON output headers to
> identify the correct protein.

## Workflow

### Standard Sequence Retrieval Cascade

When trying to find a protein sequence, follow this priority order:

1.  **Direct accession** — `fetch-protein` with GenPept/RefSeq accession
2.  **CDS translation** — `cds-translate` with nucleotide/CDS accession
3.  **PubMed-linked** — `pubmed-proteins` with PMID + gene name
4.  **Locus lookup** — `locus-protein` with locus tag + organism
5.  **Gene + organism** — `gene-protein` with gene name + organism
6.  **Patent search** — `patent-search` with patent number or keywords
7.  **Organism + length** — `organism-length` as last resort

### Interpreting Results

-   All subcommands return JSON with a `results` array
-   Each result has `sequence` (AA string), `length`, and `header`/metadata
-   When multiple results are returned, select by:
    -   Closest match to expected length (`target_length`)
    -   Header relevance (matching gene name, "disease resistance" keywords)
    -   Source priority (RefSeq > GenPept > patent)

## Reference

-   **NCBI E-utilities docs**: https://www.ncbi.nlm.nih.gov/books/NBK25499/
-   **Entrez search syntax**: https://www.ncbi.nlm.nih.gov/books/NBK49540/
-   **Database list**: protein, nuccore, gene, pubmed, pmc, biosample, etc.
-   **Common accession formats**:
    -   `XP_` / `NP_` — NCBI RefSeq protein
    -   `AAA` to `AZZ` + digits — GenPept (translated GenBank)
    -   `MK`, `MN`, `HQ`, etc. + digits — GenBank nucleotide
    -   `ENSG`, `ENST`, `ENSP` — Ensembl (use `ensembl-database` skill instead)
    -   `Q`, `P`, `O` + digits — UniProt (use `uniprot-database` skill instead)
