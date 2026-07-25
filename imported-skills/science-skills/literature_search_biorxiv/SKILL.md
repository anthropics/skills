---
name: literature-search-biorxiv
description: >
  Browse, filter, and download life sciences, biology, and medical preprints
  from bioRxiv and medRxiv. Supports fetching paper metadata by DOI,
  and browsing by date range with category and keyword filters. Keyword
  filtering is local, so date ranges MUST be narrow (1-4 weeks) with a
  category to prevent timeouts.
---

# bioRxiv and medRxiv Literature Search

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/literature_search_biorxiv_LICENSE.txt
    does not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at https://api.biorxiv.org/ and
    https://www.biorxiv.org/content/about-biorxiv and to always check the
    license of the papers retrieved by the skill for any restrictions, then (2)
    create the file recording the notification text and timestamp.

## Search Strategy Guide (Read First)

**This skill browses a date-based preprint archive. It is NOT a keyword search
engine.** Choose your approach based on what you already know:

-   **A DOI** (e.g., from a citation): Use `search_by_doi.py`. Fast and
    reliable.
-   **Approximate date + category**: Use `search_by_dates.py` with a 1–4 week
    range and `--category`.
-   **Only a topic or keywords, no date**: **Do NOT use this skill for
    discovery.** Use a keyword-capable literature skill first to find relevant
    DOIs, then return here to fetch metadata.

> **CRITICAL ANTI-PATTERN — Do NOT do this:** Do NOT attempt to search broad
> date ranges (months or years) with `--keywords` hoping to find a specific
> paper. The bioRxiv API does not support server-side keyword search. The script
> must download ALL metadata for the entire date range and filter locally in
> Python. Broad ranges will result in thousands of API calls, timeouts, and your
> request being blocked for API abuse. This is the #1 reason this skill fails.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce the required rate limit gracefully.
-   **Local Filtering (CRITICAL WARNING)**: Unlike arXiv, the bioRxiv API **does
    not support server-side keyword or author searches**. Keyword and author
    filtering is performed *locally* by the scripts after downloading all
    metadata for a specified date range. You **MUST** use narrow date ranges
    (e.g., 1-4 weeks) AND the `--category` filter when searching with
    `--keywords` or `--author`.
-   **Abstracts Excluded By Default**: To save context space in the resulting
    JSON, abstracts are stripped from the output by default. If you are
    searching by `--keywords` and want to read the abstracts of the resulting
    papers to understand their context, you **MUST** pass the
    `--include_abstracts` flag.
-   **Output Redirection**: Search commands output JSON arrays to standard
    output. Always redirect output to a file (e.g., `> results.json`) and parse
    the file separately.
-   **List Sources** If this skill is used, ensure this is mentioned in the
    output AND list the URLs of all papers that were used in producing the
    output.

## Utility Scripts

All tools enforce a cross-process rate limits and retry with backoff on failure.
To ensure you respect terms-of-service, do NOT write custom `curl` queries.

**Pagination:** The bioRxiv API returns results in pages of up to 100 papers.
The `search_by_dates.py` script automatically fetches all pages and reports
pagination progress to stderr (e.g., `[Page 2] Fetched 200/543 papers...`). The
JSON output to stdout contains the **complete** filtered result set across all
pages — no manual pagination is needed.

### 1. Search by Dates (`search_by_dates.py`)

Search for preprints within an explicit date range, optionally filtering by
category, keywords, or author.

```bash
# Broad category search over a 2-week period
uv run scripts/search_by_dates.py --server biorxiv \
  --start_date 2024-01-01 --end_date 2024-01-14 \
  --category neuroscience > results.json

# Deep keyword filtering using OR logic and including abstracts
uv run scripts/search_by_dates.py --server medrxiv \
  --start_date 2023-11-01 --end_date 2023-11-30 \
  --category infectious_diseases \
  --keywords "covid" "sars-cov-2" --match_logic OR \
  --include_abstracts > covid_papers.json

# Finding papers by a specific author in a narrow window
uv run scripts/search_by_dates.py \
  --start_date 2024-05-01 --end_date 2024-05-14 \
  --author "Smith" > smith_papers.json
```

*Required Arguments:*

-   `--start_date`: YYYY-MM-DD
-   `--end_date`: YYYY-MM-DD

*Optional Arguments:*

-   `--server`: `biorxiv` (default) or `medrxiv`
-   `--category`: A valid subject category (see below). **Highly recommended** —
    dramatically reduces the data the script must download and filter.
-   `--keywords`: List of strings to search in the title/abstract.
-   `--match_logic`: `AND` (default) or `OR` for keywords.
-   `--author`: Author name (case-insensitive string match).
-   `--include_abstracts`: Flag to include full abstracts in the JSON output.

### 2. Fetch Metadata by DOI (`search_by_doi.py`)

Retrieve the detailed JSON metadata for a single paper if you already know its
DOI. **This is the most reliable entry point.**

```bash
uv run scripts/search_by_doi.py --server biorxiv \
  --doi "10.1101/2023.08.15.551388" \
  --include_abstracts > paper_info.json
```

### Downloading Full-Text PDFs

> **This skill does NOT support PDF downloads.** To download the full-text PDF
> of a bioRxiv or medRxiv preprint, use the **`literature-search-europepmc`**
> skill. First, use the paper's DOI to look up its PMCID via EuropePMC, then use
> EuropePMC's PDF retrieval to download the document.

## Valid Subject Categories

You can pass these to the `--category` flag in `search_by_dates.py`. The script
will strictly validate them.

### bioRxiv Categories:

`animal_behavior_and_cognition`, `biochemistry`, `bioengineering`,
`bioinformatics`, `biophysics`, `cancer_biology`, `cell_biology`,
`clinical_trials`, `developmental_biology`, `ecology`, `epidemiology`,
`evolutionary_biology`, `genetics`, `genomics`, `immunology`, `microbiology`,
`molecular_biology`, `neuroscience`, `paleontology`, `pathology`,
`pharmacology_and_toxicology`, `physiology`, `plant_biology`,
`scientific_communication_and_education`, `synthetic_biology`,
`systems_biology`, `zoology`

### medRxiv Categories:

`addiction_medicine`, `allergy_and_immunology`, `anesthesia`,
`cardiovascular_medicine`, `dentistry_and_oral_medicine`, `dermatology`,
`emergency_medicine`, `endocrinology`, `epidemiology`, `forensic_medicine`,
`gastroenterology`, `genetic_and_genomic_medicine`, `health_informatics`,
`health_economics_and_outcomes_research`, `health_policy`,
`health_systems_and_quality_improvement`, `hematology`, `hiv_aids`,
`infectious_diseases`, `intensive_care_and_critical_care_medicine`,
`medical_education`, `medical_ethics`, `nephrology`, `neurology`, `nursing`,
`nutrition`, `obstetrics_and_gynecology`,
`occupational_and_environmental_health`, `oncology`, `ophthalmology`,
`orthopedics`, `otolaryngology`, `pain_medicine`, `palliative_care`,
`pathology`, `pediatrics`, `pharmacology_and_therapeutics`,
`primary_care_research`, `psychiatry_and_clinical_psychology`,
`public_and_global_health`, `radiology_and_imaging`,
`rehabilitation_medicine_and_physical_therapy`, `respiratory_medicine`,
`rheumatology`, `sexual_and_reproductive_health`, `sports_medicine`, `surgery`,
`toxicology`, `transplantation`, `urology`
