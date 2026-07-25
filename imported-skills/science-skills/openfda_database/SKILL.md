---
name: openfda-database
description: >
  Query, search, and download data from the openFDA API for drugs, devices,
  foods, tobacco, cosmetics, animal and veterinary products, substances, and
  transparency data. Use for FDA adverse events, recalls, labeling, approvals,
  shortages, 510(k) clearances, NDC lookups, and any FDA safety or regulatory
  data query across all 28 API endpoints.
---

# openFDA Search and Query

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/openfda_database_LICENSE.txt does not
    already exist in the workspace root directory then (1) prominently notify
    the user to check the terms at https://open.fda.gov/apis/ and
    https://open.fda.gov/license, then (2) create the file recording the
    notification text and timestamp.
3.  **`.env` file**: Make sure the `.env` file exists in your home directory.
    Create one if it does not exist.
4.  **`FDA_API_KEY`** (optional but recommended): Raises the daily request limit
    from 1,000 to 120,000. The skill works without it, but an agent can easily
    exhaust the keyless limit in a single session. You can register for a free
    key at https://open.fda.gov/apis/authentication/. You **MUST** use the safe
    credentials protocol in the `credentials` skill to check for and request
    this key if this skill looks relevant to the user's request.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce the required rate limit gracefully.

-   **Rate Limiting**: Respect openFDA rate limits. Without API key: 240
    requests/min, 1,000 requests/day per IP. With API key: 240 requests/min,
    120,000 requests/day per key. Always set an API key before running
    multi-query workflows.

> **Warning**: An automated agent can easily exhaust the 1,000-request daily
> limit in a single research session. Always set an API key before running
> multi-query workflows.

> You **MUST** use the safe credentials protocol in the `credentials` skill to
> help the user add `FDA_API_KEY` to their `.env` file if this skill looks
> relevant to the user's request. The script will emit a warning to stderr if no
> API key is detected.

-   **Always Use `--output`**: All subcommands require `--output <file>` to
    write results to a file. This prevents large output becoming overwhelming.
    Use jq or code to read the output file.

-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Utility Script

**Single script for all operations:**

```bash
uv run scripts/openfda_query.py {search,count,download} --output <file> [options]
```

### 1. Search

Search any of the 28 endpoints and save JSON results to a file.

```bash
uv run scripts/openfda_query.py search \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:aspirin" \
  --limit 5 --output /tmp/fda_results.json
```

Stdout prints a compact summary:

```json
{"status": "success", "output": "/tmp/fda_results.json", "results_in_file": 5, "total_matching": 601477}
```

*Options:*

-   `--output`: Output file for full JSON results (required).
-   `--category`: API category — `drug`, `device`, `food`, `tobacco`, `other`,
    `animalandveterinary`, `cosmetic`, `transparency`.
-   `--endpoint`: Endpoint within the category (e.g., `event`, `label`, `510k`).
    See [references/api_endpoints.md](references/api_endpoints.md) for full
    list.
-   `--search`: Query string (e.g.,
    `patient.drug.medicinalproduct:aspirin+AND+serious:1`).
-   `--sort`: Sort field and order (e.g., `receivedate:desc`).
-   `--limit`: Max results (default 10, max 1000).
-   `--skip`: Pagination offset (default 0).
-   `--api_key`: API key (also reads `FDA_API_KEY` env var).

### 2. Count

Count unique values of a field within matching results.

```bash
uv run scripts/openfda_query.py count \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:aspirin" \
  --count_field "patient.reaction.reactionmeddrapt.exact" \
  --summary 10 --output /tmp/aspirin_reactions.json
```

Stdout prints a summary with the top 5 terms. Full data is in the output file.

*Additional options:*

-   `--count_field`: Field to count (append `.exact` for whole-phrase counting).
-   `--summary N`: Return only the top N most frequent terms. Use this to avoid
    flooding the context with hundreds of infrequent terms.

### 3. Download

Download multiple pages of results to a file.

```bash
uv run scripts/openfda_query.py download \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:aspirin" \
  --limit 100 --max_pages 5 \
  --output /tmp/aspirin_events.json
```

*Additional options:*

-   `--max_pages`: Maximum pages to fetch (default 10).
-   `--all_results`: Automatically paginate to fetch all matching results.
    Safety cap of 25,000 records maximum per download to prevent runaway
    downloads and prevent excessive API usage.

    > **Tip**: Common drugs can have excessive reports. Use a date range (e.g.,
    > `receivedate:[20250101+TO+20250131]`) to limit the volume of download.

## Entity Resolution: Using .exact for Precision

When searching for specific product names, drug names, or categorical terms,
always use the `.exact` suffix on the field to get exact-match results. Without
it, the API tokenizes multi-word values and returns noisy partial matches.

```bash
# Precise: matches only "ADVIL"
uv run scripts/openfda_query.py search --category drug --endpoint label \
  --search 'openfda.brand_name.exact:"ADVIL"' \
  --limit 5 --output /tmp/advil_label.json
```

> **Note**: Many brand names in the FDA database include variant suffixes (e.g.,
> "TYLENOL Extra Strength" rather than just "TYLENOL"). If an `.exact` search
> returns 0 results, try without `.exact` to see the available brand name
> variants, then re-query with the full exact name.

The `.exact` suffix is also required when using `--count_field` to aggregate
whole phrases instead of individual words.

## MedDRA Term Resolution

openFDA adverse event data uses MedDRA (Medical Dictionary for Regulatory
Activities) terms for reactions. The API reports **Preferred Terms (PTs)** but
does not provide the MedDRA hierarchy (System Organ Class, High Level Terms,
etc.).

> **Note**: MedDRA is a proprietary ontology and is **not indexed** in the
> EMBL-EBI OLS. To approximate MedDRA hierarchy lookups, use the **Human
> Phenotype Ontology (HP)** or **NCI Thesaurus (NCIT)** as proxy ontologies —
> they cross-reference MedDRA IDs and provide parent/ancestor relationships.

```bash
# Step 1: Get top reactions from openFDA
uv run scripts/openfda_query.py count \
  --category drug --endpoint event \
  --search "patient.drug.medicinalproduct:metformin" \
  --count_field "patient.reaction.reactionmeddrapt.exact" \
  --summary 5 --output /tmp/metformin_reactions.json

# Step 2: Look up the top reaction term using a biomedical ontology service
# skill (e.g. embl-ebi-ols skill).
# MedDRA is not available in OLS; use the Human Phenotype Ontology (HP) or
# NCI Thesaurus (NCIT) as a proxy to find the hierarchical classification of
# the reaction term.
```

## Available Endpoints (28 total)

Category to endpoint mapping:

-   `drug`: event, label, ndc, enforcement, drugsfda, shortages
-   `device`: 510k, classification, enforcement, event, pma, recall,
    registrationlisting, udi, covid19serology
-   `food`: enforcement, event
-   `tobacco`: problem, researchpreventionads, researchdigitalads,
    researchsmokefree
-   `other`: historicaldocument, nsde, substance, unii
-   `animalandveterinary`: event
-   `cosmetic`: event
-   `transparency`: crl

## Reference

-   **Query syntax and all endpoints**: See
    [references/api_endpoints.md](references/api_endpoints.md) for field names,
    search syntax, date ranges, and boolean operators.

## Recipes

Common query patterns for drugs, devices, foods, tobacco, cosmetics, animal and
veterinary products, substances, transparency data, adverse events, recalls,
labeling, approvals, shortages, 510(k) clearances, NDC lookups, any FDA safety
or regulatory data query, and more. See
[references/recipes.md](references/recipes.md) for the full recipes.

## Workflow

1.  Search for records using `search` with `--output`. Read the output file.
2.  Use `count` with `--summary 10 --output` to summarize field distributions.
3.  Use `download` (with `--all_results` for exhaustive pulls) to fetch larger
    datasets.
4.  Read and analyze the output file using standard tools.
5.  For MedDRA term hierarchy questions, use a biomedical ontology service skill
    (e.g. EMBL-EBI OLS skill with the HP or NCIT ontology) to look up the term.
