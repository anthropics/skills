---
name: clinical-trials-database
description: >
  Query ClinicalTrials.gov via APIv2. Use when you want to search for trials by
  condition, drug, location, status, or phase; retrieve trial details by NCT ID;
  check eligibility/inclusion criteria; count trials across conditions or time
  periods; identify a sponsor's trial portfolio; find recruiting trials for
  patient matching.
---

# Clinical Trials Database

## Prerequisites

1.  **`uv`**: Read the `uv` skill and follow its Setup instructions to ensure
    `uv` is installed and on PATH.
2.  **User Notification**: If .licenses/clinical_trials_database_LICENSE.txt
    does not already exist in the workspace root directory then (1) prominently
    notify the user to check the terms at https://clinicaltrials.gov/, then (2)
    create the file recording the notification text and timestamp.

## Overview

Access worldwide clinical trial data from ClinicalTrials.gov via the REST API
v2. The CLI script at `scripts/clinical_trials_api.py` wraps the API with
dedicated flags for common filters (phase, age group, status, intervention,
sponsor, etc.) so you rarely need to construct raw queries.

## Core Rules

-   **Use the Wrapper**: ALWAYS execute the provided helper scripts to query the
    database rather than accessing the database directly. The scripts
    automatically enforce the required rate limit gracefully.
-   **Always use `--fields`** — trial JSON records can be very large; restrict
    to the data points you need.
-   **Use `--count-total` first** — check result volume before fetching all
    records.
-   **Paginate large result sets** — use `--limit` with `--page-token` to
    iterate.
-   **Trust Search Filters**: Do not manually re-filter results unless
    explicitly asked to verify detailed eligibility.
-   **Notification**: If this skill is used, ensure this is mentioned in the
    output.

## Context Efficiency Warning

Trial JSON records can be very large. **Always** use the `--fields` parameter to
restrict the response to only the data points you need. After writing to file,
read only the fields you need rather than the entire file.

> [!TIP] Use `references/studies_schema.md` to identify exact field paths for
> `--fields`.

## Response Layout Summary

API responses contain a list of studies (usually in a `studies[]` array). Each
study is split into `protocolSection` and optional `resultsSection`.

> [!Tip] Use the **shorthand aliases** below with the `--fields` parameter to
> request specific data and keep responses small.

### Top-Level Fields

-   `totalCount` — Total studies matching query (integer)
-   `studies[]` — Array of study objects
-   `nextPageToken` — cursor string for pagination

### Common Study Fields (and shorthand alias)

-   **Identification**
    -   `protocolSection.identificationModule.nctId` (`NCTId`) — Unique trial ID
    -   `protocolSection.identificationModule.briefTitle` (`BriefTitle`) — Short
        title
-   **Status**
    -   `protocolSection.statusModule.overallStatus` (`OverallStatus`) —
        Recruitment status
-   **Description**
    -   `protocolSection.descriptionModule.briefSummary` (`BriefSummary`) —
        Short description
-   **Arms & Interventions**
    -   `protocolSection.armsInterventionsModule.interventions`
        (`ArmsInterventionsModule`)
-   **Eligibility**
    -   `protocolSection.eligibilityModule.eligibilityCriteria`
        (`EligibilityCriteria`) — Inclusion/Exclusion
    -   `protocolSection.eligibilityModule.stdAges` (`StdAge`) — CHILD, ADULT,
        etc.

Consult `references/studies_schema.md` for full paths (Locations, Outcomes,
Results) and common `--fields` recipes.

## Commands

### Search for studies

Use for: finding trials by disease, drug, phase, status, age group, or any
combination of these filters.

```bash
uv run scripts/clinical_trials_api.py search \
  --condition "<disease>" \
  --intervention "<drug_or_treatment>" \
  --status "<status>" \
  --phase "<phase>" \
  --age-group "<age_group>" \
  --study-type "<study_type>" \
  --sponsor "<sponsor_name>" \
  --has-results \
  --sort "<field>:<asc|desc>" \
  --fields "<fields>" \
  --limit <N> \
  --count-total \
  --page-token "<token>" \
  --output /tmp/search_results.json
```

All flags are optional and combine via AND logic.

**Flag reference:**

-   `--condition` — Disease or condition to search for (e.g. `"cystic
    fibrosis"`).
-   `--intervention` — Drug, device, or treatment name (e.g. `"pembrolizumab"`).
-   `--status` — Recruitment status filter. Values: RECRUITING, COMPLETED,
    NOT_YET_RECRUITING, ACTIVE_NOT_RECRUITING, ENROLLING_BY_INVITATION,
    TERMINATED, SUSPENDED, WITHDRAWN.
-   `--phase` — Trial phase filter. Values: PHASE1, PHASE2, PHASE3, PHASE4,
    EARLY_PHASE1, NA.
-   `--age-group` — Patient age group filter. Values: CHILD (0–17), ADULT
    (18–64), OLDER_ADULT (65+).
-   `--study-type` — Type of study. Values: INTERVENTIONAL, OBSERVATIONAL,
    EXPANDED_ACCESS.
-   `--sponsor` — Lead sponsor or institution name (e.g. `"National Cancer
    Institute"`).
-   `--has-results` — Boolean flag (no value needed). When present, filters for
    studies that have results available on ClinicalTrials.gov.
-   `--sort` — Sort order as `FieldName:asc` or `FieldName:desc`. Common fields:
    `LastUpdatePostDate`, `EnrollmentCount`, `StudyFirstPostDate`, `StartDate`.
-   `--fields` — Comma-separated list of JSON field names to include in the
    response. Use this to keep responses small (e.g.
    `"NCTId,BriefTitle,OverallStatus,Phase"`). See
    `references/studies_schema.md` for available field paths.
-   `--limit` — Maximum number of studies to return per request (1–1000, default
    10).
-   `--count-total` — Boolean flag (no value needed). When present, the response
    includes a `totalCount` field showing the total number of matching studies
    across all pages.
-   `--page-token` — An opaque cursor string used to fetch the next page of
    results. Obtain this value from the `nextPageToken` field in a previous
    search response. Do not construct this string yourself; always copy it
    verbatim from the API response. See the Pagination section below.
-   `--advanced` — Raw Essie filter expression for structured queries beyond the
    dedicated flags (e.g. `"AREA[LocationCountry]United States"`). Combined with
    other flags via AND. See `references/clinical_trials_api.md` for syntax.
-   `--output` — **(Required)** File path where the JSON response is written.

**Example — actively recruiting Phase 3 pediatric cystic fibrosis trials:**

```bash
uv run scripts/clinical_trials_api.py search \
  --condition "cystic fibrosis" \
  --status RECRUITING \
  --phase PHASE3 \
  --age-group CHILD \
  --fields "NCTId,BriefTitle,OverallStatus,Phase" \
  --limit 10 \
  --output /tmp/cf_trials.json
```

**Example — recruiting atezolizumab trials for esophageal cancer:**

```bash
uv run scripts/clinical_trials_api.py search \
  --condition "esophageal cancer" \
  --intervention "Atezolizumab" \
  --status RECRUITING \
  --fields "NCTId,BriefTitle,Phase" \
  --limit 10 \
  --output /tmp/atezolizumab_trials.json
```

### Retrieve a study by NCT ID

Use for: fetching full details of a specific trial when you already have the NCT
identifier.

```bash
uv run scripts/clinical_trials_api.py get-study \
  <nct_id> [--fields "<fields>"] \
  --output /tmp/study.json
```

Returns a useful default set of fields if `--fields` is omitted:
`NCTId,BriefTitle,OverallStatus,Phase,BriefSummary,`
`ConditionsModule,ArmsInterventionsModule,EligibilityModule`

**Structure of the default response:**

```json
{
  "protocolSection": {
    "identificationModule": {
      "nctId": "NCT00000000",
      "briefTitle": "Study Title"
    },
    "statusModule": {
      "overallStatus": "RECRUITING"
    },
    "descriptionModule": {
      "briefSummary": "This study is about..."
    },
    "conditionsModule": {
      "conditions": [ "Condition Name" ]
    },
    "armsInterventionsModule": {
      "interventions": [ { "type": "DRUG", "name": "Drug Name" } ]
    },
    "eligibilityModule": {
      "eligibilityCriteria": "Inclusion:\n- ...",
      "stdAges": [ "ADULT" ]
    }
  }
}
```

### Get eligibility / inclusion criteria

Use for: pulling inclusion/exclusion rules, age ranges, and sex requirements for
patient-matching tasks.

```bash
uv run scripts/clinical_trials_api.py \
  get-eligibility <nct_id> \
  --output /tmp/eligibility.json
```

Shortcut that returns title and the full eligibility module (inclusion/exclusion
criteria, age range, sex).

**Example — inclusion criteria for NCT04886804:**

```bash
uv run scripts/clinical_trials_api.py \
  get-eligibility NCT04886804 \
  --output /tmp/eligibility_NCT04886804.json
```

### Count matching studies

Use for: exploring the trial landscape — checking how many trials exist for a
condition, phase, or status before fetching full records.

```bash
uv run scripts/clinical_trials_api.py count \
  --condition "<disease>" \
  [--status "<status>"] [--phase "<phase>"] ... \
  --output /tmp/count.json
```

Returns only the total count of clinical trials matching the search criteria
without fetching study records. Accepts the same filter flags as `search`.

### Search by location / geography

Use for: narrowing trials to a specific country, state, or city.

Use `--advanced` with `AREA[LocationCountry]` or `AREA[LocationCity]` to
restrict results by geography:

```bash
uv run scripts/clinical_trials_api.py search \
  --condition "cystic fibrosis" \
  --status RECRUITING \
  --advanced "AREA[LocationCity]New York" \
  --fields "NCTId,BriefTitle" \
  --limit 20 \
  --output /tmp/nyc_cf_trials.json
```

### Search by sponsor / organization

Use for: identifying a sponsor's or institution's trial portfolio.

Use `--sponsor` to find trials run by a specific institution or company:

```bash
uv run scripts/clinical_trials_api.py search \
  --sponsor "National Cancer Institute" \
  --fields "NCTId,BriefTitle,LeadSponsorName" \
  --limit 20 \
  --output /tmp/nci_trials.json
```

### Combined multi-criteria search

Use for: complex queries that layer multiple filters (condition and drug and
phase and geography and sponsor, etc.).

All flags combine via AND, so you can layer conditions, interventions, status,
phase, geography, and sponsor in a single query:

```bash
uv run scripts/clinical_trials_api.py search \
  --condition "pancreatic cancer" \
  --intervention "immunotherapy" \
  --status RECRUITING \
  --phase PHASE3 \
  --advanced "AREA[LocationCountry]United States" \
  --fields "NCTId,BriefTitle,Phase,LeadSponsorName" \
  --limit 20 \
  --output /tmp/panc_trials.json
```

### Raw API query (escape hatch)

Use for: uncommon endpoints or parameter combinations not covered by the
dedicated flags.

```bash
uv run scripts/clinical_trials_api.py raw-query \
  --endpoint <path> \
  --params '<json_dict>' \
  --output /tmp/raw_result.json
```

## Pagination

When results exceed `--limit`, the response includes a `nextPageToken`. Pass it
with `--page-token` to fetch the next page:

```bash
uv run scripts/clinical_trials_api.py search \
  --condition "breast cancer" \
  --status RECRUITING \
  --limit 50 --count-total \
  --output /tmp/breast_cancer_p1.json

uv run scripts/clinical_trials_api.py search \
  --condition "breast cancer" \
  --status RECRUITING \
  --limit 50 --page-token "CAo=" \
  --output /tmp/breast_cancer_p2.json
```

## Advanced Querying

For complex filtering beyond the dedicated flags, use `--advanced` with an Essie
expression.

**What is an Essie Expression?** Essie is the search engine powering
ClinicalTrials.gov. An Essie expression is a structured query that targets
specific fields (e.g., country, phase) rather than doing general keyword
searches.

-   **`AREA[Field]Value`**: Targets a specific field.
    -   `AREA[LocationCountry]United States`
    -   `AREA[Phase]PHASE3`
-   **Boolean operators**: Combine with `AND`, `OR`, `NOT`.
-   **`RANGE[min, max]`**: For numeric/date fields (e.g. `RANGE[500, MAX]`).

See `references/clinical_trials_api.md` for syntax and available fields.

It is combined with other flags via AND:

```bash
uv run scripts/clinical_trials_api.py search \
  --condition "diabetes" \
  --advanced "AREA[LocationCountry]United States \
    AND AREA[EnrollmentCount]RANGE[500, MAX]" \
  --fields "NCTId,BriefTitle,EnrollmentCount" \
  --output /tmp/diabetes_us_large.json
```

## References

-   **API parameters, enum values, and Essie syntax:**
    `references/clinical_trials_api.md`
-   **JSON field paths and `--fields` recipes:** `references/studies_schema.md`
