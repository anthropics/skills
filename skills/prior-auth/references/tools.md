# Healthcare MCP Tool Reference

A quick reference guide for the Clinical Trials, CMS Coverage, ICD-10, and NPI MCP connectors.

---

## Clinical Trials

| Tool | Purpose |
|------|---------|
| `trials_search` | Search ClinicalTrials.gov by condition, intervention, sponsor, location, status, or phase. Supports geographic radius search. Returns up to 100 results, sorted by most recently updated. |
| `trials_details` | Get comprehensive details for a specific trial by NCT ID, including eligibility criteria, outcomes, study design, and contact information. |

---

## CMS Coverage

| Tool | Purpose |
|------|---------|
| `cms_search_all` | Unified search across NCDs, LCDs, and Articles. Good starting point when document type is unknown. |
| `cms_search_ncds` | Search National Coverage Determinations (national-level Medicare policies that apply uniformly across all states). |
| `cms_search_lcds` | Search Local Coverage Determinations (regional policies by Medicare Administrative Contractors). Filter by state or contractor. |
| `cms_search_articles` | Search billing and coding guidance documents related to LCDs. |
| `cms_lcd_details` | Get full LCD details including policy text, HCPC codes, ICD-10 codes, and related documents. |
| `cms_article_details` | Get complete article details with codes, modifiers, bill types, and revenue codes. |
| `cms_search_medcac` | Search MEDCAC (Medicare Evidence Development & Coverage Advisory Committee) meetings. |
| `cms_contractors` | List Medicare Administrative Contractors and their jurisdictions. Filter by state or contract type. |
| `cms_states` | List valid state codes for use in other CMS tools. |
| `cms_whats_new` | Find recently updated or newly published coverage determinations (last 30 days by default). |

---

## ICD-10

| Tool | Purpose |
|------|---------|
| `icd10_search_codes` | Primary entry point: search diagnosis codes by clinical description, symptom, condition, or partial code. |
| `icd10_get_details` | Get comprehensive info for a specific code: description, billability, chapter placement, and coding guidance. |
| `icd10_validate` | Validate one or more codes for correctness and billability. Use for pre-submission claim validation. |
| `icd10_hierarchy` | Navigate parent-child relationships in the code tree (find more specific or broader codes). |
| `icd10_category` | Browse codes by chapter, body system, or condition type (e.g., "diabetes", "circulatory"). |
| `icd10_chapters` | List all 21 ICD-10-CM chapters with code ranges. Good orientation starting point. |

---

## NPI

| Tool | Purpose |
|------|---------|
| `npi_lookup_provider` | Look up a specific provider by their 10-digit NPI number. Returns demographics, addresses, specialties, and identifiers. |
| `npi_search_providers` | Search providers by name, location, specialty, or organization. Supports wildcards. Filter by individual (NPI-1) or organization (NPI-2). |
| `npi_verify_credentials` | Batch validate NPIs: checks format validity and confirms registration status in NPPES. |