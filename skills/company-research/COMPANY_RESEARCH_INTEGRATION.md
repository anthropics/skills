# Company Research v2 — Output Data Contract

## What this is

`~/code/ToolUniverse/skills/company-research/python_implementation.py` is a
Python script that collects structured intelligence on a company by hitting
16 public APIs in parallel via the ToolUniverse SDK. No LLM calls. No
inference. Pure deterministic data collection. It outputs a single JSON file.

## How to run it

```bash
cd ~/code/ToolUniverse && source .venv/bin/activate && \
python3 skills/company-research/python_implementation.py \
  "COMPANY_NAME" --output-dir OUTPUT_DIR
```

- `COMPANY_NAME` (required): e.g. `"Moderna"`, `"Myriad Genetics"`, `"Anthropic"`
- `--output-dir` / `-o` (optional): directory for the JSON file. Defaults to `.`
  Created automatically if it doesn't exist.
- Runtime: ~3 seconds (public company), ~1.5 seconds (private company)
- Returns: prints the output path to stdout

The Python entry point is:

```python
from python_implementation import company_research
path: str = company_research("Moderna", output_dir="/tmp/output")
```

## Output file

**Filename pattern**: `company_data_{slug}_{timestamp}.json`

- `{slug}`: company name lowercased, non-alphanumeric replaced with `_`, truncated to 30 chars
- `{timestamp}`: `YYYYMMDD_HHMMSS`
- Example: `company_data_moderna_20260322_092137.json`

Typical file size: 400-500 KB for a public biotech, 5-10 KB for a private company.

## JSON schema

All fields are always present. Empty sections use `{}` or `[]`, never `null`.

```json
{
  "meta": {},
  "identity": {},
  "financials": {},
  "pipeline": {},
  "regulatory": {},
  "foundation": {},
  "sources": [],
  "data_gaps": []
}
```

### `meta` (object)

Always present, always populated.

| Field | Type | Example | Notes |
| ----- | ---- | ------- | ----- |
| `company` | string | `"Moderna"` | Raw input string, unchanged |
| `timestamp` | string | `"2026-03-22T09:21:37.123456"` | ISO 8601 |
| `is_public` | bool | `true` | `true` if SEC CIK was found |
| `version` | string | `"2.0"` | Schema version. Ignore `"1.0"` artifacts |

### `identity` (object)

Company disambiguation results.

| Field | Type | Present | Source |
| ----- | ---- | ------- | ------ |
| `name` | string | always | Wikipedia canonical name, or raw input if lookup failed |
| `is_public` | bool | always | Derived from `bool(cik)` |
| `cik` | string | public only | SEC EDGAR Central Index Key, e.g. `"1682852"` |
| `ticker` | string | public only | Extracted from SEC company string, e.g. `"MRNA"` |
| `sector` | string | usually | Wikidata entity description, e.g. `"American pharmaceutical and biotechnology company"` |
| `wikidata_id` | string | usually | Wikidata Q-number, e.g. `"Q28406867"` |

### `financials` (object)

Empty `{"recent_filings": [], "full_submissions": {}}` for private companies.

| Field | Type | Notes |
| ----- | ---- | ----- |
| `recent_filings` | array of objects | SEC filings from last 180 days. Deduplicated by `form-accession`. Each object has `form`, `file_date`, `accession`, `company` |
| `full_submissions` | object | Raw SEC EDGAR company submissions blob. Contains `filings.recent` with arrays of `accessionNumber`, `form`, `filingDate`, `primaryDocument` |

### `pipeline` (object)

Seven sub-keys, all arrays of objects. Any can be `[]` if the API returned nothing.

| Field | Source API | Key fields per item |
| ----- | ---------- | ------------------- |
| `clinical_trials` | ClinicalTrials.gov | `nct_id` or `nctId`, `brief_title` or `briefTitle`, `phases`, `overallStatus` |
| `preprints` | Europe PMC (SRC:PPR) | `title`, `doi`, `firstPublicationDate`, `pubYear` |
| `publications` | PubMed | `title`, `pub_date` or `pubdate`, `journal` or `fulljournalname` |
| `fda_approved` | FDA Orange Book | `brand_name` or `trade_name`, `active_ingredient`, `application_number` |
| `fda_approvals_history` | OpenFDA | Approval records by `sponsor_name` |
| `adverse_events` | FAERS | Adverse event reaction counts by `medicinalproduct` |
| `research_output` | OpenAlex | `title`, `publication_year`, `cited_by_count` |

**Field name variation**: Upstream APIs return inconsistent key names (e.g.
`nct_id` vs `nctId`, `brief_title` vs `briefTitle`). The collector passes
through raw API responses without normalizing. Downstream consumers should
check both variants.

### `regulatory` (object)

Three sub-keys, all arrays of objects. All can be `[]`.

| Field | Source API | Search pattern |
| ----- | ---------- | -------------- |
| `device_510k` | OpenFDA 510(k) | `applicant:"{company}"` |
| `enforcement_actions` | OpenFDA enforcement | `recalling_firm:"{company}"` |
| `drug_labels` | OpenFDA labels | `openfda.manufacturer_name:"{company}"` |

### `foundation` (object)

| Field | Type | Notes |
| ----- | ---- | ----- |
| `wikipedia_summary` | string | Up to 4000 chars. Empty string `""` if not found |
| `crossref_works` | array of objects | Up to 5 Crossref DOI records. Each has `title`, `DOI`, `publisher`, etc |

### `sources` (array of objects)

Every successful API call appends one entry. This is your provenance log.

```json
{"tool": "SEC_EDGAR_search_filings", "query": "Moderna", "items": 5, "tier": "T1"}
```

| Field | Type | Notes |
| ----- | ---- | ----- |
| `tool` | string | Exact ToolUniverse tool name |
| `query` | string | The query or search term used |
| `items` | int | Count of items returned |
| `tier` | string | Evidence tier: `"T1"`, `"T2"`, or `"T3"` |

Typical count: 14-16 entries for a public biotech, 8-12 for a private company.

### `data_gaps` (array of strings)

Human-readable messages for tools that failed or returned no data.

```json
[
  "No CIK found — skipping SEC financial data (private company)",
  "FDA Orange Book search failed",
  "Crossref search failed"
]
```

These are informational, not errors. A private company will always have
`"No CIK found..."` in its gaps. A pre-commercial company will have
FDA-related gaps. This is expected behavior.

## Evidence tiers

| Tier | Sources | Meaning |
| ---- | ------- | ------- |
| T1 | SEC EDGAR, FDA (Orange Book, OpenFDA), ClinicalTrials.gov, FAERS | Regulatory/official filings |
| T2 | PubMed, OpenAlex, Crossref | Peer-reviewed or indexed academic |
| T3 | Wikipedia, Wikidata, Europe PMC preprints | Unvalidated / community-sourced |

## Edge cases

**Private company** (`is_public: false`):


- `identity.cik` and `identity.ticker` will be absent
- `financials` = `{"recent_filings": [], "full_submissions": {}}`
- `data_gaps` will include `"No CIK found — skipping SEC financial data (private company)"`
- All other sections still populate normally


**All APIs fail**:

- The collector always produces valid JSON, even if every tool errors
- `sources` will be `[]`, `data_gaps` will list every failure
- Section objects will be empty `{}` or `[]`
- `identity.name` falls back to the raw input string


**Company not found**:

- No crash. `identity.name` = raw input, `is_public` = false
- Most sections empty. `data_gaps` lists what failed.

- Example: input `"XYZNONEXISTENT99999"` produces valid 7 KB JSON

**Duplicate filings**:


- SEC filings are deduplicated by `{form}-{accession}` key before output

**Large responses**:

- `clinical_trials` capped at 15 items
- `adverse_events` capped at 20 items
- `publications`, `preprints`, `research_output` capped at 8 each
- `fda_approved`, `fda_approvals_history`, `device_510k`, `enforcement_actions`, `drug_labels` capped at 10 each
- `crossref_works` capped at 5
- `wikipedia_summary` capped at 4000 chars

## The 16 tools and what they write to

| Tool | Writes to | Tier |
| ---- | --------- | ---- |
| `Wikipedia_search` | `identity.name` | T3 |
| `SEC_EDGAR_search_filings` | `identity.cik`, `identity.ticker`, `financials.recent_filings` | T1 |
| `Wikidata_search_entities` | `identity.sector`, `identity.wikidata_id` | T3 |
| `SEC_EDGAR_get_company_submissions` | `financials.full_submissions` | T1 |
| `ClinicalTrials_search_studies` | `pipeline.clinical_trials` | T1 |
| `EuropePMC_search_articles` | `pipeline.preprints` | T3 |
| `PubMed_search_articles` | `pipeline.publications` | T2 |
| `FDA_OrangeBook_search_drug` | `pipeline.fda_approved` | T1 |
| `OpenFDA_search_drug_approvals` | `pipeline.fda_approvals_history` | T1 |
| `FAERS_count_reactions_by_drug_event` | `pipeline.adverse_events` | T1 |
| `openalex_literature_search` | `pipeline.research_output` | T2 |
| `OpenFDA_search_device_510k` | `regulatory.device_510k` | T1 |
| `OpenFDA_search_drug_enforcement` | `regulatory.enforcement_actions` | T1 |
| `OpenFDA_search_drug_labels` | `regulatory.drug_labels` | T1 |
| `Wikipedia_get_content` | `foundation.wikipedia_summary` | T3 |
| `Crossref_search_works` | `foundation.crossref_works` | T2 |
