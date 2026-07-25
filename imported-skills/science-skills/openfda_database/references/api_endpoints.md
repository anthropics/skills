# openFDA API Endpoints Reference

## Base URL

All requests go to `https://api.fda.gov/{category}/{endpoint}.json`.

## Authentication

- **Without API key**: 240 requests/min, 1,000/day per IP
- **With API key**: 240 requests/min, 120,000/day per key

Pass via `--api_key` flag or `FDA_API_KEY` environment variable.

> **Important**: Without an API key you are capped at 1,000 requests/day.
> An automated agent can easily exceed this in a single session. Always set a
> key before running multi-query workflows.

## Query Syntax

### Search

```
search=field:term
```

- `search=field:term` — match a single term
- `search=field:term+AND+field:term` — match ALL terms
- `search=field:term+field:term` — match ANY term (OR)
- `search=field:[20200101+TO+20201231]` — date range
- `search=field:"exact+phrase"` — exact phrase matching

### Exact Matching (.exact)

For categorical fields (drug names, reaction terms, manufacturer names), use
the `.exact` suffix to match whole phrases rather than individual tokens:

```
search=openfda.brand_name.exact:"TYLENOL"
count=patient.reaction.reactionmeddrapt.exact
```

Without `.exact`, the API tokenizes multi-word values and returns noisy partial
matches. Always use `.exact` when:

- Searching for a specific product by brand name
- Counting reaction terms or manufacturer names
- Querying any field that contains multi-word values

### Sort

```
sort=field:asc
sort=field:desc
```

### Count

Use `count=field` to aggregate unique values. Add `.exact` suffix for
whole-phrase counting:

```
count=patient.reaction.reactionmeddrapt.exact
```

### Pagination

- `limit=N` — number of results (max 1000)
- `skip=N` — offset for pagination (max 25000)

### Date Formats

openFDA requires dates in **YYYYMMDD** format (not ISO 8601). Date ranges use
bracket syntax with `+TO+`:

```
search=receivedate:[20230101+TO+20231231]
```

**Common pitfalls:**

| Format | Valid? |
|---|---|
| `20230101` | ✓ Correct |
| `[20230101+TO+20231231]` | ✓ Correct range |
| `2023-01-01` | ✗ Will cause an API error |
| `2023/01/01` | ✗ Will cause an API error |
| `January 1, 2023` | ✗ Will cause an API error |

## All Endpoints

### Drug (6 endpoints)

| Endpoint | Path | Description |
|---|---|---|
| event | `/drug/event.json` | Adverse event reports (FAERS) |
| label | `/drug/label.json` | Structured product labeling (SPL) |
| ndc | `/drug/ndc.json` | National Drug Code directory |
| enforcement | `/drug/enforcement.json` | Recall enforcement reports |
| drugsfda | `/drug/drugsfda.json` | Drug approvals since 1939 |
| shortages | `/drug/shortages.json` | Drug shortage reports |

### Device (9 endpoints)

| Endpoint | Path | Description |
|---|---|---|
| 510k | `/device/510k.json` | 510(k) premarket clearances |
| classification | `/device/classification.json` | Device classification data |
| enforcement | `/device/enforcement.json` | Recall enforcement reports |
| event | `/device/event.json` | Adverse event reports (MDR) |
| pma | `/device/pma.json` | Premarket approval (Class III) |
| recall | `/device/recall.json` | Device recall details |
| registrationlisting | `/device/registrationlisting.json` | Facility registrations |
| udi | `/device/udi.json` | Unique Device Identifiers (GUDID) |
| covid19serology | `/device/covid19serology.json` | COVID-19 antibody test data |

### Food (2 endpoints)

| Endpoint | Path | Description |
|---|---|---|
| enforcement | `/food/enforcement.json` | Food recall enforcement reports |
| event | `/food/event.json` | CAERS adverse event reports |

### Tobacco (4 endpoints)

| Endpoint | Path | Description |
|---|---|---|
| problem | `/tobacco/problem.json` | Tobacco product problem reports |
| researchpreventionads | `/tobacco/researchpreventionads.json` | Prevention ads research |
| researchdigitalads | `/tobacco/researchdigitalads.json` | Digital ads research |
| researchsmokefree | `/tobacco/researchsmokefree.json` | Smokefree campaign research |

### Other (4 endpoints)

| Endpoint | Path | Description |
|---|---|---|
| historicaldocument | `/other/historicaldocument.json` | FDA press releases 1913-2014 |
| nsde | `/other/nsde.json` | NDC SPL data elements |
| substance | `/other/substance.json` | Substance molecular data |
| unii | `/other/unii.json` | Unique Ingredient Identifiers |

### Animal & Veterinary (1 endpoint)

| Endpoint | Path | Description |
|---|---|---|
| event | `/animalandveterinary/event.json` | Animal drug adverse events |

### Cosmetic (1 endpoint)

| Endpoint | Path | Description |
|---|---|---|
| event | `/cosmetic/event.json` | Cosmetic adverse event reports |

### Transparency (1 endpoint)

| Endpoint | Path | Description |
|---|---|---|
| crl | `/transparency/crl.json` | Complete Response Letters |

## Common Field Names

### Drug Adverse Events (`drug/event`)

- `patient.drug.medicinalproduct` — drug name
- `patient.reaction.reactionmeddrapt` — reaction term (MedDRA PT)
- `serious` — 1 for serious, 2 for not serious
- `occurcountry` — country code
- `receivedate` — date received (YYYYMMDD)
- `patient.drug.drugindication` — drug indication

### Drug Labeling (`drug/label`)

- `openfda.brand_name` — brand name (use `.exact` for precise matching)
- `openfda.generic_name` — generic name
- `openfda.manufacturer_name` — manufacturer
- `indications_and_usage` — indications
- `warnings` — warnings section
- `dosage_and_administration` — dosage info

### Drug Shortages (`drug/shortages`)

- `generic_name` — generic drug name
- `status` — shortage status
- `proprietary_name` — brand/proprietary name

### Device Events (`device/event`)

- `device.generic_name` — device generic name
- `device.brand_name` — device brand name
- `device.manufacturer_d_name` — manufacturer
- `mdr_text.text` — event narrative

### Animal & Veterinary Events (`animalandveterinary/event`)

- `animal.species` — species name (e.g. Dog, Cat, Horse)
- `animal.breed.breed_component` — breed
- `animal.gender` — gender
- `reaction.veddra_term_name` — reaction term
- `drug.brand_name` — drug brand name
- `serious_ae` — serious adverse event flag

### Food Enforcement (`food/enforcement`)

- `reason_for_recall` — recall reason
- `classification` — Class I, II, or III
- `recalling_firm` — company name
- `product_description` — product details
- `recall_initiation_date` — date of recall (YYYYMMDD)
