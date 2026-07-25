# ClinicalTrials.gov API v2 Reference

This document covers the querying mechanics, parameter reference, valid enum
values, and advanced expression syntax for the ClinicalTrials.gov REST API v2.

## Endpoints

- `/studies` — GET — Search and filter studies, returns paginated list
- `/studies/{nctId}` — GET — Retrieve a single study by NCT ID
- `/studies/metadata` — GET — List all available data fields
- `/studies/enums` — GET — List all enum types and valid values
- `/studies/search-areas` — GET — List searchable field areas

## Query Parameters

Query parameters perform ranked text searches. They influence the relevance
ordering of results.

- `query.cond` (`--condition`) — Condition or disease
- `query.intr` (`--intervention`) — Intervention or treatment (drug, device,
  etc.)
- `query.term` (`--term`) — General search across all text fields (57 fields)
- `query.titles` (`--title`) — Study titles and acronyms
- `query.locn` (`--location`) — Location-related fields (city, state, country,
  facility)
- `query.spons` (`--sponsor`) — Sponsor or collaborator name
- `query.id` (`--id`) — Study identifiers (NCT ID, org study ID)

## Filter Parameters

Filter parameters perform exact matching and do not affect relevance ranking.

- `filter.overallStatus` (`--status`) — Recruitment status (comma-separated)
- `filter.advanced` (`--advanced` / `--phase` / `--age-group` / `--study-type` /
  `--sponsor`) — Essie expression for structured filtering
- `filter.ids` — Restrict to specific NCT IDs
- `filter.geo` — Distance-based geographic filter

## Control Parameters

- `fields` (`--fields`) — Comma-separated list of fields to return
- `pageSize` (`--limit`) — Results per page (1–1000, default 10)
- `pageToken` (`--page-token`) — Token for the next page of results
- `countTotal` (`--count-total`) — If `true`, response includes `totalCount`
- `sort` (`--sort`) — Sort field and direction, e.g. `LastUpdatePostDate:desc`
- `format` — Response format: `json` (default) or `csv`

### Sortable Fields

Common sortable fields: `LastUpdatePostDate`, `NumericChange`,
`EnrollmentCount`, `StudyFirstPostDate`, `StartDate`.

Format: `FieldName:asc` or `FieldName:desc`.

## Valid Enum Values

### Recruitment Status (`filter.overallStatus`)

- `RECRUITING` — Currently enrolling participants
- `NOT_YET_RECRUITING` — Approved but not yet enrolling
- `ACTIVE_NOT_RECRUITING` — Ongoing but no longer enrolling
- `ENROLLING_BY_INVITATION` — Enrolling by invitation only
- `COMPLETED` — Study finished
- `SUSPENDED` — Temporarily halted
- `TERMINATED` — Stopped early
- `WITHDRAWN` — Pulled before enrollment

### Phase

- `EARLY_PHASE1` — Early Phase 1 (formerly Phase 0)
- `PHASE1` — Phase 1
- `PHASE2` — Phase 2
- `PHASE3` — Phase 3
- `PHASE4` — Phase 4 (post-marketing)
- `NA` — Not Applicable

### Standard Age Group (`StdAge`)

- `CHILD` — Birth to 17 years
- `ADULT` — 18 to 64 years
- `OLDER_ADULT` — 65+ years

### Study Type

- `INTERVENTIONAL` — Tests a treatment or intervention
- `OBSERVATIONAL` — Observes outcomes without intervention
- `EXPANDED_ACCESS` — Treatment use outside of clinical trials

### Sex

- `ALL` — All sexes eligible
- `MALE` — Males only
- `FEMALE` — Females only

## Essie Expression Syntax (for `filter.advanced`)

The `filter.advanced` parameter accepts Essie expressions for structured,
non-ranked filtering.

### AREA Operator

Target a specific field: `AREA[FieldName]Value`

Examples:

- `AREA[Phase]PHASE3` — Phase 3 trials only
- `AREA[StdAge]CHILD` — Trials accepting pediatric patients
- `AREA[StudyType]INTERVENTIONAL` — Interventional studies only
- `AREA[LeadSponsorName]Pfizer` — Sponsored by Pfizer
- `AREA[LocationCountry]United States` — Located in the US
- `AREA[Sex]FEMALE` — Female-only trials

### Boolean Operators

Combine clauses with `AND`, `OR`, `NOT`:

- `AREA[Phase]PHASE3 AND AREA[StdAge]CHILD`
- `AREA[Phase]PHASE2 OR AREA[Phase]PHASE3`
- `NOT AREA[StudyType]OBSERVATIONAL`

### RANGE Operator

Filter date or numeric fields within a range:

- `AREA[StartDate]RANGE[01/01/2023, MAX]` — Started on or after Jan 1, 2023
- `AREA[EnrollmentCount]RANGE[100, 500]` — Enrollment between 100 and 500
- `AREA[CompletionDate]RANGE[MIN, 12/31/2025]` — Completing before end of 2025

Use `MIN` and `MAX` for open-ended boundaries.

## Response Data Structure

Study records are organised into hierarchical modules:

### protocolSection

- **identificationModule** — NCT ID, titles, organisation
- **statusModule** — overall status, start / completion dates, last update
- **sponsorCollaboratorsModule** — lead sponsor, collaborators, responsible
  party
- **descriptionModule** — brief summary, detailed description
- **conditionsModule** — conditions under study
- **designModule** — study type, phases, enrolment info
- **armsInterventionsModule** — study arms and interventions
- **outcomesModule** — primary and secondary outcomes
- **eligibilityModule** — inclusion / exclusion criteria, age / sex requirements
- **contactsLocationsModule** — contacts and site locations
- **referencesModule** — citations and links

### derivedSection

- **conditionBrowseModule** — MeSH terms for conditions
- **interventionBrowseModule** — MeSH terms for interventions

### resultsSection (when available)

- **participantFlowModule** — participant flow
- **baselineCharacteristicsModule** — baseline data
- **outcomeMeasuresModule** — outcome results
- **adverseEventsModule** — adverse events

### hasResults

Boolean flag indicating whether results have been posted for the study.

## Pagination

When results exceed the page size, the response includes a `nextPageToken`field.
Pass this token via the `pageToken` parameter (or `--page-token` flag) to fetch
the next page. The final page omits this token.

Response shape for multi-study queries:
```json
{
  "totalCount": 1234,
  "studies": [...],
  "nextPageToken": "CAo="
}
```

## Data Standards

- **Dates** — ISO 8601 structured objects,
  e.g. `{"date": "2024-03-15", "type": "ACTUAL"}`
- **Rich text** — descriptive fields use CommonMark Markdown
- **Enums** — status, phase, study type, and similar fields use standardised
  enumerated values (not free text)
