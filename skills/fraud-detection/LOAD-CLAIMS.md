# LOAD-CLAIMS — map a payer's raw claims into the canonical schema

Followed when `SKILL.md` step 1 finds no claims DB yet, or the user points at a raw source.
This is a **one-time onboarding per payer**: you author a re-runnable ingest, validate it, and
hand back a `.duckdb` path the sweep reads. The LLM does the mapping; detection stays deterministic.

**Canonical schema** (the contract): `${CLAUDE_PLUGIN_ROOT}/skills/fraud-detection/claims-schema.sql` —
six tables (`claims`, `claim_lines`, `claim_dx`, `members`, `enrollment`, `inpatient_stays`).
Read it first.

## 1. Discover the source

Your posture: **never dead-end.** The user often doesn't know the technical shape of their own
claims data. Every "I don't know" gets a next question that moves toward either (a) a connection
string / file path you can sample, or (b) the name of the person who can give you one. Keep going
until you have ~100 rows in front of you.

**Open with:** *"Where do your adjudicated claims live — a database I can connect to, files you
can drop somewhere, or a system name?"*

| If they say… | Next step |
|---|---|
| "Postgres / Snowflake / SQL Server / BigQuery / Oracle" | Ask for a **read-only connection string** (or `psql`/`sqlcmd` creds). Sample: `duckdb -c "ATTACH '<conn>' AS src; DESCRIBE; SELECT * FROM src.<t> LIMIT 100"`. DuckDB has native scanners for most. |
| "It's in our data warehouse / lake" | Same — that's a SQL endpoint. Ask which (Snowflake/Databricks/Redshift/BigQuery) and for a read role. Parquet on S3/GCS: `duckdb -c "SELECT * FROM read_parquet('s3://…/*.parquet') LIMIT 100"`. |
| "We get 837 files from the clearinghouse" | Ask for one file (any recent 837P/837I). `head -c 50k file.x12` → ISA/GS/ST envelope, 2300 (claim) / 2400 (line) / HI (dx) loops. |
| "We have a FHIR server / Claim resources" | Ask for the base URL + a bearer token (or an ndjson export). `head -n 5 *.ndjson \| jq '.resourceType, .item[0], .diagnosis[0]'`. |
| "CSV / Parquet / extracts" | Ask where they land. `duckdb -c "DESCRIBE SELECT * FROM read_csv_auto('<glob>')"`. |
| A **product name** — "Facets", "QNXT", "HealthEdge/HealthRules", "Epic Tapestry", "Availity", "Plexis" | These all sit on a SQL DB. Ask for a read connection to it and start from the platform's known claim/line tables (e.g. Facets `CMC_CLCL_CLAIM`/`CMC_CDML_CL_LINE`; QNXT `claim`/`claimdetail`). Web-search "<product> data dictionary claims tables" if the user doesn't know the names. |
| "There's an internal API" | Ask for the endpoint + auth and one example request. Write `ingest/<payer>/fetch.js` (paginate → ndjson), then treat as flat file. |
| **"I don't know"** | *"What do your analysts open when they need to look at a claim?"* — that tool's connection is your way in. Still nothing → *"Who on your data/IT side owns the claims warehouse? Can we loop them in?"* You're not blocked; you're routing to the owner. |
| "We can't give you direct access" | Ask for a **one-time extract**: ~6 months of professional + institutional claims with member IDs, as CSV/Parquet to a path you can read. That's enough to build the mapping; production access can follow. |

Once you can see ~100 rows, you have the column names/loops — move to §2.

## 2. Propose the mapping

Write `~/.claude/data/healthcare/fraud-detection/ingest/<payer>/mapping.md` (override the parent
`~/.claude/data/healthcare` with `$CLAUDE_HEALTHCARE_DATA`): for **every** canonical column,
the source expression that fills it (or `NULL — not present in source`). Show it to the user and
get sign-off before writing the converter — this is the design review.

## 3. Write the converter

Produce `~/.claude/data/healthcare/fraud-detection/ingest/<payer>/ingest.sql` (or `.js` for X12/FHIR):

- **SQL source** → `INSERT INTO claims SELECT their_col AS claim_id, … FROM src.schema.table`
- **CSV/Parquet** → `CREATE TABLE claims AS SELECT … FROM read_csv('<glob>', …)` (same pattern as `fetch-reference.js`'s ingest specs)
- **X12 837** → `ingest.js` walks loops: 2300→`claims`, 2400 SV1/SV2→`claim_lines`, HI→`claim_dx`
- **FHIR** → `ingest.js` maps `Claim.item[]`→lines, `Claim.diagnosis[]`→dx, `Claim.provider`→billing_npi

Target DB: `~/.claude/data/healthcare/fraud-detection/data-cache/corpus.duckdb`. Apply `claims-schema.sql`
to it first so the tables exist with the right types.

## 4. Schema extension (additive only)

If the source carries a field detectors could use but `claims-schema.sql` lacks (e.g.
`place_of_service`, `taxonomy_code`, `drg`): propose `ALTER TABLE … ADD COLUMN …`, append it to
`claims-schema.sql` with a comment, and note it in `mapping.md`. **Never rename or drop** an
existing column — detectors depend on the names.

> **Medicaid note.** The `lob` argument (not a per-claim column) routes the NCCI detectors
> (D1/D2/D11) to the Medicaid MUE/PTP tables. State-specific Medicaid coverage policy (state plan
> amendments, fee schedules) is a per-customer feed; not ingested from a public source.

## Members + enrollment

Two tables carry the beneficiary side of the corpus; both come from the **payer's member master /
834 enrollment feed**, not from claims:

- **`members`** — one row per person (`bene_id` PK). `dob`, `dod`, `sex`, `zip` straight from the
  member master. `dod` drives D3 after-death; the rest are context for adjudication/synthesis.
- **`enrollment`** — the coverage timeline: one row per contiguous coverage span
  (`bene_id`, `plan_id`, `program`, `enrolled_state`, `effective_from`, `effective_to`,
  `term_reason`). `program` is **constant per payer feed** = the payer's line of business
  (`medicaid` for a Medicaid MCO, `medicare` for an MA plan). `enrolled_state` is the member's
  state of enrollment from the 834 / member master and routes state-excluded-provider checks (D3)
  and state policy lookup (D4/D19/D20).

**COB / TPL is encoded in `enrollment`, not a separate table.** A second span for the same
`bene_id` whose `[effective_from, effective_to]` overlaps the primary span but carries a
**different `program`** (e.g. a `medicare` span alongside the payer's `medicaid` span) IS the
other-coverage record D21 scans for. Ingest known other-coverage from the payer's COB/TPL file as
additional `enrollment` rows with the other payer's `program`; do not create a `cob` table.

## 5. Load + validate

Run the converter, then `~/.claude/data/healthcare/fraud-detection/ingest/<payer>/validate.sql`:
- row counts vs source
- null-rate per required column (`claim_id`, `billing_npi`, `hcpcs`, `dos_from`, `allowed_amount`)
- format checks: `billing_npi ~ '^\d{10}$'`, `hcpcs ~ '^[A-Z0-9]{5}$'`
- referential: every `claim_lines.claim_id` exists in `claims`

Report the counts and any validation failures.

## 6. Hand off

Print the absolute path to `~/.claude/data/healthcare/fraud-detection/data-cache/corpus.duckdb`. The main skill resumes with
`corpusDb=<that path>`. Detectors attach it alongside the public reference tables:

```sql
ATTACH '<dataRoot>/data-cache/reference/<q>/reference.duckdb' AS ref (READ_ONLY);
ATTACH '<dataRoot>/data-cache/corpus.duckdb'                  AS corpus;
```
