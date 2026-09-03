# Reference data — what feeds the detectors and where to get it

The detectors join claims against ~32 public reference tables in `reference.duckdb` plus
prose policy docs in `policy/`. `node scripts/fetch-reference.js <quarter>` fetches all of
it. This doc is the map for when that script fails, a source moves, or you need a table
that isn't wired yet. The full per-source ingest spec lives in `scripts/fetch-reference.js`
(`SOURCES`); per-source CSV quirks in `scripts/CLAUDE.md`.

## On-disk layout (populated at runtime, never committed)

Everything lands under `~/.claude/data/healthcare/fraud-detection/` (override the parent with `$CLAUDE_HEALTHCARE_DATA`):
`data-cache/reference/<quarter>/reference.duckdb` (~37M rows, ~2GB) + `policy/*.txt`, plus
`data-cache/corpus.duckdb` via `LOAD-CLAIMS.md`. The plugin
install path is a versioned cache wiped on upgrade — never write there.

## Federal CMS — stable, versioned (one fetch-reference.js run)

| Detector(s) | Table(s) | What it is | Base URL / resolver | kind | Cadence |
|---|---|---|---|---|---|
| D1/D11 | `mue`, `mue_medicaid` | NCCI Medically Unlikely Edits | `cms.gov/files/zip/medicare-ncci-{q}-practitioner-services-mue-table.zip` · Medicaid: `…/medicaid-ncci-{q}-mue-edits-…` | `zip` | quarterly |
| D2 | `ptp`, `ptp_medicaid` | NCCI Procedure-to-Procedure edits | `cms.gov/files/zip/medicare-ncci-{q}-practitioner-ptp-edits-ccipra-v###r0-f{1-4}.zip` (re-probe `v###` per quarter) | `zip` | quarterly |
| D3 | `aoc` | Add-on code → primary pairs | `cms.gov/files/zip/add-code-edits-medicare-effective-MMDDYYYY.zip` (date-suffixed; fixed-width → preprocess) | `zip` | quarterly |
| D3/D10 | `leie` | OIG exclusions | `oig.hhs.gov/exclusions/downloadables/UPDATED.csv` | `csv` | monthly, stable URL |
| D4 | `article_x_*`, `lcd*`, `ncd_*` | MCD coverage Articles/LCDs/NCDs (HCPCS↔ICD-10) | `downloads.cms.gov/medicare-coverage-database/downloads/exports/{current_article,all_lcd,ncd}.zip` (zip-in-zip) | `mcd-coverage` | rolling |
| D7 | `partb_by_provider*`, `psps`, `partb_by_geography` | Part B utilization benchmarks | data.cms.gov DCAT — title `Medicare Physician & Other Practitioners …` | `cms-catalog` | annual |
| D9 | `order_and_referring` | Providers eligible to order/refer | data.cms.gov DCAT — title `Order and Referring` | `cms-catalog` | weekly |
| D10 | `revoked_providers` | Revoked Medicare suppliers | data.cms.gov DCAT — title `Revoked Medicare Providers and Suppliers` | `cms-catalog` | monthly |
| D14 | `opt_out` | Opt-out affidavits | data.cms.gov DCAT — title `Opt Out Affidavits` | `cms-catalog` | quarterly |
| D15 | `dmepos_by_supplier`, `dmepos_by_referrer` | DMEPOS utilization | data.cms.gov DCAT — title `Medicare Durable Medical Equipment…` | `cms-catalog` | annual |
| D16 | `partd_by_provider` | Part D prescribing | data.cms.gov DCAT — title `Medicare Part D Prescribers - by Provider` | `cms-catalog` | annual |
| D17 | `market_saturation_county` | Provider density vs benes | data.cms.gov DCAT — title `Market Saturation & Utilization State-County` | `cms-catalog` | semiannual |
| D18 | `owners_*` | Facility ownership (HHA/hospice/SNF/hospital) | data.cms.gov DCAT — title `<Facility> All Owners` | `cms-catalog` | monthly |
| D7 | `ffs_enrollment`, `taxonomy_crosswalk` | PECOS enrollment + specialty map | data.cms.gov DCAT | `cms-catalog` | monthly |
| exposure-$ | `pfs` | PFS RVU file | `cms.gov/files/zip/rvu{yy}{q}-updated-MM-DD-YYYY.zip` (suffix unpredictable — re-probe PFS RVU page) | `zip` | annual+ |
| D2 adjudicate | `policy/mln1783722.txt`, `policy/ncci-policy-ch1.txt` | MLN modifier-59 + NCCI Ch.1 prose | `cms.gov/files/document/<slug>.pdf` (occasionally renumber) | `pdf` | static |

> **CPT® / data licensing.** CPT® codes and descriptions are copyright American Medical
> Association. CPT is a registered trademark of the AMA. Use of CPT in this tool requires a valid
> AMA CPT license; payers processing claims typically hold one. The NCCI, PFS, and MCD datasets
> this tool ingests carry the AMA's standard license notice — see the header of any fetched NCCI
> file. This tool does not redistribute CPT content; it reads the files you fetch under your license.

**`cms-catalog` = never hardcode the download URL.** Resolve from `https://data.cms.gov/data.json`
by dataset title regex → latest CSV `distribution`. The catalog always carries the current release
path even after CMS rotates the GUID.

**When a federal fetch 404s**: the filename pattern shifted (NCCI/PFS/AOC do this every few
quarters). Search `data.cms.gov` or the dataset's landing page (`cms.gov/medicare/coding-billing/…`,
`cms.gov/medicare/payment/fee-schedules/physician`) for the current filename, then bump the URL
template in `SOURCES`. Don't change the `ingest` spec unless the file shape changed too.

## State Medicaid exclusion lists (D3)

OpenSanctions aggregates ~30 state Medicaid sanction/termination lists into one normalized feed.
Base: `https://data.opensanctions.org/datasets/latest/us_<st>_med_exclusions/targets.simple.csv`
— `kind: "opensanctions-medicaid"` iterates `states[]` and unions into `state_medicaid_exclusions`.
**CC-BY-NC license** — non-commercial use; for production, source the underlying state lists
directly (each state's OIG/Medicaid Integrity page). ProviderTrust maintains a
[source index](https://www.providertrust.com/exclusion-sources/).

## State Medicaid policy text (D4/D19/D20/D23 adjudicate)

51 state sites, ~7 distinct architectures. `state-policy/<st>.json` holds each state's
`index` URL + `docs[]` list + `fetchVia` + `siteArchitecture`. **These configs go stale** — sites
restructure, doc IDs rotate, monthly releases bump the path. Full per-state table: `STATES.md`.

| Architecture | States (examples) | Fetch |
|---|---|---|
| Per-chapter/per-service PDFs, curl works | TX FL PA IL NC VA WA AZ MA TN IN SC LA KY UT IA NV MS NM WV ID HI NH SD ND AK … (~30) | `curl` direct; URL pattern in config |
| Monolithic single PDF | MI WY | `curl`; chapters are `#page=` anchors |
| DOCX (not PDF) | ME AR MO | `curl`; convert via `libreoffice --convert-to txt` or `pandoc` |
| ASP.NET/DNN postback portal — doc IDs behind `__doPostBack` / dropdown | GA NJ CT WI KS DE DC | browser (`claude-in-chrome`): `form_input` + click; doc IDs rotate |
| HTML-only rule chapters — no PDFs | OH MD OR OK MT RI | save rendered page text, not a PDF |
| WAF / bot-manager blocks curl | NY CA CO MN VT | browser fetch with real UA; curl 403s |
| CPT/AMA license click-through gate | AL WI | index gated; chapter PDFs usually curl direct |

**When a state fetch fails:**
1. The config's `index` URL usually still resolves — open it in Chrome (`mcp__claude-in-chrome__navigate`
   + `get_page_text`); the `siteArchitecture` field tells you what to expect.
2. Postback portals → `form_input` + click, not curl. HTML-rule states → no PDFs; save rendered
   text. WAF states → curl will always 403; don't retry it.
3. If the index URL is dead too: web-search `<state> Medicaid provider manual` — the agency
   **domain** (health.ny.gov, tmhp.com, ahca.myflorida.com, mmis.georgia.gov, hca.wa.gov, …) is
   stable even when paths move. `CRAWL.md` has the full re-discovery procedure.
4. Update `state-policy/<st>.json` in place (new `docs[].url`, bump `lastVerified`).

## Medicaid pharmacy / utilization (data.medicaid.gov — DKAN, not DCAT)

Fetched on demand per detector rather than via the bulk `SOURCES` list. data.medicaid.gov uses a DKAN catalog
(`https://data.medicaid.gov/api/1/…`) — same resolve-by-title pattern, different JSON shape.

| Detector | Dataset | URL hint |
|---|---|---|
| D23 | NADAC (drug acquisition cost) | `download.medicaid.gov/data/nadac-…-<MM-DD-YYYY>.csv`, weekly |
| D16 | State Drug Utilization Data | data.medicaid.gov dataset, annual per state×NDC×quarter |
| — | T-MSIS TAF (claims benchmark) | **DUA-gated via ResDAC** — not public; DQ Atlas (quality metrics) is |

## Payer-supplied data (NOT public — see LOAD-CLAIMS.md)

`claims` / `claim_lines` / `claim_dx` / `members` / `enrollment` / `inpatient_stays` come from the
customer's claims system / 834 feeds, mapped into `corpus.duckdb` per `LOAD-CLAIMS.md`. The
reference layer never substitutes for these.

## Adding a new source

1. Pick `kind`: `csv` (save as-is) · `zip` (unzip then ingest) · `pdf` (→ `policy/*.txt` via
   pdftotext) · `cms-catalog` (resolve from data.json by title) · `mcd-coverage` (zip-in-zip).
2. Append a `SOURCES` entry in `fetch-reference.js` with `name`, `url`/`title`, `out`, `note`, and
   `ingest:{table, glob, opts?, select?}`. Clean header → just `{table, glob}`. Messy header →
   prefer a `preprocess` hook that emits a clean CSV over piling on `read_csv` opts.
3. `node scripts/fetch-reference.js <q> <name> --ingest-only` to test the read_csv opts against
   already-cached files without re-downloading.
4. Record the per-source quirk in `scripts/CLAUDE.md` and the detector mapping here.
