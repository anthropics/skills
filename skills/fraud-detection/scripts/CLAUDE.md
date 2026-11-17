# scripts/ — reference-data layer

## Adding a detector

Drop `scripts/dNN-<slug>.js` exporting `detector = {id, tier, scheme, label, cat, needsJudgment, link?, run(claims, ctx)}`. `registry.js` auto-discovers it; SCHEME/LINKS/NEEDS_JUDGMENT/COVERED_SCHEMES derive automatically (and screen.js writes the roster into `referrals.index.json` meta for the sandboxed workflows). Only manual touches: `source-row.js` ROW_SPECS (if it has a citable reference-table row), `ARCHITECTURE.html` grid, `REFERENCE-DATA.md` table row.

## One storage layer, two read paths

Every reference table lives in **`~/.claude/data/healthcare/fraud-detection/data-cache/reference/<q>/reference.duckdb`**
(override the parent `~/.claude/data/healthcare` with `$CLAUDE_HEALTHCARE_DATA`) as a named table,
with provenance (sourceUrl / release / rows / fetchedAt) in the sibling `reference.meta.json`.
The raw source files (CSVs, unzipped TXTs) **stay on disk** alongside the .duckdb — never deleted.

- **Detectors / source-row / anything cited** → read DuckDB (`duck.js` `query()`). Exact, indexed,
  one row not a 50 MB grep.
- **Discovery / Synthesize agents** → may grep raw files OR `duckdb … -c "DESCRIBE t; SELECT * LIMIT 5"`.
  Same discoverability, far fewer tokens. Raw files are the audit trail; nothing depends on them.

## fetch-reference.js — three ingest paths into the same .duckdb

| kind | source shape | how it lands |
|---|---|---|
| `cms-catalog` | data.cms.gov DCAT entry (clean CSV) | resolve URL from data.json → curl → `ingestCsv()` (iconv-fallback) → table. tmp CSV deleted. |
| `csv` / `zip` / `mcd-coverage` with `ingest:` | clean-header CSV after fetch/unzip | `ingestLocalCsv()` → `CREATE TABLE AS SELECT * FROM read_csv(glob, …opts)`. Raw files kept. |
| `zip` with `preprocess:` | fixed-width or otherwise non-CSV | `preprocess(dir)` runs first (e.g. `fixedWidthToCsv()`), writes a clean headered CSV, then `ingest:` reads it normally. |
| `pdf` | prose policy doc (NCCI manual, MLN article) | curl → `pdftotext -layout` → `policy/<name>.txt`. No DuckDB table. |

**What goes in DuckDB vs filesystem-only:** `reference.duckdb` holds keyed tables detectors join
against (HCPCS, NPI, ICD-10, county, …). Un-keyed prose — policy manuals, MLN PDFs — stays as
`policy/*.{pdf,txt}` on disk; adjudicate prompts cite them by name, nothing queries them by key.

`--ingest-only` skips fetch/unzip and re-runs preprocess+ingest over already-cached files — use it
when a `read_csv` opt or column spec changes.

## Per-source quirks (why the `ingest.opts` differ)

| table | quirk | handled by |
|---|---|---|
| `mue` | row 1 is a multi-line **quoted** AMA copyright cell (Latin-1); row 2 is the header with an embedded newline in `"HCPCS/\nCPT Code"` | `opts: {skip:2, encoding:'latin-1', strict_mode:false, columns:{…}}` + `select` to parse `mai` int from `"2 Date of Service Edit: …"` |
| `ptp` | tab-delimited, 6-row banner header; ships as **4 files**, two `.TXT` two `.txt` | `glob:"*.[tT][xX][tT]"`, `opts:{skip:6, delim:'\t', columns:{…}}`; ingest only on f4 so all parts are present |
| `pfs` | 10-row title/copyright preamble, 32 positional columns | `opts:{skip:10, all_varchar:true}` + `select` projects the ~10 columns detectors use |
| `aoc` | **fixed-width**, no delimiter | `preprocess: fixedWidthToCsv(…)` → `aoc.csv`, then plain `read_csv` |
| `leie`, `article_x_*`, `lcd*`, `ncd_*` | clean header row 1 | plain `read_csv(header=true)` |

If a new source has a clean header, just add `ingest:{table, glob}`. If it's messy, prefer a
`preprocess` that emits a clean CSV over piling more `read_csv` options on — the resulting CSV is
greppable and the ingest stays uniform.

## Identity-keyed tables and the payer overlay

`leie` / `revoked_providers` are identity-keyed (NPI). The payer's own exclusion/credentialing rows
are merged onto `ctx.leie` / `ctx.revoked` at `buildContext()` time from the `*_overlay` tables in
`corpus.duckdb`. **`source-row.js` pulls D3/D10 rows from the overlay-merged ctx Maps, not the
public `reference.duckdb`**, so payer-supplied rows resolve alongside the OIG/CMS lists. Code-keyed
tables (mue/ptp/pfs/aoc/coverage) use real HCPCS/ICD-10 codes and pull straight from DuckDB.

## Scale path

Small corpora run via `loadCorpus → detectors iterate array` in memory. At 250K+ claims, the
detectors run as DuckDB joins instead: claims stay in-table, each `dNN-*.js` issues
`CREATE TABLE findings_dNN AS SELECT … FROM claims JOIN <ref>`, and adjudicate/synthesize agents
query per-NPI on demand instead of receiving the full sweep. The reference tables are already in
place for those joins.
