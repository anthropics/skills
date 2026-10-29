#!/usr/bin/env node
// Fetch the public Medicare/Medicaid reference tables the detectors cite against.
// Plain JS — runs under node (18+) or bun, no build step. Public government data only,
// no PHI. Populates the gitignored reference/<quarter>/ tree, versioned by DOS quarter.
//
//   node scripts/fetch-reference.js            # current quarter (DEFAULT_QUARTER)
//   node scripts/fetch-reference.js 2026q3     # a specific quarter
//
// Network note: cms.gov / oig.hhs.gov are not on the dev sandbox allowlist — run with the
// sandbox disabled. Re-fetch is reproducible; URLs are version-pinned by quarter.

import { execFile } from "node:child_process";
import { existsSync, statSync } from "node:fs";
import { mkdir, writeFile, readFile, rm } from "node:fs/promises";
import path from "node:path";
import { promisify } from "node:util";

import { ddl, query, refDb, refMeta } from "./duck.js";
import { refDir } from "./paths.js";

const run = promisify(execFile);
// data.cms.gov DCAT catalog — fetched once per run, every cms-catalog source resolves from it.
const CMS_CATALOG_URL = "https://data.cms.gov/data.json";
let _cmsCatalog = null;
async function cmsCatalog() {
  if (_cmsCatalog) return _cmsCatalog;
  const r = await fetch(CMS_CATALOG_URL);
  if (!r.ok) throw new Error(`catalog fetch ${r.status}`);
  _cmsCatalog = await r.json();
  return _cmsCatalog;
}
const DEFAULT_QUARTER = "2026q3";

/**
 * Each source: where it goes under reference/<quarter>/, the URL, and how to land it.
 * kind: "csv" = save as-is · "zip" = save + unzip · "data-api" = CMS JSON API (sample only) ·
 *       "cms-catalog" = resolve bulk CSV from data.cms.gov/data.json → Parquet via DuckDB.
 * Quarter-specific URLs interpolate {q} (e.g. "2026q3") and {qDash} (e.g. "2026-q3").
 */
const SOURCES = (q) => {
  const qDash = q.replace(/q/, "-q"); // 2026q3 -> 2026-q3
  return [
    {
      name: "leie",
      kind: "csv",
      out: "leie/UPDATED.csv",
      url: "https://oig.hhs.gov/exclusions/downloadables/UPDATED.csv",
      note: "OIG exclusions — refreshed monthly; the latest full file (not quarter-pinned).",
      ingest: { table: "leie", glob: "UPDATED.csv" },
    },
    {
      name: "state-medicaid-exclusions",
      kind: "opensanctions-medicaid",
      out: "state-medicaid-exclusions",
      // one CSV per state at data.opensanctions.org/datasets/latest/us_<st>_med_exclusions/targets.simple.csv
      states: [
        "al",
        "az",
        "ca",
        "co",
        "de",
        "ia",
        "in",
        "ks",
        "ky",
        "la",
        "ma",
        "md",
        "me",
        "mi",
        "mn",
        "mo",
        "ms",
        "mt",
        "nd",
        "ne",
        "nh",
        "nv",
        "ny",
        "pa",
        "sc",
        "tn",
        "tx",
        "wa",
        "wv",
        "wy",
      ],
      note: "D3 — state Medicaid exclusion lists beyond LEIE. CC-BY-NC (OpenSanctions) — non-commercial; for production source state OIG lists directly.",
      ingest: {
        table: "state_medicaid_exclusions",
        glob: "us_*.csv",
        opts: { filename: true },
        // targets.simple.csv columns: id, schema, name, aliases, birth_date, countries, addresses,
        // identifiers (semicolon-separated; NPI is sometimes one), sanctions, dataset, first_seen,
        // last_seen, last_change. Extract the 10-digit NPI from identifiers; state from the filename
        // (dataset column is a human title, not the slug).
        select:
          "regexp_extract(identifiers, '\\b[0-9]{10}\\b') AS npi, " +
          "upper(regexp_extract(filename, 'us_([a-z]{2})_med_exclusions', 1)) AS state, " +
          "name, dataset, sanctions, first_seen",
      },
    },
    {
      name: "ncci-mue-practitioner",
      kind: "zip",
      out: "ncci/mue-practitioner",
      url: `https://www.cms.gov/files/zip/medicare-ncci-${qDash}-practitioner-services-mue-table.zip`,
      ingest: {
        table: "mue",
        glob: "*.csv",
        // row 1 is a multi-line quoted AMA copyright cell (Latin-1); row 2 is the header (with an
        // embedded newline in "HCPCS/\nCPT Code"). Skip both and name columns explicitly.
        opts: {
          skip: 2,
          header: false,
          delim: ",",
          quote: '"',
          encoding: "latin-1",
          strict_mode: false,
          columns: { hcpcs: "VARCHAR", mue: "INTEGER", mai_raw: "VARCHAR", rationale: "VARCHAR" },
        },
        // mai is "2 Date of Service Edit: Policy" → keep the leading integer
        select: "hcpcs, mue, CAST(regexp_extract(mai_raw, '^[0-9]+') AS INTEGER) AS mai, rationale",
      },
    },
    {
      name: "ncci-mln-modifier-59",
      kind: "pdf",
      out: "policy/mln1783722.pdf",
      url: "https://www.cms.gov/files/document/mln1783722-proper-use-modifiers-59-xe-xp-xs-xu.pdf",
      note: "MLN1783722 — modifier 59/X{E,P,S,U} distinct-service criteria. D2 adjudication cites it.",
    },
    {
      name: "ncci-policy-manual-ch1",
      kind: "pdf",
      out: "policy/ncci-policy-ch1.pdf",
      url: "https://www.cms.gov/files/document/chapter1generalcorrectcodingpoliciesfinal11.pdf",
      note: "NCCI Policy Manual Ch.1 — General Correct Coding Policies (modifier-59 authority).",
    },
    {
      name: "ncci-ptp-practitioner-changes",
      kind: "zip",
      out: "ncci/ptp-practitioner-changes",
      url: `https://www.cms.gov/files/zip/medicare-ncci-${q}-practitioner-quarterly-additions-deletions-revisions-ptp.zip`,
      note: "PTP quarterly DELTA (additions/deletions/revisions). Full base table below.",
    },
    // Full NCCI PTP base table (practitioner) — 4 files. CPT® codes are © AMA; CMS distributes under
    // license for Medicare/Medicaid program-integrity use. The /files/zip/ path serves the ZIP directly (the /license/ama?file= wrapper
    // returns the acceptance page). The version code (v322r0 = 2026q3) is quarter-specific — re-probe
    // the NCCI PTP edits page per quarter and bump it.
    ...[1, 2, 3, 4].map((n) => ({
      name: `ncci-ptp-practitioner-base-f${n}`,
      kind: "zip",
      out: "ncci/ptp-practitioner",
      url: `https://www.cms.gov/files/zip/medicare-ncci-${q}-practitioner-ptp-edits-ccipra-v322r0-f${n}.zip`,
      note: "Full PTP base table (CPT® © AMA; CMS-distributed for Medicare/Medicaid program-integrity use).",
      // Only ingest after the LAST file lands so the table is built from all four parts at once.
      ...(n === 4 && {
        ingest: {
          table: "ptp",
          // f1/f2 ship as .TXT, f3/f4 as .txt — match both
          glob: "*.[tT][xX][tT]",
          opts: {
            skip: 6,
            header: false,
            delim: "\t",
            columns: {
              column1: "VARCHAR",
              column2: "VARCHAR",
              in_existence: "VARCHAR",
              effective: "VARCHAR",
              deletion: "VARCHAR",
              mod: "VARCHAR",
              rationale: "VARCHAR",
            },
          },
        },
      }),
    })),
    // ── Medicaid NCCI (separate program — D1/D2/D11 route by ctx.lob) ────────────────────
    // Medicaid publishes its own MUE + PTP edits at /ncci-medicaid/medicaid-ncci-edit-files. Same
    // AMA-preamble/Latin-1 quirks, but: MUE has NO MAI column (Medicaid MUEs are all DOS edits),
    // and PTP ships as ONE zip with one big tab-delimited .txt (active = empty deletion date, vs
    // Medicare's "*"). Re-probe that page per quarter (filename pattern shifted q2→q3).
    {
      name: "ncci-mue-medicaid-practitioner",
      kind: "zip",
      out: "ncci/mue-medicaid-practitioner",
      url: `https://www.cms.gov/files/zip/medicaid-ncci-${qDash}-mue-edits-practitioner-services.zip`,
      ingest: {
        table: "mue_medicaid",
        glob: "*.txt",
        opts: {
          skip: 2,
          header: false,
          delim: "\t",
          quote: '"',
          encoding: "latin-1",
          strict_mode: false,
          columns: { hcpcs: "VARCHAR", mue: "INTEGER", rationale: "VARCHAR" },
        },
        select: "hcpcs, mue, NULL::INTEGER AS mai, rationale",
      },
    },
    {
      name: "ncci-ptp-medicaid-practitioner",
      kind: "zip",
      out: "ncci/ptp-medicaid-practitioner",
      url: `https://www.cms.gov/files/zip/medicaid-ncci-${qDash}-ptp-edits-practitioner-services.zip`,
      ingest: {
        table: "ptp_medicaid",
        glob: "*.txt",
        opts: {
          skip: 3,
          header: false,
          delim: "\t",
          encoding: "latin-1",
          strict_mode: false,
          columns: {
            column1: "VARCHAR",
            column2: "VARCHAR",
            effective: "VARCHAR",
            deletion: "VARCHAR",
            mod: "VARCHAR",
            rationale: "VARCHAR",
          },
        },
      },
    },
    // ── data.cms.gov-hosted sets via the DCAT catalog (kind: "cms-catalog") ────────────────
    // Resolved from data.json by title regex → latest bulk CSV → DuckDB → Parquet. URLs never
    // rot (catalog always carries the current release path). See research/cms-data-catalog.md.
    //
    // Benchmarks (annual) — peer-cohort distributions for the statistical detectors.
    {
      name: "partb-by-provider",
      kind: "cms-catalog",
      title: /^Medicare Physician & Other Practitioners - by Provider$/,
      types: { Rndrng_NPI: "VARCHAR" },
      note: "D7 cohort population (1.3M rows). Replaces the 5k data-api sample.",
    },
    {
      name: "partb-by-provider-service",
      kind: "cms-catalog",
      title: /^Medicare Physician & Other Practitioners - by Provider and Service$/,
      out: "benchmarks/partb-by-provider-service.parquet",
      note: "D7 procedure-level outliers (per-HCPCS volume per provider).",
    },
    {
      name: "partb-by-geography",
      kind: "cms-catalog",
      title: /^Medicare Physician & Other Practitioners - by Geography and Service$/,
      out: "benchmarks/partb-by-geography.parquet",
      note: "State/CBSA-level HCPCS norms — geographic peer baselines.",
    },
    {
      name: "dmepos-by-supplier",
      kind: "cms-catalog",
      title: /^Medicare Durable Medical Equipment, Devices & Supplies - by Supplier$/,
      out: "benchmarks/dmepos-by-supplier.parquet",
      note: "D15 DME supplier outliers (highest-FWA category).",
    },
    {
      name: "dmepos-by-referrer",
      kind: "cms-catalog",
      title: /^Medicare Durable Medical Equipment, Devices & Supplies - by Referring Provider$/,
      out: "benchmarks/dmepos-by-referrer.parquet",
      note: "D15 DME referrer outliers.",
    },
    {
      name: "partd-by-provider",
      kind: "cms-catalog",
      title: /^Medicare Part D Prescribers - by Provider$/,
      out: "benchmarks/partd-by-provider.parquet",
      note: "D16 prescribing outliers (opioid/brand-ratio vs specialty cohort).",
    },
    {
      name: "market-saturation-county",
      kind: "cms-catalog",
      title: /^Market Saturation & Utilization State-County$/,
      out: "benchmarks/market-saturation-county.parquet",
      note: "D17 — CMS's own program-integrity dataset (provider density vs beneficiary need).",
    },
    {
      name: "psps",
      kind: "cms-catalog",
      title: /^Physician\/Supplier Procedure Summary$/,
      out: "benchmarks/psps.parquet",
      note: "National HCPCS volume/allowed-amount aggregates — D7 baselines.",
    },
    // Enrollment / eligibility (sub-annual) — provider-status checks. NPI/date columns are pinned
    // to VARCHAR so detector + gate code (written against string-valued JSON) keeps its contract.
    {
      name: "order-and-referring",
      kind: "cms-catalog",
      title: /^Order and Referring$/,
      types: { NPI: "VARCHAR" },
      note: "D9 ineligible-orderer. Full file (was 5k sample).",
    },
    {
      name: "revoked-providers",
      kind: "cms-catalog",
      title: /^Revoked Medicare Providers and Suppliers$/,
      types: {
        NPI: "VARCHAR",
        REVOCATION_EFCTV_DT: "VARCHAR",
        REENROLLMENT_BAR_EXPRTN_DT: "VARCHAR",
      },
      note: "D10 revoked-provider billing. Full file (was 5k sample).",
    },
    {
      name: "opt-out",
      kind: "cms-catalog",
      title: /^Opt Out Affidavits$/,
      types: {
        npi: "VARCHAR",
        "Optout Effective Date": "VARCHAR",
        "Optout End Date": "VARCHAR",
      },
      note: "D14 — opted-out provider billing Medicare = 100% improper.",
    },
    {
      name: "ffs-enrollment",
      kind: "cms-catalog",
      title: /^Medicare Fee-For-Service\s+Public Provider Enrollment$/,
      types: { NPI: "VARCHAR" },
      note: "Full PECOS enrollment status/specialty — replaces NPPES for Medicare-enrolled checks.",
    },
    {
      name: "taxonomy-crosswalk",
      kind: "cms-catalog",
      title: /^Medicare Provider and Supplier Taxonomy Crosswalk$/,
      out: "enrollment/taxonomy-crosswalk.parquet",
      note: "NPPES taxonomy → Medicare specialty code map — fixes D7 cohort specialty mismatch.",
    },
    // Ownership (monthly/quarterly) — common-ownership ring detection (D18).
    ...["Home Health Agency", "Hospice", "Skilled Nursing Facility", "Hospital"].map((f) => ({
      name: `owners-${f.toLowerCase().replace(/\s+/g, "-")}`,
      kind: "cms-catalog",
      title: new RegExp(`^${f} All Owners$`),
      out: `ownership/${f.toLowerCase().replace(/\s+/g, "-")}-owners.parquet`,
      note: "D18 ownership-ring detection.",
    })),
    {
      name: "ncci-aoc",
      kind: "zip",
      out: "ncci/add-on-codes",
      url: "https://www.cms.gov/files/zip/add-code-edits-medicare-effective-06012026.zip",
      note: "D3 orphan add-on (Type 1). Date-suffixed filename — re-probe the AOC page per quarter.",
      // Fixed-width source — preprocess to a clean CSV first so ingest is plain read_csv (no
      // SUBSTRING-in-SQL). Positions: 1=type · 2-6=add-on · 14-18=primary · 26-32=effective(YYYYDDD)
      // · 40+=description.
      preprocess: async (dir) => {
        const cols = [
          ["type", 0, 1],
          ["addon", 1, 6],
          ["primary_code", 13, 18],
          ["effective", 25, 32],
          ["description", 39],
        ];
        await fixedWidthToCsv(dir, "*.txt", "aoc.csv", cols);
      },
      ingest: { table: "aoc", glob: "aoc.csv" },
    },
    {
      name: "pfs-rvu",
      kind: "zip",
      out: "pfs/rvu26a",
      url: "https://www.cms.gov/files/zip/rvu26a-updated-12-29-2025.zip",
      note: "Exposure $ for PFS status-A codes. 'updated-MM-DD-YYYY' suffix is unpredictable — re-probe rvu<yy><q> page per release.",
      ingest: {
        table: "pfs",
        glob: "PPRRVU*_nonQPP.csv",
        opts: { skip: 10, header: false, all_varchar: true },
        // PPRRVU has 32 positional columns; keep only what detectors need (HCPCS row 0, MOD 1,
        // DESCRIPTION 2, STATUS 3, WORK_RVU 5, NONFAC_PE 6, FAC_PE 8, MP 10, GLOB_DAYS 14, CF 25).
        select:
          "column00 AS hcpcs, column01 AS mod, column02 AS description, column03 AS status, " +
          "TRY_CAST(column05 AS DOUBLE) AS work_rvu, TRY_CAST(column06 AS DOUBLE) AS nonfac_pe_rvu, " +
          "TRY_CAST(column08 AS DOUBLE) AS fac_pe_rvu, TRY_CAST(column10 AS DOUBLE) AS mp_rvu, " +
          "column14 AS glob_days, TRY_CAST(column25 AS DOUBLE) AS conv_factor",
      },
    },
    {
      name: "coverage-articles",
      kind: "mcd-coverage",
      out: "coverage",
      url: "https://downloads.cms.gov/medicare-coverage-database/downloads/exports/current_article.zip",
      inner: "current_article_csv.zip",
      files: [
        "article_x_hcpc_code.csv",
        "article_x_icd10_covered.csv",
        "article_x_icd10_noncovered.csv",
      ],
      note: "D4 medical-necessity — HCPCS↔covered/non-covered ICD-10 from MCD Billing & Coding Articles.",
      ingest: { table: null, perFile: true }, // one table per file (clean headers)
    },
    {
      name: "coverage-lcds",
      kind: "mcd-coverage",
      out: "coverage",
      url: "https://downloads.cms.gov/medicare-coverage-database/downloads/exports/all_lcd.zip",
      inner: "all_lcd_csv.zip",
      // LCDs do NOT carry ICD-10 covered/non-covered mappings (that's Articles only). lcd.csv is the
      // full policy text per LCD (51MB) — greppable for discovery; lcd_x_hcpc_code.csv is HCPCS→LCD.
      files: [
        "lcd.csv",
        "lcd_x_hcpc_code.csv",
        "lcd_x_contractor.csv",
        "lcd_related_ncd_documents.csv",
      ],
      note: "D4 context — which LCDs govern a HCPCS, plus full LCD text for discovery agents.",
      ingest: { table: null, perFile: true },
    },
    {
      name: "coverage-ncds",
      kind: "mcd-coverage",
      out: "coverage",
      url: "https://downloads.cms.gov/medicare-coverage-database/downloads/exports/ncd.zip",
      inner: "ncd_csv.zip",
      files: ["ncd_trkg.csv", "ncd_bnft_ctgry_ref.csv", "ncd_trkg_bnft_xref.csv"],
      note: "NCD index (national determinations). HCPCS/ICD-10 mappings live in MAC Articles, not NCDs.",
      ingest: { table: null, perFile: true },
    },
  ];
};

const UA = "fraud-detection-reference-fetch/1.0";

// curl streams to disk (no in-memory buffer), retries transient failures, and resumes partials
// (-C -). Node fetch().arrayBuffer() would hold multi-GB CSVs in memory before writing.
async function fetchToFile(url, dest) {
  await mkdir(path.dirname(dest), { recursive: true });
  await run("curl", ["-fsSL", "--retry", "3", "-C", "-", "-A", UA, "-o", dest, url]);
  return statSync(dest).size;
}

// reference.meta.json — { <table>: {title, release, sourceUrl, rows, bytes, encoding?, fetchedAt} }
async function loadMeta(quarter) {
  const p = refMeta(quarter);
  if (!existsSync(p)) return {};
  return JSON.parse(await readFile(p, "utf8"));
}
async function saveMeta(quarter, meta) {
  await writeFile(refMeta(quarter), JSON.stringify(meta, null, 2));
}

// CREATE OR REPLACE TABLE <name> from a CSV. Tries UTF-8 first; on a unicode error, transcodes
// the file in place via iconv (CMS enrollment/ownership exports are Windows-1252/Latin-1 — a safe
// assumption for US-gov CSVs; would NOT generalize to arbitrary international data) and retries.
// `types` is an optional {column: "DUCKDB_TYPE"} map — used to pin identifier/date columns to
// VARCHAR so downstream detector code (written against string-valued JSON) keeps its contract.
async function ingestCsv(tmp, table, db, types) {
  const lit = (s) => String(s).replace(/'/g, "''");
  const typeOpt = types
    ? `, types={${Object.entries(types)
        .map(([c, t]) => `'${lit(c)}': '${lit(t)}'`)
        .join(", ")}}`
    : "";
  const sql = `CREATE OR REPLACE TABLE ${table} AS SELECT * FROM read_csv_auto('${lit(tmp)}', header=true, sample_size=-1${typeOpt})`;
  try {
    await ddl(sql, { db });
    return null;
  } catch (e) {
    if (!/Invalid unicode|not utf-8/i.test(String(e))) throw e;
    await run("sh", [
      "-c",
      `iconv -f latin1 -t UTF-8 '${lit(tmp)}' > '${lit(tmp)}.u8' && mv '${lit(tmp)}.u8' '${lit(tmp)}'`,
    ]);
    await ddl(sql, { db });
    return "latin1";
  }
}

// Convert a fixed-width text file to a headered CSV so it can ingest via plain read_csv. `cols` is
// [[name, start, end?], ...] (0-based, end-exclusive; omit end for "to EOL").
async function fixedWidthToCsv(dir, glob, outName, cols) {
  const { glob: g } = await import("node:fs/promises");
  const files = [];
  for await (const f of g(path.join(dir, glob))) files.push(f);
  const cell = (s) => (/[",\n]/.test(s) ? `"${s.replace(/"/g, '""')}"` : s);
  const lines = [cols.map((c) => c[0]).join(",")];
  for (const f of files) {
    for (const ln of (await readFile(f, "utf8")).split(/\r?\n/)) {
      if (!ln.trim()) continue;
      lines.push(cols.map(([, a, b]) => cell(ln.slice(a, b).trim())).join(","));
    }
  }
  await writeFile(path.join(dir, outName), lines.join("\n") + "\n");
}

// Ingest already-unzipped local CSV/TXT into reference.duckdb as a named table and record provenance
// in reference.meta.json. `spec` carries: table, glob (relative to dir), opts (DuckDB read_csv opts),
// optional select (post-read projection/cleanup). With perFile, each file in `files` becomes its own
// table named after the file stem (clean-header MCD exports).
async function ingestLocalCsv(dir, spec, src, quarter) {
  const db = refDb(quarter);
  const meta = await loadMeta(quarter);
  const targets = spec.perFile
    ? src.files.map((f) => ({ table: f.replace(/\.csv$/, ""), glob: f, opts: {} }))
    : [{ table: spec.table, glob: spec.glob, opts: spec.opts || {}, select: spec.select }];
  const out = [];
  for (const t of targets) {
    const o = t.opts;
    const csvOpts = [
      `'${path.join(dir, t.glob).replace(/'/g, "''")}'`,
      "header=" + (o.header === false ? "false" : "true"),
      o.skip ? `skip=${o.skip}` : null,
      o.delim ? `delim='${o.delim}'` : null,
      o.quote ? `quote='${o.quote.replace(/'/g, "''")}'` : null,
      o.encoding ? `encoding='${o.encoding}'` : null,
      o.strict_mode === false ? "strict_mode=false" : null,
      o.all_varchar ? "all_varchar=true" : null,
      o.filename ? "filename=true" : null,
      o.columns
        ? `columns={${Object.entries(o.columns)
            .map(([k, v]) => `'${k}': '${v}'`)
            .join(", ")}}`
        : null,
      "ignore_errors=true",
      "union_by_name=true",
    ]
      .filter(Boolean)
      .join(", ");
    const sel = t.select || "*";
    await ddl(`CREATE OR REPLACE TABLE ${t.table} AS SELECT ${sel} FROM read_csv(${csvOpts})`, {
      db,
    });
    const [{ n }] = await query(`SELECT count(*) AS n FROM ${t.table}`, {}, { db });
    meta[t.table] = {
      title: src.name,
      release: quarter,
      sourceUrl: src.url,
      rows: Number(n),
      fetchedAt: new Date().toISOString(),
    };
    out.push(`${t.table}:${Number(n).toLocaleString()}`);
  }
  await saveMeta(quarter, meta);
  return out.join(" ");
}

async function fetchSource(src, quarterDir, quarter) {
  const dest = src.out ? path.join(quarterDir, src.out) : null;
  // --ingest-only: skip the fetch/unzip and just (re-)ingest already-present files into DuckDB.
  // Useful when files are cached but the table schema or read_csv opts changed.
  if (process.argv.includes("--ingest-only")) {
    if (!src.ingest) return "no ingest";
    const dir = src.kind === "csv" ? path.dirname(dest) : dest;
    if (src.preprocess) await src.preprocess(dir);
    return await ingestLocalCsv(dir, src.ingest, src, quarter);
  }
  if (src.kind === "csv") {
    const n = await fetchToFile(src.url, dest);
    const ing = src.ingest
      ? await ingestLocalCsv(path.dirname(dest), src.ingest, src, quarter)
      : "";
    return `${(n / 1e6).toFixed(1)} MB${ing ? ` · ${ing}` : ""}`;
  }
  if (src.kind === "zip") {
    const zip = `${dest}.zip`;
    await fetchToFile(src.url, zip);
    await mkdir(dest, { recursive: true });
    await run("unzip", ["-o", "-q", zip, "-d", dest]); // requires `unzip` on PATH
    await rm(zip);
    if (src.preprocess) await src.preprocess(dest);
    const ing = src.ingest ? await ingestLocalCsv(dest, src.ingest, src, quarter) : "";
    return `unzipped${ing ? ` · ${ing}` : ""}`;
  }
  if (src.kind === "data-api") {
    const url = `https://data.cms.gov/data-api/v1/dataset/${src.id}/data?size=${src.size}`;
    const n = await fetchToFile(url, dest);
    return `${(n / 1e3).toFixed(0)} KB`;
  }
  if (src.kind === "cms-catalog") {
    // Resolve the bulk CSV from the DCAT catalog (no hardcoded GUIDs that rot per release),
    // curl it to a tmp file, ingest into reference.duckdb as a named table (iconv-fallback for
    // Latin-1 exports), record provenance in reference.meta.json, then drop the tmp.
    const cat = await cmsCatalog();
    const ds = cat.dataset.find((d) => src.title.test(d.title));
    if (!ds) throw new Error(`no catalog match for ${src.title}`);
    const csvs = (ds.distribution || []).filter((d) => d.format === "CSV" && d.downloadURL);
    const dist =
      src.pick && src.pick.year
        ? csvs.find((d) => (d.title || "").includes(String(src.pick.year)))
        : csvs[0]; // catalog lists latest first
    if (!dist) throw new Error(`no CSV distribution for "${ds.title}"`);
    const table = src.table || src.name.replace(/-/g, "_");
    const meta = await loadMeta(quarter);
    const typesKey = JSON.stringify(src.types || null);
    if (meta[table]?.release === dist.title && (meta[table]?.typesKey ?? "null") === typesKey) {
      return `${table} current (${meta[table].rows.toLocaleString()} rows, skipped)`;
    }
    const db = refDb(quarter);
    await mkdir(path.dirname(db), { recursive: true });
    const tmp = path.join(quarterDir, `.${table}.tmp.csv`);
    const bytes = await fetchToFile(dist.downloadURL, tmp);
    const encoding = await ingestCsv(tmp, table, db, src.types);
    const [{ n }] = await query(`SELECT count(*) AS n FROM ${table}`, {}, { db });
    await rm(tmp);
    meta[table] = {
      title: ds.title,
      release: dist.title,
      sourceUrl: dist.downloadURL,
      rows: Number(n),
      bytes,
      typesKey,
      ...(encoding && { encoding }),
      fetchedAt: new Date().toISOString(),
    };
    await saveMeta(quarter, meta);
    return `${table}: ${Number(n).toLocaleString()} rows (${(bytes / 1e6).toFixed(0)} MB CSV${encoding ? `, ${encoding}` : ""})`;
  }
  if (src.kind === "pdf") {
    // Prose policy docs (NCCI manual, MLN articles). No join key → no DuckDB table; the PDF and a
    // pdftotext-extracted .txt sit under reference/<q>/policy/ for grep + adjudicate-prompt citation.
    // CMS PDFs are born-digital so pdftotext is sufficient (no OCR). Requires `pdftotext` (poppler).
    const bytes = await fetchToFile(src.url, dest);
    const txt = dest.replace(/\.pdf$/i, ".txt");
    await run("pdftotext", ["-layout", "-enc", "UTF-8", dest, txt]);
    const meta = await loadMeta(quarter);
    meta[src.name] = {
      title: src.note || src.name,
      sourceUrl: src.url,
      bytes,
      txtBytes: statSync(txt).size,
      fetchedAt: new Date().toISOString(),
    };
    await saveMeta(quarter, meta);
    return `${(bytes / 1e3).toFixed(0)} KB pdf · ${(statSync(txt).size / 1e3).toFixed(0)} KB text`;
  }
  if (src.kind === "opensanctions-medicaid") {
    // OpenSanctions aggregates per-state Medicaid exclusion lists into a uniform CSV. One file per
    // state → us_<st>_med_exclusions.csv, then ingestLocalCsv unions them via the glob.
    await mkdir(dest, { recursive: true });
    const failed = [];
    for (const st of src.states) {
      const slug = `us_${st}_med_exclusions`;
      const url = `https://data.opensanctions.org/datasets/latest/${slug}/targets.simple.csv`;
      try {
        await fetchToFile(url, path.join(dest, `${slug}.csv`));
      } catch (e) {
        failed.push(st);
      }
    }
    const ing = await ingestLocalCsv(
      dest,
      src.ingest,
      { ...src, url: "data.opensanctions.org" },
      quarter,
    );
    return `${src.states.length - failed.length}/${src.states.length} states${failed.length ? ` (404: ${failed.join(",")})` : ""} · ${ing}`;
  }
  if (src.kind === "mcd-coverage") {
    // MCD exports are zip-in-a-zip: <name>.zip → <inner>_csv.zip → CSVs. Multiple mcd-coverage
    // sources share dest=coverage/, so name the outer tmp by src.name to avoid collisions.
    const outer = `${dest}.${src.name}.outer.zip`;
    await fetchToFile(src.url, outer);
    await mkdir(dest, { recursive: true });
    await run("unzip", ["-o", "-q", outer, src.inner, "-d", dest]);
    await run("unzip", ["-o", "-q", path.join(dest, src.inner), ...src.files, "-d", dest]);
    await rm(outer);
    await rm(path.join(dest, src.inner));
    const ing = src.ingest ? await ingestLocalCsv(dest, src.ingest, src, quarter) : "";
    return `${src.files.length} files${ing ? ` · ${ing}` : ""}`;
  }
  throw new Error(`unknown kind: ${src.kind}`);
}

async function main() {
  const quarter = (process.argv[2] || DEFAULT_QUARTER).toLowerCase();
  if (!/^\d{4}q[1-4]$/.test(quarter)) {
    console.error(`Bad quarter "${quarter}" — expected e.g. 2026q3`);
    process.exit(1);
  }
  const only = process.argv.slice(3).filter((a) => !a.startsWith("-"));
  const quarterDir = refDir(quarter);
  console.log(`Fetching reference tables → ${quarterDir}/`);
  let sources = SOURCES(quarter);
  if (only.length) sources = sources.filter((s) => only.includes(s.name));
  const results = [];
  for (const src of sources) {
    try {
      const detail = await fetchSource(src, quarterDir, quarter);
      console.log(`  ✓ ${src.name} (${detail})`);
      results.push({ name: src.name, ok: true });
    } catch (err) {
      console.error(`  ✗ ${src.name}: ${err.message}`);
      results.push({ name: src.name, ok: false, err: err.message });
    }
  }
  const ok = results.filter((r) => r.ok).length;
  console.log(`\n${ok}/${results.length} sources fetched into ${quarterDir}/`);
  if (ok < results.length) {
    console.log("Some sources failed — check the URL/quarter (CMS file names shift) and retry.");
    process.exit(1);
  }
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
