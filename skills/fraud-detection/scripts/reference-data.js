// Loaders for the public reference tables fetched into reference/<quarter>/.
// Plain JS (node/bun), no deps. Detectors cite against these; everything is keyed/versioned
// by date-of-service quarter where the source is quarterly. Files are small enough to hold in
// memory (MUE ~15k rows, LEIE ~83k rows). Run scripts/fetch-reference.js first.

import { readFileSync, existsSync, readdirSync } from "node:fs";
import path from "node:path";

import { precomputeCohorts } from "./d07-outlier.js";
import { precomputeDmeCohorts } from "./d15-dme-outlier.js";
import { precomputePartdLookups } from "./d16-prescribing-outlier.js";
import { precomputeSaturation } from "./d17-market-saturation.js";
import { precomputeOwnerIndex } from "./d18-ownership-ring.js";
import { query, refDb, refDir } from "./duck.js";
import { loadNppes } from "./enrichment.js";

/**
 * Build the full detector context for a quarter + claims corpus. Single source of truth so every
 * caller (screen.js, eval/run.js, the workflow) loads the SAME reference/enrichment tables — keeps
 * detectors from silently going dark when one caller forgets a loader. PTP/coverage are scoped to the
 * HCPCS present in the corpus (those tables are large).
 *
 * `corpusDb` (path to corpus.duckdb) is the SOLE source for payer feeds + overlay tables — every
 * ctx.* a detector reads traces to ONE named table (see ctx.sources). `lob` (medicare|medicaid)
 * routes the program-specific NCCI tables and state-exclusion lookups; it is a property of the
 * RUN, not the claim row — a payer screens one line of business at a time.
 */
export async function buildContext(quarter, claims, corpusDb, lob = "medicare") {
  const codes = new Set();
  for (const c of claims) for (const l of c.lines || []) if (l.hcpcs) codes.add(l.hcpcs);
  const mue = await loadMUE(quarter);
  const ctx = {
    quarter,
    lob,
    mue,
    nonPayable: {
      medicare: nonPayableCodes(mue.medicare),
      medicaid: nonPayableCodes(mue.medicaid),
    },
    aoc: loadAOC(quarter),
    pfs: loadPFS(quarter),
    leie: loadLEIE(quarter),
    stateExclusions: await loadStateExclusions(quarter),
    revoked: await loadRevoked(quarter),
    orderReferring: await loadOrderReferring(quarter),
    optOut: await loadOptOut(quarter),
    ptp: await loadPTP(quarter, codes),
    coverage: loadCoverage(quarter, codes),
    // HCPCS → governing LCD ids (lcd_x_hcpc_code), scoped to corpus codes. D4 attaches as
    // evidence.lcdIds; the adjudicate stage reads lcd.indication for these to weigh the prose.
    lcdByHcpcs: await loadLcdByHcpcs(quarter, codes),
    // D7 reads precomputed cohort stats (DuckDB MEDIAN/MAD over the full 1.3M-row table) instead
    // of loading partb_by_provider into memory.
    cohorts: await precomputeCohorts(quarter, claims),
    partbByProvider: null,
    members: new Map(), // beneId → {dob, dod, sex, zip}
    enrollment: new Map(), // beneId → [{planId, program, enrolledState, effectiveFrom, effectiveTo}]
    nppes: loadNppes(),
  };
  // Read members/enrollment + overlay tables from corpus.duckdb into the merge shape.
  const overlay = await loadOverlayFromDb(corpusDb);
  // overlay.nppes merges early so precomputeSaturation (which reads ctx.nppes for state) sees it
  mergeOverlay.nppes(ctx, overlay?.nppes);
  // tier-2 statistical/network precomputes (DuckDB-backed) so detector.run() stays synchronous
  const npis = new Set();
  for (const c of claims) {
    if (c.billingNpi) npis.add(c.billingNpi);
    if (c.renderingNpi) npis.add(c.renderingNpi);
  }
  ctx.dmeCohorts = await precomputeDmeCohorts(quarter, claims);
  const partd = await precomputePartdLookups(quarter, claims);
  ctx.partdRows = partd.rows;
  ctx.partdCohorts = partd.cohorts;
  ctx.saturation = await precomputeSaturation(quarter, claims, ctx.nppes);
  ctx.ownerIndex = await precomputeOwnerIndex(quarter, npis);
  // Payer-supplied feeds — not public CMS data; come from the payer's own claims/834 systems.
  ctx.inpatientStays = new Map();
  for (const k of Object.keys(mergeOverlay)) mergeOverlay[k](ctx, overlay[k]);
  ctx.sources = buildSources(corpusDb);
  return ctx;
}

/** First enrollment span for `beneId` covering `dos` whose program matches the run's lob, else null. */
export function enrollmentAt(ctx, beneId, dos) {
  for (const s of ctx.enrollment.get(beneId) || [])
    if (s.program === ctx.lob && dos >= s.effectiveFrom && dos <= (s.effectiveTo || "9999-12-31"))
      return s;
  return null;
}

// One merge helper per ctx field — the SINGLE code path for "merge a row into ctx.X", called for
// both the JSON _identity.json overlay (back-compat) and the corpus.duckdb-loaded overlay.
const mergeOverlay = {
  nppes: (ctx, rows) => {
    for (const r of rows || []) ctx.nppes.set(r.npi, r);
  },
  leie: (ctx, rows) => {
    for (const r of rows || [])
      ctx.leie.byNpi.set(r.npi, { exclType: r.exclType, exclDate: r.exclDate });
  },
  stateExclusions: (ctx, rows) => {
    for (const r of rows || [])
      ctx.stateExclusions.set(r.npi, {
        state: r.state,
        name: r.name,
        sanctionDate: r.sanctionDate,
      });
  },
  revoked: (ctx, rows) => {
    if (rows && rows.length) ctx.revoked = [...ctx.revoked, ...rows];
  },
  members: (ctx, rows) => {
    for (const r of rows || []) ctx.members.set(r.beneId, r);
  },
  enrollment: (ctx, rows) => {
    for (const r of rows || []) {
      const a = ctx.enrollment.get(r.beneId) || [];
      a.push(r);
      ctx.enrollment.set(r.beneId, a);
    }
  },
  inpatientStays: (ctx, rows) => {
    for (const r of rows || []) ctx.inpatientStays.set(r.beneId, r);
  },
  // tier-2 benchmark overlays (D15–D18) so synthetic 9-prefix NPIs can appear in cohort/benchmark
  // tables they would never match in real DuckDB. Merged AFTER precompute so overlay wins.
  dmeCohorts: (ctx, rows) => {
    for (const r of rows || [])
      ctx.dmeCohorts.set(r.specialty, { n: r.n, median: r.median, mad: r.mad });
  },
  partdRows: (ctx, rows) => {
    for (const r of rows || []) ctx.partdRows.set(r.npi, r);
  },
  partdCohorts: (ctx, rows) => {
    for (const r of rows || [])
      ctx.partdCohorts.set(r.specialty, { n: r.n, median: r.median, mad: r.mad });
  },
  saturation: (ctx, rows) => {
    for (const r of rows || []) ctx.saturation.set(`${r.state}|${r.type_of_service}`, r);
  },
  ownerIndex: (ctx, rows) => {
    for (const r of rows || [])
      ctx.ownerIndex.set(r.ownerId, { ownerName: r.ownerName, npis: new Set(r.npis) });
  },
};

// Read every overlay/payer-feed table from corpus.duckdb and normalise to the SAME shape as the
// JSON _identity.json overlay, so mergeOverlay is the single merge code path.
async function loadOverlayFromDb(db) {
  const q = (sql) => query(sql, {}, { db }).catch(() => []);
  const [members, enroll, stays, leie, revoked, nppes, dmeC, partdR, partdC, sat, owner] =
    await Promise.all([
      q("SELECT bene_id, dob, dod, sex, zip FROM members"),
      q(
        "SELECT bene_id, plan_id, program, enrolled_state, effective_from, effective_to, term_reason FROM enrollment",
      ),
      q("SELECT bene_id, admit_date, discharge_date, facility_npi FROM inpatient_stays"),
      q("SELECT npi, excl_type, excl_date FROM leie_overlay"),
      q("SELECT * FROM revoked_overlay"),
      q("SELECT npi, registry_status, state, specialty FROM nppes_overlay"),
      q("SELECT specialty, n, median, mad FROM dme_cohort_overlay"),
      q(
        "SELECT npi, prscrbr_type, opioid_prscrbr_rate, opioid_tot_clms, tot_clms FROM partd_row_overlay",
      ),
      q("SELECT specialty, n, median, mad FROM partd_cohort_overlay"),
      q("SELECT * FROM saturation_overlay"),
      q("SELECT owner_id, owner_name, npi FROM owner_overlay"),
    ]);
  // owner_overlay is one row per (owner, npi) — fold back to {ownerId, ownerName, npis[]}.
  const ownerIdx = new Map();
  for (const r of owner) {
    const e = ownerIdx.get(r.owner_id) || {
      ownerId: r.owner_id,
      ownerName: r.owner_name,
      npis: [],
    };
    e.npis.push(r.npi);
    ownerIdx.set(r.owner_id, e);
  }
  return {
    members: members.map((r) => ({
      beneId: r.bene_id,
      dob: r.dob,
      dod: r.dod,
      sex: r.sex,
      zip: r.zip,
    })),
    enrollment: enroll.map((r) => ({
      beneId: r.bene_id,
      planId: r.plan_id,
      program: r.program,
      enrolledState: r.enrolled_state,
      effectiveFrom: r.effective_from,
      effectiveTo: r.effective_to,
      termReason: r.term_reason,
    })),
    inpatientStays: stays.map((r) => ({
      beneId: r.bene_id,
      admitDate: r.admit_date,
      dischargeDate: r.discharge_date,
      facilityNpi: r.facility_npi,
    })),
    leie: leie.map((r) => ({ npi: r.npi, exclType: r.excl_type, exclDate: r.excl_date })),
    // d10 resolves column names by regex on the FIRST row of ctx.revoked (which is a real
    // ref.revoked_providers row in UPPER_SNAKE) — keep overlay rows in the same key shape.
    revoked: revoked.map((r) => ({
      NPI: r.npi,
      REVOCATION_EFCTV_DT: r.revocation_efctv_dt,
      REENROLLMENT_BAR_EXPRTN_DT: r.reenrollment_bar_exprtn_dt,
      REVOCATION_RSN: r.revocation_rsn,
    })),
    nppes: nppes.map((r) => ({
      npi: r.npi,
      registryStatus: r.registry_status,
      state: r.state,
      specialty: r.specialty,
    })),
    dmeCohorts: dmeC,
    partdRows: partdR.map((r) => ({
      npi: r.npi,
      Prscrbr_Type: r.prscrbr_type,
      Opioid_Prscrbr_Rate: r.opioid_prscrbr_rate,
      Opioid_Tot_Clms: r.opioid_tot_clms,
      Tot_Clms: r.tot_clms,
    })),
    partdCohorts: partdC,
    saturation: sat,
    ownerIndex: [...ownerIdx.values()],
  };
}

// One documented table name per ctx field, so a finding can cite where its trigger row lives.
function buildSources(corpusDb) {
  const c = corpusDb ? "corpus" : "overlay(_identity.json)";
  return {
    mue: "ref.mue / ref.mue_medicaid (by ctx.lob)",
    aoc: "ref.aoc",
    pfs: "ref.pfs",
    ptp: "ref.ptp / ref.ptp_medicaid (by ctx.lob)",
    coverage: "ref.article_x_hcpc_code + ref.article_x_icd10_*",
    leie: `ref.leie + ${c}.leie_overlay`,
    stateExclusions: `ref.state_medicaid_exclusions + ${c}.state_exclusions_overlay`,
    revoked: `ref.revoked_providers + ${c}.revoked_overlay`,
    orderReferring: "ref.order_and_referring",
    optOut: "ref.opt_out",
    cohorts: "ref.partb_by_provider",
    nppes: `enrichment.nppes + ${c}.nppes_overlay`,
    members: `${c}.members`,
    enrollment: `${c}.enrollment`,
    inpatientStays: `${c}.inpatient_stays`,
    dmeCohorts: `ref.dmepos_by_supplier + ${c}.dme_cohort_overlay`,
    partdRows: `ref.partd_by_provider + ${c}.partd_row_overlay`,
    partdCohorts: `ref.partd_by_provider + ${c}.partd_cohort_overlay`,
    saturation: `ref.market_saturation_county + ${c}.saturation_overlay`,
    ownerIndex: `ref.owners_* + ref.ffs_enrollment + ${c}.owner_overlay`,
  };
}

/** DOS (YYYY-MM-DD) -> NCCI/PFS quarter string, e.g. "2024-08-14" -> "2024q3". */
export function resolveQuarter(dos) {
  const [y, m] = dos.split("-").map(Number);
  return `${y}q${Math.floor((m - 1) / 3) + 1}`;
}

// --- minimal RFC4180-ish CSV parser (handles quoted fields + embedded newlines/commas) ---
function parseCsv(text) {
  const rows = [];
  let row = [],
    field = "",
    inQuotes = false;
  for (let i = 0; i < text.length; i++) {
    const c = text[i];
    if (inQuotes) {
      if (c === '"') {
        if (text[i + 1] === '"') {
          field += '"';
          i++;
        } else inQuotes = false;
      } else field += c;
    } else if (c === '"') inQuotes = true;
    else if (c === ",") {
      row.push(field);
      field = "";
    } else if (c === "\n") {
      row.push(field);
      rows.push(row);
      row = [];
      field = "";
    } else if (c === "\r") {
      /* skip */
    } else field += c;
  }
  if (field.length || row.length) {
    row.push(field);
    rows.push(row);
  }
  return rows;
}

/**
 * NCCI MUE practitioner tables → { medicare: Map<hcpcs,{mue,mai,rationale}>, medicaid: Map<…> }.
 * Read from reference.duckdb (ingested by fetch-reference.js). Medicare MAI: 1 = line edit,
 * 2 = absolute DOS cap, 3 = per-day clinical. Medicaid publishes no MAI (mai=null → D1 treats as
 * a per-day edit, which is correct for Medicaid).
 */
export async function loadMUE(quarter) {
  const db = refDb(quarter);
  const load = async (table) => {
    const out = new Map();
    const rows = await query(`SELECT hcpcs, mue, mai, rationale FROM ${table}`, {}, { db }).catch(
      () => [],
    );
    for (const r of rows)
      out.set(r.hcpcs, { mue: r.mue, mai: r.mai, rationale: r.rationale || "" });
    return out;
  };
  return { medicare: await load("mue"), medicaid: await load("mue_medicaid") };
}

/** Codes D11 may flag: never-payable by rationale, or an absolute (MAI-2) zero. NOT bare MUE=0. */
export function nonPayableCodes(mue) {
  const banned = /discontinued|not payable|compounded/i;
  const out = new Map();
  for (const [code, v] of mue) {
    if (banned.test(v.rationale) || (v.mue === 0 && v.mai === 2)) out.set(code, v);
  }
  return out;
}

/**
 * OIG LEIE → { byNpi: Map<npi,row>, rows: [...] }. NPI populated only since ~2008, so ~10% of
 * rows are NPI-joinable (Tier-1); the rest need name+DOB matching (lead-only — see DESIGN.md).
 * Not quarter-versioned; loaded from whichever quarter dir has it (latest fetched).
 */
export function loadLEIE(quarter) {
  const csv = path.join(refDir(quarter), "leie", "UPDATED.csv");
  const rows = parseCsv(readFileSync(csv, "latin1"));
  const hdr = rows[0];
  const idx = Object.fromEntries(hdr.map((h, i) => [h.trim(), i]));
  const byNpi = new Map();
  const out = [];
  for (const r of rows.slice(1)) {
    if (r.length < hdr.length) continue;
    const rec = {
      npi: (r[idx.NPI] || "").trim(),
      lastName: r[idx.LASTNAME],
      firstName: r[idx.FIRSTNAME],
      busName: r[idx.BUSNAME],
      exclType: r[idx.EXCLTYPE],
      exclDate: r[idx.EXCLDATE],
      dob: r[idx.DOB],
    };
    out.push(rec);
    if (rec.npi && rec.npi !== "0000000000") byNpi.set(rec.npi, rec);
  }
  return { byNpi, rows: out };
}

/**
 * State Medicaid exclusion lists (OpenSanctions aggregation) → Map<npi, {state, name, sanctionDate}>.
 * Only rows with a parseable 10-digit NPI in `identifiers` (Tier-1 join). dataset is e.g.
 * "us_ny_med_exclusions" → state "NY". Not quarter-versioned upstream.
 */
export async function loadStateExclusions(quarter) {
  const out = new Map();
  const rows = await query(
    "SELECT npi, state, name, sanctions, first_seen FROM state_medicaid_exclusions WHERE npi IS NOT NULL AND npi <> ''",
    {},
    { db: refDb(quarter) },
  ).catch(() => []);
  for (const r of rows) {
    // `sanctions` is the state's listed action date (YYYY-MM-DD); first_seen is OpenSanctions' crawl
    // timestamp — only fall back to its date part if sanctions is empty.
    const sanctionDate = r.sanctions || (r.first_seen ? String(r.first_seen).slice(0, 10) : null);
    out.set(r.npi, { state: r.state, name: r.name, sanctionDate });
  }
  return out;
}

/**
 * CMS catalog-backed tables (data.cms.gov) — ingested into reference.duckdb as named tables by
 * fetch-reference.js (kind: "cms-catalog"). Read via DuckDB; fall back to the legacy JSON sample
 * if the DB/table hasn't been ingested yet so the eval keeps running during bootstrap.
 */
async function loadTable(quarter, table, { cols, jsonFallback } = {}) {
  const db = refDb(quarter);
  if (existsSync(db)) {
    try {
      return await query(`SELECT ${cols || "*"} FROM ${table}`, {}, { db });
    } catch {
      /* table not ingested yet — fall through */
    }
  }
  const json = jsonFallback && path.join(refDir(quarter), jsonFallback);
  return json && existsSync(json) ? JSON.parse(readFileSync(json, "utf8")) : [];
}
export const loadPartBGeography = (q) => loadTable(q, "partb_by_geography");
export const loadRevoked = (q) =>
  loadTable(q, "revoked_providers", { jsonFallback: "enrollment/revoked-providers.json" });
export const loadOrderReferring = (q) =>
  loadTable(q, "order_and_referring", { jsonFallback: "enrollment/order-and-referring.json" });
export const loadOptOut = (q) => loadTable(q, "opt_out");
// D7 queries the table directly via cohortStatsSql() — this loader is kept only for the legacy
// in-JS cohortStats() path and is intentionally NOT loaded into ctx by default (1.3M rows in
// memory). buildContext sets ctx.partbByProvider = null; D7 falls back to SQL.
export const loadPartBProvider = (q) =>
  loadTable(q, "partb_by_provider", {
    cols: "Rndrng_NPI, Rndrng_Prvdr_Type, Rndrng_Prvdr_State_Abrvtn, Tot_Benes, Tot_Srvcs",
    jsonFallback: "benchmarks/partb-by-provider.json",
  });

/**
 * PFS PPRRVU (non-QPP) → Map<hcpcs, {status, workRvu, peRvu, mpRvu, globalDays, cf}>.
 * Positional parse (multi-row header makes names ambiguous). status 'A' = active/separately
 * payable; globalDays (000/010/090/XXX/YYY/ZZZ) powers D13. Drives exposure $ for PFS codes.
 */
export function loadPFS(quarter) {
  const dir = path.join(refDir(quarter), "pfs", "rvu26a");
  const rows = parseCsv(readFileSync(findFile(dir, /PPRRVU.*nonQPP\.csv$/i), "latin1"));
  const start = rows.findIndex((r) => (r[0] || "").trim() === "HCPCS") + 1;
  const out = new Map();
  for (const r of rows.slice(start)) {
    const code = (r[0] || "").trim();
    if (!/^[0-9A-Z]{5}$/.test(code)) continue;
    out.set(code, {
      status: (r[3] || "").trim(),
      workRvu: Number(r[5]) || 0,
      peRvu: Number(r[6]) || 0,
      mpRvu: Number(r[10]) || 0,
      globalDays: (r[14] || "").trim(),
      cf: Number(r[25]) || 0,
    });
  }
  return out;
}

/** NCCI add-on-code edits → Map<addon, {primaries:Set, contractorDefined:bool}>. D3 orphan add-on. */
export function loadAOC(quarter) {
  const dir = path.join(refDir(quarter), "ncci", "add-on-codes");
  const txt = readFileSync(findFile(dir, /\.txt$/i), "latin1");
  const out = new Map();
  for (const line of txt.split(/\r?\n/)) {
    const p = line.trim().split(/\s+/);
    if (p.length < 2 || !/^[0-9A-Z]{5,6}$/.test(p[0])) continue;
    const e = out.get(p[0]) || { primaries: new Set(), contractorDefined: false };
    if (p[1] === "CCCCC") e.contractorDefined = true;
    else e.primaries.add(p[1]);
    out.set(p[0], e);
  }
  return out;
}

/** PTP DELTA only (additions) — full base table is AMA-gated (DESIGN.md §4). Label citations partial. */
export function loadPTPChanges(quarter) {
  const dir = path.join(refDir(quarter), "ncci", "ptp-practitioner-changes");
  const lines = readFileSync(findFile(dir, /Additions.*\.txt$/i), "latin1").split(/\r?\n/);
  const pairs = [];
  for (const line of lines) {
    const p = line.trim().split(/[\s,]+/);
    if (p.length >= 2 && /^[0-9A-Z]{5}$/.test(p[0]) && /^[0-9A-Z]{5}$/.test(p[1])) {
      pairs.push({ col1: p[0], col2: p[1] });
    }
  }
  return pairs;
}

/**
 * Full NCCI PTP base tables (practitioner) → { medicare: Map<"c1|c2",{mod,rationale}>, medicaid }.
 * Read from reference.duckdb (ingested by fetch-reference.js). Keeps only ACTIVE edits — Medicare
 * marks active rows with deletion='*'; Medicaid leaves deletion empty. mod: "0" = never allowed,
 * "1" = allowed only with an appropriate bypass modifier. `codeFilter` (Set of HCPCS) scopes to
 * edits whose BOTH codes appear in the corpus — the full tables are ~1.7M+ active pairs each.
 */
export async function loadPTP(quarter, codeFilter) {
  const db = refDb(quarter);
  const list = [...(codeFilter || [])].map((c) => `'${String(c).replace(/'/g, "''")}'`).join(",");
  const load = async (table) => {
    const out = new Map();
    if (!list) return out;
    const rows = await query(
      `SELECT column1, column2, mod, rationale FROM ${table}
       WHERE (deletion = '*' OR deletion IS NULL OR deletion = '')
         AND column1 IN (${list}) AND column2 IN (${list})`,
      {},
      { db },
    ).catch(() => []);
    for (const r of rows)
      out.set(`${r.column1}|${r.column2}`, { mod: String(r.mod), rationale: r.rationale || "" });
    return out;
  };
  return { medicare: await load("ptp"), medicaid: await load("ptp_medicaid") };
}

/**
 * CMS Medicare Coverage (Billing & Coding Articles) — HCPCS ↔ covered/non-covered ICD-10.
 * Since ~2019 CMS keeps the covered-diagnosis lists in companion Articles, not the LCDs. Parses the
 * three MCD export tables (article_x_hcpc_code, article_x_icd10_covered, article_x_icd10_noncovered).
 * Returns { hcpcToArticles: Map<hcpc, Set<articleId>>, coveredByArticle, noncoveredByArticle }.
 * Pass `codeFilter` (a Set of HCPCS) to scope to the corpus — the covered table is ~426k rows.
 */
export async function loadLcdByHcpcs(quarter, codeFilter) {
  if (!codeFilter || !codeFilter.size) return new Map();
  const list = [...codeFilter].map((c) => `'${String(c).replace(/'/g, "''")}'`).join(",");
  const rows = await query(
    `SELECT hcpc_code_id AS hcpcs, lcd_id FROM lcd_x_hcpc_code WHERE hcpc_code_id IN (${list})`,
    {},
    { db: refDb(quarter) },
  );
  const out = new Map();
  for (const r of rows) {
    const a = out.get(r.hcpcs) || [];
    a.push(Number(r.lcd_id));
    out.set(r.hcpcs, a);
  }
  return out;
}

export function loadCoverage(quarter, codeFilter) {
  const dir = path.join(refDir(quarter), "coverage");
  const empty = {
    hcpcToArticles: new Map(),
    coveredByArticle: new Map(),
    noncoveredByArticle: new Map(),
  };
  if (!existsSync(dir)) return empty;
  // quoted CSV "a","b",... — fields I need (id, code) precede the comma-bearing descriptions
  const cell = (s) => s.replace(/^"/, "").replace(/"$/, "");
  const rows = (file) => readFileSync(path.join(dir, file), "latin1").split(/\r?\n/).slice(1);

  const hcpcToArticles = new Map();
  const relevant = new Set();
  for (const line of rows("article_x_hcpc_code.csv")) {
    const p = line.split('","');
    if (p.length < 3) continue;
    const articleId = cell(p[0]);
    const hcpc = cell(p[2]);
    if (codeFilter && !codeFilter.has(hcpc)) continue;
    if (!hcpcToArticles.has(hcpc)) hcpcToArticles.set(hcpc, new Set());
    hcpcToArticles.get(hcpc).add(articleId);
    relevant.add(articleId);
  }
  const codesByArticle = (file) => {
    const out = new Map();
    if (!relevant.size) return out;
    for (const line of rows(file)) {
      const p = line.split('","');
      if (p.length < 3) continue;
      const articleId = cell(p[0]);
      if (!relevant.has(articleId)) continue;
      if (!out.has(articleId)) out.set(articleId, new Set());
      out.get(articleId).add(cell(p[2]));
    }
    return out;
  };
  return {
    hcpcToArticles,
    coveredByArticle: codesByArticle("article_x_icd10_covered.csv"),
    noncoveredByArticle: codesByArticle("article_x_icd10_noncovered.csv"),
  };
}

function findFile(dir, re) {
  const hit = readdirSync(dir).find((f) => re.test(f));
  if (!hit) throw new Error(`no file matching ${re} in ${dir}`);
  return path.join(dir, hit);
}
