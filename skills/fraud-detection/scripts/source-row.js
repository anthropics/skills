// For every TABLE-BACKED finding, attach the exact reference-table row that triggered it and
// write that row to a tiny sibling CSV in the run dir — so a reviewer sees the literal data point
// inline ("here is the row that says 11450 has GLOB DAYS=090") and can download/recheck it without
// hunting through a 1.3M-row file. Mirrors the D7 cohort-slice pattern, generalized.
//
// Called from screen.js after runSweep:
//   await attachSourceRows(result, ctx)
//   await writeSourceRowSlices(result, ctx, outDir)
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import path from "node:path";

import { query, refDb, refMeta } from "./duck.js";

// All reference tables now live in reference.duckdb; provenance (sourceUrl/release/rows) comes
// from reference.meta.json. Identity-keyed tables (leie, revoked_providers) still pull rows from
// the overlay-merged ctx Maps so 9-prefix reserved-range NPIs resolve against synthetic fixtures.

const slug = (s) =>
  String(s)
    .toLowerCase()
    .replace(/[^a-z0-9]+/g, "-")
    .replace(/^-+|-+$/g, "");

// Per-detector spec: how to pull the triggering row out of ctx (file-based loaders) or DuckDB.
// Return null when the detector isn't row-backed (computed/statistical).
// TODO: ROW_SPECS is the last per-detector map outside the dNN-*.js files. It's a function (not
// data) so it doesn't fold into the registry pattern cleanly yet — when refactoring, move each
// spec onto detector.sourceRow(f, ctx) and derive ROW_SPECS from registry.DETECTORS.
const ROW_SPECS = {
  D1: (f) => {
    const t = f.evidence.program === "medicaid" ? "mue_medicaid" : "mue";
    return {
      table: t,
      key: { hcpcs: f.citation.hcpcs },
      sql: `SELECT hcpcs, mue, mai, rationale FROM ${t} WHERE hcpcs = $hcpcs`,
    };
  },
  D2: (f) => {
    const t = f.evidence.program === "medicaid" ? "ptp_medicaid" : "ptp";
    return {
      table: t,
      key: { column1: f.evidence.column1, column2: f.evidence.column2 },
      sql: `SELECT column1, column2, mod, effective, deletion, rationale FROM ${t} WHERE column1 = $column1 AND column2 = $column2`,
    };
  },
  D3: (f, ctx) => {
    if (f.evidence?.signal !== "excluded-provider") return null; // after-death/orphan are not row-backed
    const npi = f.evidence.role === "rendering" ? null : f.npi; // billing-NPI exclusion
    const r = ctx.leie?.byNpi?.get?.(npi);
    return r ? { table: "leie", key: { NPI: npi }, row: r } : null;
  },
  D9: (f) => ({
    // Negative evidence: the orderer NPI is ABSENT from order_and_referring. row=null is the proof.
    table: "order_and_referring",
    key: { NPI: f.evidence.orderingNpi },
    sql: `SELECT * FROM order_and_referring WHERE NPI = $NPI`,
    absenceIsFinding: true,
  }),
  D10: (f, ctx) => {
    // ctx.revoked is the overlay-merged array (real CMS rows + synthetic _identity.json rows for the
    // 9-prefix reserved range), so pull from it rather than DuckDB so synthetic NPIs resolve.
    const r = (ctx.revoked || []).find((x) => (x.NPI || "").trim() === f.npi);
    return r ? { table: "revoked_providers", key: { NPI: f.npi }, row: r } : null;
  },
  D11: (f) => {
    const t = f.evidence.program === "medicaid" ? "mue_medicaid" : "mue";
    return {
      table: t,
      key: { hcpcs: f.citation.hcpcs },
      sql: `SELECT hcpcs, mue, mai, rationale FROM ${t} WHERE hcpcs = $hcpcs`,
    };
  },
  D13: (f) => ({
    table: "pfs",
    key: { hcpcs: f.evidence.procedure },
    sql: `SELECT hcpcs, description, status, glob_days, work_rvu, conv_factor FROM pfs WHERE hcpcs = $hcpcs AND mod IS NULL`,
  }),
  D14: (f) => ({
    table: "opt_out",
    key: { NPI: f.evidence.npi },
    sql: `SELECT * FROM opt_out WHERE NPI = $NPI`,
  }),
};

function loadMeta(quarter) {
  const f = refMeta(quarter);
  return existsSync(f) ? JSON.parse(readFileSync(f, "utf8")) : {};
}

// Attach evidence.sourceRow to every row-backed finding. ctx-map specs already carry `row`;
// `sql` specs are resolved against reference.duckdb.
export async function attachSourceRows(result, ctx) {
  const meta = loadMeta(ctx.quarter);
  const db = refDb(ctx.quarter);
  for (const r of result.referrals) {
    for (const f of r.findings) {
      const spec = ROW_SPECS[f.detectorId]?.(f, ctx);
      if (!spec) continue;
      let row = spec.row;
      if (spec.sql) {
        const rows = await query(spec.sql, spec.key, { db });
        row = rows[0] ?? null;
      }
      const m = meta[spec.table];
      f.evidence.sourceRow = {
        table: spec.table,
        key: spec.key,
        row,
        absenceIsFinding: spec.absenceIsFinding && row == null,
        sourceUrl: m?.sourceUrl ?? null,
        sourceLabel: m?.sourceUrl?.split("/").pop() ?? m?.title ?? null,
        release: m?.release ?? ctx.quarter,
        file: `srcrow-${spec.table}-${slug(Object.values(spec.key).join("-"))}.csv`,
      };
    }
  }
}

// Write each sourceRow to a one-row CSV in outDir so the reviewer can download the exact data point.
// attachSourceRows already resolved `row` (ctx-map and DuckDB alike), so write uniformly from memory.
export function writeSourceRowSlices(result, ctx, outDir) {
  const written = new Set();
  for (const r of result.referrals) {
    for (const f of r.findings) {
      const sr = f.evidence?.sourceRow;
      if (!sr || written.has(sr.file)) continue;
      written.add(sr.file);
      const out = path.join(outDir, sr.file);
      if (sr.row) {
        const cols = Object.keys(sr.row);
        writeFileSync(
          out,
          cols.join(",") + "\n" + cols.map((c) => csvCell(sr.row[c])).join(",") + "\n",
        );
      } else if (sr.absenceIsFinding) {
        writeFileSync(
          out,
          `# no row in ${sr.table} for ${JSON.stringify(sr.key)} — that absence IS the finding\n`,
        );
      }
    }
  }
}

const csvCell = (v) => {
  const s = v == null ? "" : String(v);
  return /[",\n]/.test(s) ? `"${s.replace(/"/g, '""')}"` : s;
};
