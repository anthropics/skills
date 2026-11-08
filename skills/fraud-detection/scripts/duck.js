// Thin DuckDB CLI wrapper. We shell out (no native bindings) so the plugin stays a plain-JS
// install. DuckDB gives us native MEDIAN/MAD/QUANTILE and a single persistent .duckdb store —
// the cms-catalog fetch kind ingests reference tables into it; detectors query named tables.
//
// Requires `duckdb` on PATH (brew install duckdb / apt install duckdb).
import { execFile } from "node:child_process";
import { promisify } from "node:util";

import { SKILL_ROOT as ROOT } from "./paths.js";
// One persistent DB per quarter; reference tables live as named tables inside it.
export { refDir, refDb, refMeta } from "./paths.js";

const exec = promisify(execFile);

// Single-quote a literal for inline SQL. Prefer `query(sql, {params})` over building SQL strings.
const sqlLit = (v) =>
  v == null ? "NULL" : typeof v === "number" ? String(v) : `'${String(v).replace(/'/g, "''")}'`;

/**
 * Run a SQL statement and return parsed rows (array of objects).
 * `params` are substituted as `$name` → SQL-quoted literal (this is NOT a prepared statement —
 * callers must only pass trusted/validated values; detector inputs are deterministic-floor data).
 * `db` opens a persistent database file (default: in-memory).
 */
export async function query(sql, params = {}, { db, cwd = ROOT } = {}) {
  let q = sql;
  for (const [k, v] of Object.entries(params)) q = q.replaceAll(`$${k}`, sqlLit(v));
  const args = db ? [db, "-readonly", "-json", "-c", q] : ["-json", "-c", q];
  const { stdout } = await exec("duckdb", args, { cwd, maxBuffer: 256 * 1024 * 1024 });
  const out = stdout.trim();
  return out ? JSON.parse(out) : [];
}

/** Run a statement for side effects (CREATE TABLE, COPY TO, etc.); returns nothing. */
export async function ddl(sql, { db, cwd = ROOT } = {}) {
  const args = db ? [db, "-c", sql] : ["-c", sql];
  await exec("duckdb", args, { cwd, maxBuffer: 256 * 1024 * 1024 });
}
