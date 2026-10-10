#!/usr/bin/env node
import { existsSync } from "node:fs";
// Fetch + CACHE NPPES registry status for every billing/rendering/referring NPI in a corpus.
// Snapshot pattern (same as fetch-enrichment.js): query the public NPI Registry once, write the
// answer to <DATA_ROOT>/data-cache/enrichment/nppes/<npi>.json, and the pipeline reads the cache —
// so the sweep is reproducible with no runtime network/MCP dependency.
//
//   node scripts/fetch-nppes.js <corpus.duckdb>
//
// 9-prefix NPIs are NPPES-reserved (never issued) and do not resolve by design — they cache as
// { registryStatus: "not-found" }, which is itself the improper-billing signal the rubric checks.
//
// Network note: npiregistry.cms.gov may be blocked by the command sandbox — run sandbox-disabled.
import { mkdir, writeFile } from "node:fs/promises";
import path from "node:path";

import { query } from "./duck.js";
import { dataCache, corpusDb as defaultCorpusDb } from "./paths.js";

const OUT = dataCache("enrichment", "nppes");

async function corpusNpis(db) {
  const rows = await query(
    `SELECT DISTINCT npi FROM (
       SELECT billing_npi AS npi FROM claims
       UNION SELECT rendering_npi FROM claims
       UNION SELECT referring_npi FROM claims
     ) WHERE npi IS NOT NULL ORDER BY npi`,
    {},
    { db },
  );
  return rows.map((r) => String(r.npi));
}

async function fetchNppes(npi) {
  // Format guard FIRST — a non-10-digit value never reaches the URL.
  if (!/^\d{10}$/.test(npi)) {
    return { npi, registryStatus: "not-found", note: "invalid NPI format (not 10 digits)" };
  }
  // NPPES reserves the 9-prefix range — a 9xxxxxxxxx NPI is non-issued by definition. Short-circuit
  // to not-found without a network call (so synthetic fixtures need no egress to cache correctly).
  if (npi.startsWith("9")) {
    return { npi, registryStatus: "not-found", note: "9-prefix NPI is NPPES reserved/non-issued" };
  }
  const url = new URL("https://npiregistry.cms.gov/api/");
  url.searchParams.set("version", "2.1");
  url.searchParams.set("number", npi);
  const res = await fetch(url);
  if (!res.ok) return { npi, registryStatus: "unknown", note: `HTTP ${res.status}` };
  const json = await res.json();
  const r = (json.results || [])[0];
  if (!r) return { npi, registryStatus: "not-found" };
  const b = r.basic || {};
  const status = b.status === "A" ? "active" : b.status === "D" ? "deactivated" : "unknown";
  const tax = (r.taxonomies || []).find((t) => t.primary) || (r.taxonomies || [])[0] || {};
  const loc = (r.addresses || []).find((a) => a.address_purpose === "LOCATION") || {};
  return {
    npi,
    registryStatus: status,
    providerName: b.organization_name || `${b.first_name || ""} ${b.last_name || ""}`.trim(),
    specialty: tax.desc || "",
    state: loc.state || "",
  };
}

async function main() {
  const db = process.argv[2] || defaultCorpusDb();
  await mkdir(OUT, { recursive: true });
  const npis = await corpusNpis(db);
  console.log(`NPPES: resolving ${npis.length} distinct NPIs…`);
  for (const npi of npis) {
    const file = path.join(OUT, `${npi}.json`);
    if (existsSync(file)) {
      console.log(`  ${npi} → cached`);
      continue;
    }
    try {
      const out = await fetchNppes(npi);
      await writeFile(file, JSON.stringify(out, null, 2));
      console.log(
        `  ${npi} → ${out.registryStatus}${out.providerName ? ` (${out.providerName})` : ""}`,
      );
    } catch (e) {
      await writeFile(
        file,
        JSON.stringify({ npi, registryStatus: "unknown", error: String(e.message) }, null, 2),
      );
      console.log(`  ${npi} → error: ${e.message}`);
    }
  }
  console.log(`wrote ${OUT}/ (${npis.length} NPIs)`);
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
