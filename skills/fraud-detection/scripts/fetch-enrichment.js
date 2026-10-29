#!/usr/bin/env node
// Fetch + CACHE public code-keyed enrichment the detectors can cite against, deterministically.
// This is the script-API alternative to live MCP calls: we snapshot the public answer once and
// cache it as reference, so a sweep is reproducible (no runtime auth / rate limits / drift).
// Plain JS (node 18+ / bun), public government APIs only, no PHI. Output → gitignored enrichment/.
//
//   node scripts/fetch-enrichment.js
//
// Sources (code-keyed → work on synthetic claims, since the CODES are real):
//   • ICD-10-CM validity/description — NLM Clinical Tables (no auth)
//   • CMS Coverage LCD/NCD — api.coverage.cms.gov (feeds D4 medical-necessity)
// NPI Registry is intentionally NOT fetched here: 9-prefix NPIs are NPPES-reserved (never issued)
// and never resolve in NPPES by design — NPI enrichment stays interactive/optional (see PLUGIN.md).
//
// Network note: clinicaltables.nlm.nih.gov is not on the dev sandbox allowlist — run sandbox-disabled.
import { mkdir, writeFile, readFile } from "node:fs/promises";
import path from "node:path";

import { dataCache } from "./paths.js";

const OUT = dataCache("enrichment");

// every distinct diagnosis code referenced by the corpus you are about to screen.
// Pass the corpus as a JSON file (array of claims, each with a `diagnoses: [{code}]` field):
//   node scripts/fetch-enrichment.js path/to/claims.json
async function corpusDxCodes() {
  const corpusPath = process.argv[2];
  if (!corpusPath) {
    throw new Error("usage: node scripts/fetch-enrichment.js <claims.json>");
  }
  const claims = JSON.parse(await readFile(corpusPath, "utf8"));
  const s = new Set();
  for (const c of claims) for (const d of c.diagnoses || []) if (d.code) s.add(d.code);
  return [...s].sort();
}

// NLM Clinical Tables ICD-10-CM: returns [total, [codes], null, [[code, name],...]]
async function fetchIcd10(code) {
  const url = `https://clinicaltables.nlm.nih.gov/api/icd10cm/v3/search?sf=code&terms=${encodeURIComponent(code)}`;
  const res = await fetch(url);
  if (!res.ok) throw new Error(`ICD-10 ${code}: HTTP ${res.status}`);
  const [, , , rows] = await res.json();
  // exact match on the normalized code (the API may return related codes too)
  const norm = (x) => x.replace(/\./g, "").toUpperCase();
  const hit = (rows || []).find((r) => norm(r[0]) === norm(code));
  return { code, valid: Boolean(hit), description: hit ? hit[1] : null };
}

async function main() {
  await mkdir(path.join(OUT, "icd10"), { recursive: true });
  const codes = await corpusDxCodes();
  console.log(`ICD-10: validating ${codes.length} distinct corpus dx codes via NLM…`);
  const out = {};
  for (const code of codes) {
    try {
      out[code] = await fetchIcd10(code);
      console.log(
        `  ${code} → ${out[code].valid ? "valid" : "INVALID"}${out[code].description ? ` (${out[code].description})` : ""}`,
      );
    } catch (e) {
      out[code] = { code, valid: null, description: null, error: String(e.message) };
      console.log(`  ${code} → error: ${e.message}`);
    }
  }
  const file = path.join(OUT, "icd10", "validity.json");
  await writeFile(
    file,
    JSON.stringify(
      { source: "NLM Clinical Tables ICD-10-CM v3", fetched: codes.length, codes: out },
      null,
      2,
    ),
  );
  console.log(`wrote enrichment/icd10/validity.json (${Object.keys(out).length} codes)`);

  await fetchCmsCoverageIndex();
}

// CMS Coverage (Medicare Coverage Database) — PUBLIC, token-free at /v1/reports/*. NOTE: this gives
// the LCD/Article document INDEX (id, display id, title, dates, url) only. The HCPCS→covered-ICD-10
// mappings that D4 medical-necessity needs live behind the AUTHENTICATED /v1/data/* endpoints (HTTP
// 401 without a token), so they are NOT fetched here — D4 stays blocked on a code-mapping source
// (see BUILD.md / HILLCLIMB.md). Caching the index still gives the skill a real coverage catalog.
async function fetchCmsCoverageIndex() {
  await mkdir(path.join(OUT, "cms-coverage"), { recursive: true });
  const base = "https://api.coverage.cms.gov/v1/reports";
  for (const [name, report] of [
    ["lcds", "local-coverage-final-lcds"],
    ["articles", "local-coverage-articles"],
  ]) {
    try {
      const res = await fetch(`${base}/${report}?`);
      if (!res.ok) throw new Error(`HTTP ${res.status}`);
      const json = await res.json();
      const rows = (json.data || []).map((d) => ({
        id: d.document_id,
        displayId: d.document_display_id,
        type: d.document_type,
        title: d.title,
        effective: d.effective_date,
        url: d.url,
      }));
      const file = path.join(OUT, "cms-coverage", `${name}.json`);
      await writeFile(
        file,
        JSON.stringify({ source: `CMS MCD ${report}`, count: rows.length, rows }, null, 2),
      );
      console.log(`wrote enrichment/cms-coverage/${name}.json (${rows.length} ${name})`);
    } catch (e) {
      console.log(`CMS Coverage ${name} → error: ${e.message}`);
    }
  }
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
