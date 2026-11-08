// Loaders for the cached enrichment snapshots (scripts/fetch-enrichment.js). These read the
// fetched-and-cached public answers so detectors get reproducible enrichment with no runtime
// network/MCP dependency. All loaders degrade gracefully (empty map) when the cache is absent,
// so the deterministic core still runs without a fetch.
import { readFileSync, readdirSync, existsSync } from "node:fs";
import path from "node:path";

import { dataCache } from "./paths.js";

// ICD-10-CM validity by code → Map<code, { valid, description }>
export function loadIcd10() {
  const file = dataCache("enrichment", "icd10", "validity.json");
  if (!existsSync(file)) return new Map();
  const { codes } = JSON.parse(readFileSync(file, "utf8"));
  return new Map(Object.entries(codes || {}));
}

// CMS Coverage document INDEX (LCDs + Articles) → { lcds:[...], articles:[...] }. This is the
// token-free public catalog (id/displayId/title/effective/url) — it does NOT carry HCPCS→covered-ICD-10
// mappings (those are auth-gated), so it cannot yet power D4 medical-necessity. Useful as a coverage
// catalog the skill can reference. Degrades to empty arrays if the cache is absent.
export function loadCoverageIndex() {
  const read = (name) => {
    const file = dataCache("enrichment", "cms-coverage", `${name}.json`);
    return existsSync(file) ? JSON.parse(readFileSync(file, "utf8")).rows || [] : [];
  };
  return { lcds: read("lcds"), articles: read("articles") };
}

// NPPES registry status by NPI → Map<npi, { registryStatus, providerName, specialty, state }>.
// Populated by scripts/fetch-nppes.js. Degrades to an empty map when the cache is absent.
export function loadNppes() {
  const dir = dataCache("enrichment", "nppes");
  if (!existsSync(dir)) return new Map();
  const m = new Map();
  for (const f of readdirSync(dir)) {
    if (!f.endsWith(".json")) continue;
    const r = JSON.parse(readFileSync(path.join(dir, f), "utf8"));
    if (r.npi) m.set(r.npi, r);
  }
  return m;
}
