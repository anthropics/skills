// Auto-discovers detector modules (dNN-*.js) so the workflow fans out over all of them.
// Each module exports `detector` = { id, tier, scheme, label, cat, needsJudgment, link?, run(claims, ctx) }.
//
// This is the SINGLE SOURCE for per-detector metadata. SCHEME / LINKS / NEEDS_JUDGMENT /
// COVERED_SCHEMES are all derived from the detector files themselves — adding a new dNN-*.js is
// the only step needed to register a detector across the pipeline, the renderers, and the
// workflow prompts (screen.js writes needsJudgment + coveredSchemes into referrals.index.json
// meta so the sandboxed workflow can read them without importing this module).
import { readdirSync } from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";

export async function loadDetectors() {
  const dir = import.meta.dirname;
  const files = readdirSync(dir)
    .filter((f) => /^d\d\d-.*\.js$/.test(f))
    .sort();
  const out = [];
  for (const f of files) {
    const mod = await import(pathToFileURL(path.join(dir, f)).href);
    if (mod.detector) out.push(mod.detector);
  }
  return out;
}

// Top-level await (ESM) — every consumer of these maps is already async-loaded.
export const DETECTORS = await loadDetectors();

export const SCHEME = Object.fromEntries(
  DETECTORS.map((d) => [d.scheme, { cat: d.cat, label: d.label }]),
);

export const LINKS = Object.fromEntries(DETECTORS.filter((d) => d.link).map((d) => [d.id, d.link]));

export const NEEDS_JUDGMENT = new Set(DETECTORS.filter((d) => d.needsJudgment).map((d) => d.id));

export const COVERED_SCHEMES = DETECTORS.map((d) => `${d.id} ${d.scheme}`).join(", ");
