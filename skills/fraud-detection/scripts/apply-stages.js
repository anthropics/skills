#!/usr/bin/env node
// Applies the workflow return (detect/adjudicate/synthesize) onto the detect-stage snapshot to
// produce the auditable stage files. The workflow sandbox has no filesystem, so the skill writes
// the workflow return to out/workflow-result.json and then runs this script.
//
//   node scripts/apply-stages.js
//
// Reads:  out/referrals.detect.json, out/workflow-result.json
// Writes: out/referrals.adjudicated.json, out/referrals.final.json, out/referrals.json (canonical),
//         out/source-excerpts.json, out/providers.json (sidecars for the renderers)
import { readFileSync, writeFileSync, existsSync } from "node:fs";
import path from "node:path";

import { outDir as resolveOutDir } from "./paths.js";

const outDir = resolveOutDir();
const round = (n) => Math.round(n * 100) / 100;

const detect = JSON.parse(readFileSync(path.join(outDir, "referrals.detect.json"), "utf8"));
const wfPath = path.join(outDir, "workflow-result.json");
if (!existsSync(wfPath)) {
  console.error("out/workflow-result.json not found — write the workflow return there first");
  process.exit(1);
}
// The skill may write either the workflow script's return value directly, OR the Workflow tool's
// wrapper {summary, agentCount, logs, result}. Unwrap to the inner result either way.
let wf = JSON.parse(readFileSync(wfPath, "utf8"));
if (wf && wf.result && !wf.adjudicate) wf = wf.result;

// ── adjudicated snapshot: merge {status, adjudication} onto each finding ───────
const adjBy = new Map();
for (const a of wf.adjudicate?.findings ?? []) adjBy.set(`${a.npi}|${a.detectorId}`, a);
const adjudicated = structuredClone(detect);
for (const r of adjudicated.referrals) {
  for (const f of r.findings) {
    const a = adjBy.get(`${r.npi}|${f.detectorId}`);
    f.status = a?.status ?? "confirmed";
    f.adjudication = a?.adjudication ?? { by: "rule", confidence: "high", reason: f.citation.rule };
  }
}
writeFileSync(
  path.join(outDir, "referrals.adjudicated.json"),
  JSON.stringify(adjudicated, null, 2),
);

// ── final snapshot: attach narratives + recompute meta from confirmed-only ─────
const caseBy = new Map();
for (const c of wf.synthesize?.cases ?? []) caseBy.set(c.npi, c);
const final = structuredClone(adjudicated);
for (const r of final.referrals) {
  const c = caseBy.get(r.npi);
  if (c)
    r.narrative = {
      priority: c.priority,
      text: c.narrative,
      citedFindings: c.citedFindings,
      caveats: c.caveats,
      audit: c.audit,
    };
  // Exposure recompute. The detect-stage recoverable/estimate are ALREADY per-line-deduped by
  // pipeline.js (multiple detectors on the same claim line count once). A naive re-sum here would
  // undo that. So: keep the detect-stage values when nothing is dismissed (the common case). When a
  // finding IS dismissed, subtract its exposure but never below zero — this is an upper bound when
  // the dismissed finding overlapped another detector on the same line; a precise recompute would
  // re-run pipeline.js's dedup over the surviving findings.
  const dismissed = r.findings.filter((f) => f.status === "dismissed");
  if (dismissed.length) {
    let rec = r.recoverableUsd;
    let est = r.statisticalEstimateUsd;
    for (const f of dismissed) {
      if (f.detectorId === "D7" || f.detectorId === "D15") est -= f.exposureUsd;
      else rec -= f.exposureUsd;
    }
    r.recoverableUsd = round(Math.max(0, rec));
    r.statisticalEstimateUsd = round(Math.max(0, est));
    r.exposureUsd = round(r.recoverableUsd + r.statisticalEstimateUsd);
  }
}
final.meta.recoverableUsd = round(final.referrals.reduce((s, r) => s + r.recoverableUsd, 0));
final.meta.statisticalEstimateUsd = round(
  final.referrals.reduce((s, r) => s + r.statisticalEstimateUsd, 0),
);
final.meta.totalExposureUsd = round(final.meta.recoverableUsd + final.meta.statisticalEstimateUsd);
final.leads = wf.synthesize?.leads ?? [];
writeFileSync(path.join(outDir, "referrals.final.json"), JSON.stringify(final, null, 2));
writeFileSync(path.join(outDir, "referrals.json"), JSON.stringify(final, null, 2));

// ── sidecars for the renderers (same shape as before) ──────────────────────────
const excerpts = {};
const providers = {};
for (const c of wf.synthesize?.cases ?? []) {
  for (const e of c.sourceExcerpts ?? []) {
    (excerpts[c.npi] ||= {})[e.detectorId] = { excerpt: e.excerpt, highlight: e.highlight };
  }
}
for (const r of final.referrals) {
  const e = r.enrichment;
  if (e?.registryStatus === "active" && e.providerName) {
    providers[r.npi] = { name: e.providerName, specialty: e.specialty, state: e.state };
  }
}
writeFileSync(path.join(outDir, "source-excerpts.json"), JSON.stringify(excerpts, null, 2));
writeFileSync(path.join(outDir, "providers.json"), JSON.stringify(providers, null, 2));

console.log(
  `apply-stages: adjudicated (${adjBy.size} findings) → final ` +
    `($${final.meta.recoverableUsd} recoverable + $${final.meta.statisticalEstimateUsd} estimate, ` +
    `${final.referrals.length} referrals, ${final.leads.length} leads)`,
);
