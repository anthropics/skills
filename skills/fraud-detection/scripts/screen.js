#!/usr/bin/env node
// Screen a claims corpus → out/referrals.json (the deterministic core; zero model calls).
// This is the product entry point for the deterministic sweep — point it at any corpus directory
// of one-claim-per-file JSON. The model-driven investigation (workflows/investigate.js) calls this
// as its Tier-1 floor; you can also run it standalone to validate the pipeline end-to-end.
//
//   node scripts/screen.js <corpus.duckdb> [quarter] [lob]
//   node scripts/screen.js ~/.claude/data/healthcare/fraud-detection/data-cache/corpus.duckdb 2026q3 medicaid
//
// corpus.duckdb is built per LOAD-CLAIMS.md from a real payer
// feed. `lob` (medicare|medicaid, default medicare) routes the program-specific NCCI tables and
// state-exclusion lookups via ctx.lob — program is now a property of the run, not the claim row.
import { writeFileSync, mkdirSync } from "node:fs";
import path from "node:path";

import { writeCohortSlices } from "./cohort-slice.js";
import { query } from "./duck.js";
import { outDir as resolveOutDir } from "./paths.js";
import { runSweep } from "./pipeline.js";
import { buildContext } from "./reference-data.js";
import { COVERED_SCHEMES, NEEDS_JUDGMENT } from "./registry.js";
import { attachSourceRows, writeSourceRowSlices } from "./source-row.js";

// Load the canonical claims tables (claims-schema.sql) from corpus.duckdb and reconstruct
// the in-memory claim shape detectors read. members/enrollment + overlay tables are read by
// buildContext(corpusDb) directly, so this returns {claims} only.
async function loadCorpusFromDb(db) {
  const [claims, lines, dx] = await Promise.all([
    query("SELECT * FROM claims", {}, { db }),
    query("SELECT * FROM claim_lines ORDER BY claim_id, line_no", {}, { db }),
    query("SELECT * FROM claim_dx ORDER BY claim_id, dx_seq", {}, { db }),
  ]);
  // duckdb -json serializes VARCHAR[] as its own list-literal string ("[59, FA]"), not a real
  // JSON array — elements are unquoted, so parse the literal directly rather than via JSON.parse.
  const arr = (v) =>
    Array.isArray(v)
      ? v
      : typeof v === "string"
        ? v
            .slice(1, -1)
            .split(", ")
            .filter(Boolean)
            .map((s) => s.replace(/^['"]|['"]$/g, ""))
        : [];
  const linesBy = new Map();
  for (const l of lines) {
    const a = linesBy.get(l.claim_id) || [];
    a.push({
      hcpcs: l.hcpcs,
      units: l.units,
      dosFrom: l.dos_from,
      dosTo: l.dos_to,
      allowedAmount: l.allowed_amount,
      modifiers: arr(l.modifiers),
      pos: l.pos,
    });
    linesBy.set(l.claim_id, a);
  }
  const dxBy = new Map();
  for (const d of dx) {
    const a = dxBy.get(d.claim_id) || [];
    a.push({ code: d.dx_code });
    dxBy.set(d.claim_id, a);
  }
  const out = claims.map((c) => ({
    claimId: c.claim_id,
    billingNpi: c.billing_npi,
    renderingNpi: c.rendering_npi,
    referringNpi: c.referring_npi,
    beneId: c.bene_id,
    specialty: c.specialty,
    adjudication: { status: c.adjudication_status, cobPaidAmount: c.cob_paid_amount },
    frequencyCode: c.frequency_code,
    lines: linesBy.get(c.claim_id) || [],
    diagnoses: dxBy.get(c.claim_id) || [],
  }));
  return { claims: out };
}

async function main() {
  const corpusDb = process.argv[2] && path.resolve(process.argv[2]);
  if (!corpusDb || !corpusDb.endsWith(".duckdb")) {
    console.error("usage: node scripts/screen.js <corpus.duckdb> [quarter] [lob]");
    process.exit(1);
  }
  const q = (process.argv[3] || "2026q3").toLowerCase();
  const lob = (process.argv[4] || "medicare").toLowerCase();
  const { claims } = await loadCorpusFromDb(corpusDb);
  console.log(`Screening ${claims.length} claims (lob=${lob}) against ${q} reference tables…`);

  const ctx = await buildContext(q, claims, corpusDb, lob);
  const result = await runSweep(claims, ctx);
  const outDir = resolveOutDir();
  mkdirSync(outDir, { recursive: true });
  // statistical detectors (D7): drop the exact cohort slice into the run dir so a reviewer can
  // recompute median/MAD/z themselves; tags evidence.cohortFile before serialization.
  await writeCohortSlices(result, ctx, outDir);
  // table-backed detectors: attach the literal triggering reference-table row + write it as a
  // one-row CSV sibling so the data point is verifiable inline (no 1.3M-row file hunt).
  await attachSourceRows(result, ctx);
  await writeSourceRowSlices(result, ctx, outDir);
  const json = JSON.stringify(result, null, 2);
  // referrals.json is the canonical, progressively-enriched file the renderers read; the .detect
  // snapshot is the immutable detect-stage record the adjudicate/synthesize stages and eval grade against.
  writeFileSync(path.join(outDir, "referrals.json"), json);
  writeFileSync(path.join(outDir, "referrals.detect.json"), json);
  // Slim index: just enough for the workflow to drive control flow + audit $ figures, without
  // shipping 40–80KB of evidence/citation/claimContext through a model's StructuredOutput call.
  // Downstream agents read full findings from disk via jq + (ridx, fidx).
  const index = {
    // meta carries the registry-derived detector roster so the sandboxed Workflow (no fs/import)
    // can read which detectors need LLM adjudication and which schemes are already covered.
    meta: { ...result.meta, needsJudgment: [...NEEDS_JUDGMENT], coveredSchemes: COVERED_SCHEMES },
    referrals: result.referrals.map((r, ridx) => ({
      npi: r.npi,
      ridx,
      schemes: r.schemes,
      exposureUsd: r.exposureUsd,
      recoverableUsd: r.recoverableUsd,
      statisticalEstimateUsd: r.statisticalEstimateUsd,
      enrichment: { registryStatus: r.enrichment?.registryStatus, note: r.enrichment?.note },
      findings: r.findings.map((f, fidx) => ({
        fidx,
        detectorId: f.detectorId,
        exposureUsd: f.exposureUsd,
      })),
    })),
  };
  writeFileSync(path.join(outDir, "referrals.index.json"), JSON.stringify(index));

  console.log(
    `\nout/referrals.json — ${result.meta.referralCount} referrals, $${result.meta.totalExposureUsd} exposure ` +
      `(${result.meta.gate.findings} findings kept, ${result.meta.gate.droppedAtGate} dropped at gate)`,
  );
  for (const r of result.referrals) {
    console.log(
      `  ${r.npi}  ${r.confidence.padEnd(6)} $${String(r.exposureUsd).padStart(7)}  [${r.schemes.join(", ")}]`,
    );
  }
}

main().catch((e) => {
  console.error(e);
  process.exit(1);
});
