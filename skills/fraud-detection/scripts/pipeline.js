import { gateFindings } from "./gate.js";
// Sweep pipeline (deterministic core). Runs every detector over the claims, shape-asserts each
// finding at the gate boundary, rolls findings up to provider-level referrals, dedups exposure
// across detectors so one claim line's dollars are not double-counted, and ranks by scheme breadth
// then exposure. Output is the canonical referrals.json contract — renderers (dashboard / packet /
// xlsx) and the narrative agent consume this, never the raw detectors.
//
// NOTE: this is a plain deterministic JS module, NOT a Claude Code dynamic Workflow — it makes zero
// model calls (invariant: math in code, never the model). The only LLM step is the referral
// narrative in the skill, which runs AFTER this on the returned JSON.
import { enrollmentAt } from "./reference-data.js";
import { loadDetectors } from "./registry.js";
import { resolveSource } from "./sources.js";
import { summarize } from "./summaries.js";

const round = (n) => Math.round(n * 100) / 100;

export async function runSweep(claims, ctx) {
  const detectors = await loadDetectors();
  const tierOf = new Map(detectors.map((d) => [d.id, d.tier]));

  // 1. run detectors
  const raw = [];
  for (const d of detectors) for (const f of d.run(claims, ctx)) raw.push(f);

  // 2. citation gate — deterministic recompute; only findings whose cited number reproduces survive
  const { kept: findings, dropped } = gateFindings(raw, claims, ctx);

  // attach a plain-English summary + the public-authority citation (link + on-page highlight) to each
  // surviving finding. source is Tier-1 (deterministic, from known codes); Tier-2 may upgrade it with
  // a verbatim excerpt from the page it reads.
  // Also attach the cited claims' diagnoses + line summary so the adjudicate stage has the context it
  // needs WITHOUT reading the corpus (which may be a JSON dir or corpus.duckdb — adjudicate must be
  // source-agnostic). For D13 the surgery claim isn't in claimIds, so include it via procedureClaimId.
  const byId = new Map(claims.map((c) => [c.claimId, c]));
  const claimContextOf = (id) => {
    const c = byId.get(id);
    if (!c) return { claimId: id };
    const firstDos = (c.lines || []).map((l) => l.dosFrom).sort()[0];
    return {
      claimId: id,
      enrollment: firstDos ? enrollmentAt(ctx, c.beneId, firstDos) : null,
      diagnoses: (c.diagnoses || []).map((d) => d.code),
      lines: (c.lines || []).map((l) => ({
        hcpcs: l.hcpcs,
        dos: l.dosFrom,
        units: l.units,
        modifiers: l.modifiers || [],
      })),
    };
  };
  for (const f of findings) {
    f.summary = summarize(f);
    f.source = resolveSource(f);
    // Every finding starts as a candidate; the adjudicate stage (workflow) sets confirmed/dismissed/
    // downgraded + adjudication.{reason, by}. Mechanical detectors auto-confirm there.
    f.status = "candidate";
    f.evidence = f.evidence || {};
    const ids = new Set(f.claimIds);
    if (f.evidence.procedureClaimId) ids.add(f.evidence.procedureClaimId);
    f.evidence.claimContext = [...ids].map(claimContextOf);
  }

  // 3. roll up to provider-level referrals. Exposure is deduped at the LINE level (same line flagged
  // by several detectors counts once; distinct improper lines sum) — and split by tier: tier-1 is
  // RECOVERABLE (hard rule allegation), tier-2 is a statistical ESTIMATE. We never blend them into one
  // "recovery" number, so a soft outlier estimate can't masquerade as a confirmed overpayment.
  const byNpi = new Map();
  for (const f of findings) {
    const r = byNpi.get(f.npi) || {
      npi: f.npi,
      schemes: new Set(),
      findings: [],
      perLineHard: new Map(),
      perLineEst: new Map(),
    };
    r.schemes.add(f.scheme);
    r.findings.push(f);
    const share = f.claimIds.length ? f.exposureUsd / f.claimIds.length : 0;
    const lineKey = `${f.citation.hcpcs || ""}|${f.citation.dos || ""}`;
    const bucket = tierOf.get(f.detectorId) === 1 ? r.perLineHard : r.perLineEst;
    for (const cid of f.claimIds) {
      const k = `${cid}|${lineKey}`;
      bucket.set(k, Math.max(bucket.get(k) || 0, share));
    }
    byNpi.set(f.npi, r);
  }
  const sum = (m) => round([...m.values()].reduce((s, x) => s + x, 0));

  const referrals = [...byNpi.values()]
    .map((r) => {
      const recoverableUsd = sum(r.perLineHard);
      const statisticalEstimateUsd = sum(r.perLineEst);
      return {
        npi: r.npi,
        schemes: [...r.schemes],
        schemeCount: r.schemes.size,
        findingCount: r.findings.length,
        claimIds: [...new Set(r.findings.flatMap((f) => f.claimIds))],
        // exposureUsd = combined (recoverable + estimate); the split fields keep them distinguishable
        exposureUsd: round(recoverableUsd + statisticalEstimateUsd),
        recoverableUsd,
        statisticalEstimateUsd,
        // all-deterministic (tier-1) findings → high confidence; any statistical (tier-2) → medium
        confidence: r.findings.every((f) => tierOf.get(f.detectorId) === 1) ? "high" : "medium",
        // NPPES registry status from the cached snapshot (scripts/fetch-nppes.js). 9-prefix NPIs are
        // NPPES-reserved/non-issued by definition — short-circuit to not-found regardless of cache.
        enrichment:
          ctx.nppes?.get(r.npi) ??
          (r.npi.startsWith("9")
            ? { npi: r.npi, registryStatus: "not-found", note: "reserved synthetic NPI" }
            : { npi: r.npi, registryStatus: "unknown" }),
        findings: r.findings,
      };
    })
    // multi-scheme provider ranks above single-scheme, then by recoverable (hard) dollars, then estimate
    .sort(
      (a, b) =>
        b.schemeCount - a.schemeCount ||
        b.recoverableUsd - a.recoverableUsd ||
        b.statisticalEstimateUsd - a.statisticalEstimateUsd,
    );

  // Only stamp the synthetic-data banner when EVERY billing NPI in the corpus is in the
  // NPPES-reserved 9-prefix range (i.e., a fixture set). Real payer data clears it.
  const allSyntheticNpis =
    claims.length > 0 && claims.every((c) => String(c.billingNpi || c.npi || "").startsWith("9"));

  return {
    meta: {
      disclaimer: allSyntheticNpis ? "SYNTHETIC FIXTURE DATA — NOT A REAL DETERMINATION" : "",
      language:
        "Findings describe indicators consistent with the named scheme; they are not a determination of fraud.",
      quarter: ctx.quarter,
      detectors: detectors.map((d) => d.id),
      referralCount: referrals.length,
      totalExposureUsd: round(referrals.reduce((s, r) => s + r.exposureUsd, 0)),
      recoverableUsd: round(referrals.reduce((s, r) => s + r.recoverableUsd, 0)),
      statisticalEstimateUsd: round(referrals.reduce((s, r) => s + r.statisticalEstimateUsd, 0)),
      gate: { findings: findings.length, droppedAtGate: dropped.length },
    },
    referrals,
  };
}
