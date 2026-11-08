// D7 — Statistical outlier (SUPPORTING, tier 2). A provider whose services-per-beneficiary ratio is a
// robust-z outlier versus their specialty cohort. The cohort distribution comes from the real CMS
// "Medicare Physician & Other Practitioners — by Provider" file (Tot_Srvcs / Tot_Benes by
// Rndrng_Prvdr_Type), so the basis is reproducible: named file, specialty cohort, n, median, MAD.
// Robust z = (value − median) / (1.4826 × MAD). Exposure is a clearly-labeled statistical ESTIMATE:
// the share of allowed dollars above the cohort-median utilization — never a hard rule allegation.
// Requires the provider's specialty on the claim; providers without it are skipped (no cohort).

import { query, refDb } from "./duck.js";

const Z_THRESHOLD = 3.5;
const MIN_COHORT = 30; // need enough peers for a stable median/MAD
const MIN_BENES = 11; // CMS suppresses provider rows under 11 benes; mirror that for cohort members

const median = (a) => {
  const s = [...a].sort((x, y) => x - y);
  const m = Math.floor(s.length / 2);
  return s.length % 2 ? s[m] : (s[m - 1] + s[m]) / 2;
};

// median + MAD of services-per-beneficiary for a specialty cohort in the by-provider table
export function cohortStats(byProvider, specialty) {
  const vals = [];
  for (const r of byProvider || []) {
    if (r.Rndrng_Prvdr_Type !== specialty) continue;
    const b = +r.Tot_Benes;
    const s = +r.Tot_Srvcs;
    if (b >= MIN_BENES && s > 0) vals.push(s / b);
  }
  if (vals.length < MIN_COHORT) return null;
  const med = median(vals);
  const mad = median(vals.map((v) => Math.abs(v - med))) || 0.0001;
  return { n: vals.length, median: med, mad };
}

// Same cohort stats but computed by DuckDB over the partb_by_provider table in reference.duckdb
// (native MEDIAN/MAD, no 1.3M-row JS load). Optional state/ruca narrow the cohort to a
// geo-adjusted peer group.
export async function cohortStatsSql(quarter, specialty, { state, ruca } = {}) {
  const preds = [`Rndrng_Prvdr_Type = $specialty`, `Tot_Benes::int >= ${MIN_BENES}`];
  if (state) preds.push(`Rndrng_Prvdr_State_Abrvtn = $state`);
  if (ruca) preds.push(`Rndrng_Prvdr_RUCA = $ruca`);
  const sql = `
    SELECT count(*) AS n, median(spb) AS median, mad(spb) AS mad
    FROM (SELECT Tot_Srvcs::double / Tot_Benes::double AS spb
          FROM partb_by_provider
          WHERE ${preds.join(" AND ")})`;
  const [r] = await query(sql, { specialty, state, ruca }, { db: refDb(quarter) });
  if (!r || Number(r.n) < MIN_COHORT) return null;
  return { n: Number(r.n), median: Number(r.median), mad: Number(r.mad) || 0.0001 };
}

// Precompute cohort stats for every specialty present in the claims corpus (called from buildContext)
// so detector.run() stays synchronous. Returns Map<specialty, {n, median, mad}>.
export async function precomputeCohorts(quarter, claims) {
  const specialties = new Set();
  for (const c of claims) if (c.specialty) specialties.add(c.specialty);
  const out = new Map();
  for (const s of specialties) {
    const stats = await cohortStatsSql(quarter, s);
    if (stats) out.set(s, stats);
  }
  return out;
}

export const detector = {
  id: "D7",
  tier: 2,
  scheme: "utilization-outlier",
  label: "Utilization outlier",
  cat: "stat",
  needsJudgment: true,
  link: {
    label: "Benchmark dataset (methodology)",
    url: "https://data.cms.gov/provider-summary-by-type-of-service/medicare-physician-other-practitioners/medicare-physician-other-practitioners-by-provider",
  },
  run(claims, ctx) {
    // ctx.cohorts is precomputed in buildContext via cohortStatsSql (DuckDB over the full 1.3M-row
    // partb_by_provider table). The legacy in-JS cohortStats() path runs only if ctx.partbByProvider
    // is loaded (transition fallback).
    const byProvider = ctx.partbByProvider;
    const cohorts = ctx.cohorts;
    if (!cohorts && !byProvider) return [];

    // aggregate net-payable claims per provider
    const prov = new Map();
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      if (!c.specialty) continue; // no specialty → cannot place in a cohort
      const npi = c.renderingNpi || c.billingNpi;
      const p = prov.get(npi) || {
        npi,
        specialty: c.specialty,
        benes: new Set(),
        srvcs: 0,
        allowed: 0,
        claimIds: [],
      };
      for (const l of c.lines || []) {
        p.srvcs += l.units || 1; // unit-weighted, to match CMS Tot_Srvcs in the cohort
        p.allowed += l.allowedAmount || 0;
      }
      if (c.beneId) p.benes.add(c.beneId);
      p.claimIds.push(c.claimId);
      prov.set(npi, p);
    }

    const findings = [];
    for (const p of prov.values()) {
      const benes = p.benes.size;
      if (!benes) continue;
      const stats = cohorts ? cohorts.get(p.specialty) : cohortStats(byProvider, p.specialty);
      if (!stats) continue;
      const value = p.srvcs / benes;
      const z = (value - stats.median) / (1.4826 * stats.mad);
      if (z < Z_THRESHOLD) continue;
      const excessFraction = Math.max(0, (value - stats.median) / value);
      const exposure = Math.round(p.allowed * excessFraction * 100) / 100;
      findings.push({
        detectorId: "D7",
        npi: p.npi,
        scheme: "utilization-outlier",
        claimIds: p.claimIds,
        citation: {
          rule: `Services-per-beneficiary ${value.toFixed(1)} vs ${p.specialty} cohort median ${stats.median.toFixed(1)} (robust z ${z.toFixed(1)})`,
          ruleVersion: ctx.quarter,
          computed: Math.round(z * 10) / 10,
          threshold: Z_THRESHOLD,
        },
        exposureUsd: exposure,
        evidence: {
          basis: "CMS Medicare Physician & Other Practitioners — by Provider",
          specialty: p.specialty,
          cohortN: stats.n,
          cohortMedian: Math.round(stats.median * 100) / 100,
          cohortMad: Math.round(stats.mad * 100) / 100,
          providerValue: Math.round(value * 100) / 100,
          note: "Statistical indicator (supporting) — exposure is an estimate above cohort-median utilization, not a rule-based overpayment.",
        },
      });
    }
    return findings;
  },
};
