// D16 — Prescribing outlier (SUPPORTING, tier 2). The corpus carries no Part D claims, so this is
// BENCHMARK-ONLY: for each rendering NPI in the corpus, look up their row in the CMS "Medicare
// Part D Prescribers — by Provider" file and compute a robust-z on Opioid_Prscrbr_Rate vs their
// Prscrbr_Type cohort. Exposure is $0 — there are no corpus dollars to allege; the finding is a
// pure supporting signal that strengthens co-occurring D-series referrals (the canonical pill-mill
// flag). Citation cites the published opioid rate vs cohort median.

import { query, refDb } from "./duck.js";

const Z_THRESHOLD = 3.5;
const MIN_COHORT = 30;

// median + MAD of Opioid_Prscrbr_Rate for a Prscrbr_Type cohort in partd_by_provider.
async function cohortStatsSql(quarter, specialty) {
  const sql = `
    SELECT count(*) AS n, median(r) AS median, mad(r) AS mad
    FROM (SELECT Opioid_Prscrbr_Rate::double AS r
          FROM partd_by_provider
          WHERE Prscrbr_Type = $specialty AND Opioid_Prscrbr_Rate IS NOT NULL AND Opioid_Prscrbr_Rate <> '')`;
  const [r] = await query(sql, { specialty }, { db: refDb(quarter) });
  if (!r || Number(r.n) < MIN_COHORT) return null;
  return { n: Number(r.n), median: Number(r.median), mad: Number(r.mad) || 0.0001 };
}

// Precompute the per-NPI Part D row + per-specialty cohort stats for every rendering NPI in the
// corpus (called from buildContext). Returns { rows: Map<npi,row>, cohorts: Map<specialty,stats> }.
export async function precomputePartdLookups(quarter, claims) {
  const npis = new Set();
  for (const c of claims) if (c.renderingNpi) npis.add(c.renderingNpi);
  const rows = new Map();
  const specialties = new Set();
  if (npis.size) {
    const inList = [...npis].map((n) => `'${String(n).replace(/'/g, "''")}'`).join(",");
    const hits = await query(
      `SELECT PRSCRBR_NPI, Prscrbr_Type, Opioid_Prscrbr_Rate, Opioid_Tot_Clms, Tot_Clms
       FROM partd_by_provider WHERE PRSCRBR_NPI IN (${inList})`,
      {},
      { db: refDb(quarter) },
    );
    for (const r of hits) {
      rows.set(String(r.PRSCRBR_NPI), r);
      if (r.Prscrbr_Type) specialties.add(r.Prscrbr_Type);
    }
  }
  const cohorts = new Map();
  for (const s of specialties) {
    const stats = await cohortStatsSql(quarter, s);
    if (stats) cohorts.set(s, stats);
  }
  return { rows, cohorts };
}

export const detector = {
  id: "D16",
  tier: 2,
  scheme: "prescribing-outlier",
  label: "Opioid prescribing outlier",
  cat: "stat",
  needsJudgment: false,
  run(claims, ctx) {
    const rows = ctx.partdRows;
    const cohorts = ctx.partdCohorts;
    if (!rows || !rows.size || !cohorts) return [];

    // map each rendering NPI to its corpus claimIds so the finding cites real corpus claims
    const claimIdsByNpi = new Map();
    for (const c of claims) {
      const npi = c.renderingNpi;
      if (!npi || !rows.has(npi)) continue;
      (claimIdsByNpi.get(npi) || claimIdsByNpi.set(npi, []).get(npi)).push(c.claimId);
    }

    const findings = [];
    for (const [npi, r] of rows) {
      const rate = Number(r.Opioid_Prscrbr_Rate);
      if (!Number.isFinite(rate)) continue;
      const stats = cohorts.get(r.Prscrbr_Type);
      if (!stats) continue;
      const z = (rate - stats.median) / (1.4826 * stats.mad);
      if (z < Z_THRESHOLD) continue;
      const ids = claimIdsByNpi.get(npi) || [];
      if (!ids.length) continue; // gate requires claimIds; skip if NPI somehow not in corpus
      findings.push({
        detectorId: "D16",
        npi,
        scheme: "prescribing-outlier",
        claimIds: ids,
        citation: {
          rule: `Part D opioid prescribing rate ${rate.toFixed(1)} vs ${r.Prscrbr_Type} cohort median ${stats.median.toFixed(1)} (robust z ${z.toFixed(1)})`,
          ruleVersion: ctx.quarter,
          computed: Math.round(z * 10) / 10,
          threshold: Z_THRESHOLD,
        },
        exposureUsd: 0, // benchmark-only; no corpus Part D dollars to allege
        evidence: {
          basis: "CMS Medicare Part D Prescribers — by Provider",
          specialty: r.Prscrbr_Type,
          opioidPrscrbrRate: rate,
          opioidTotClms: Number(r.Opioid_Tot_Clms) || null,
          totClms: Number(r.Tot_Clms) || null,
          cohortN: stats.n,
          cohortMedian: Math.round(stats.median * 100) / 100,
          cohortMad: Math.round(stats.mad * 100) / 100,
          note: "Supporting signal only — published Part D benchmark, not a corpus-dollar allegation.",
        },
      });
    }
    return findings;
  },
};
