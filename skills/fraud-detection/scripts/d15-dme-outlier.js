// D15 — DME outlier (SUPPORTING, tier 2). DMEPOS is the highest-FWA-rate Medicare category. A
// supplier whose claims-per-beneficiary on DME lines is a robust-z outlier vs their specialty
// cohort in the CMS "Medicare DMEPOS — by Supplier" file (Tot_Suplr_Clms / Tot_Suplr_Benes by
// Suplr_Prvdr_Spclty_Desc). Same robust-z math as D7; same exposure ESTIMATE (share of allowed
// dollars above cohort-median utilization). DME lines = HCPCS prefix E/K/L or A4xxx–A9xxx.

import { query, refDb } from "./duck.js";

const Z_THRESHOLD = 3.5;
const MIN_COHORT = 30; // need enough peers for a stable median/MAD
const MIN_BENES = 11; // CMS suppresses provider rows under 11 benes; mirror that for cohort members

const isDme = (h) => /^[EKL]/.test(h) || /^A[4-9]/.test(h);

// median + MAD of claims-per-beneficiary for a DMEPOS supplier-specialty cohort, via DuckDB
// over the dmepos_by_supplier table (native MEDIAN/MAD; no full-table JS load).
export async function cohortStatsSql(quarter, specialty) {
  const sql = `
    SELECT count(*) AS n, median(cpb) AS median, mad(cpb) AS mad
    FROM (SELECT Tot_Suplr_Clms::double / Tot_Suplr_Benes::double AS cpb
          FROM dmepos_by_supplier
          WHERE Suplr_Prvdr_Spclty_Desc = $specialty AND Tot_Suplr_Benes::int >= ${MIN_BENES})`;
  const [r] = await query(sql, { specialty }, { db: refDb(quarter) });
  if (!r || Number(r.n) < MIN_COHORT) return null;
  return { n: Number(r.n), median: Number(r.median), mad: Number(r.mad) || 0.0001 };
}

// Precompute cohort stats for every specialty present on DME-carrying claims (called from
// buildContext) so detector.run() stays synchronous. Returns Map<specialty, {n, median, mad}>.
export async function precomputeDmeCohorts(quarter, claims) {
  const specialties = new Set();
  for (const c of claims)
    if (c.specialty && (c.lines || []).some((l) => isDme(l.hcpcs))) specialties.add(c.specialty);
  const out = new Map();
  for (const s of specialties) {
    const stats = await cohortStatsSql(quarter, s);
    if (stats) out.set(s, stats);
  }
  return out;
}

export const detector = {
  id: "D15",
  tier: 2,
  scheme: "dme-outlier",
  label: "DME outlier",
  cat: "stat",
  needsJudgment: false,
  run(claims, ctx) {
    const cohorts = ctx.dmeCohorts;
    if (!cohorts || !cohorts.size) return [];

    // aggregate net-payable DME lines per supplier (billingNpi — DME suppliers bill, not render)
    const prov = new Map();
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      if (!c.specialty) continue;
      const dme = (c.lines || []).filter((l) => isDme(l.hcpcs));
      if (!dme.length) continue;
      const npi = c.billingNpi;
      const p = prov.get(npi) || {
        npi,
        specialty: c.specialty,
        benes: new Set(),
        clms: 0,
        allowed: 0,
        claimIds: [],
      };
      p.clms += 1; // CMS Tot_Suplr_Clms is a claim count, not line/unit count
      for (const l of dme) p.allowed += l.allowedAmount || 0;
      if (c.beneId) p.benes.add(c.beneId);
      p.claimIds.push(c.claimId);
      prov.set(npi, p);
    }

    const findings = [];
    for (const p of prov.values()) {
      const benes = p.benes.size;
      if (!benes) continue;
      const stats = cohorts.get(p.specialty);
      if (!stats) continue;
      const value = p.clms / benes;
      const z = (value - stats.median) / (1.4826 * stats.mad);
      if (z < Z_THRESHOLD) continue;
      const excessFraction = Math.max(0, (value - stats.median) / value);
      const exposure = Math.round(p.allowed * excessFraction * 100) / 100;
      findings.push({
        detectorId: "D15",
        npi: p.npi,
        scheme: "dme-outlier",
        claimIds: p.claimIds,
        citation: {
          rule: `DME claims-per-beneficiary ${value.toFixed(1)} vs ${p.specialty} cohort median ${stats.median.toFixed(1)} (robust z ${z.toFixed(1)})`,
          ruleVersion: ctx.quarter,
          computed: Math.round(z * 10) / 10,
          threshold: Z_THRESHOLD,
        },
        exposureUsd: exposure,
        evidence: {
          basis: "CMS Medicare DMEPOS — by Supplier",
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
