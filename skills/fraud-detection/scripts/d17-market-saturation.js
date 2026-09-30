// D17 — Market saturation (SUPPORTING, tier 2). CMS's own program-integrity dataset: counties
// where provider density per beneficiary far exceeds need are classic fraud-ring territory. Claims
// lack a county field, so we use the provider's NPPES practice-address state and check the
// market_saturation_county table for that state + a service-type mapped from the corpus HCPCS
// category. Flag where number_of_providers_description = "High" OR a moratorium is in effect.
// Exposure is $0 — pure supporting context that strengthens co-occurring D-series referrals.

import { query, refDb } from "./duck.js";

// Coarse HCPCS-prefix → CMS market-saturation type_of_service. Only the categories CMS publishes.
function serviceType(hcpcs) {
  if (/^[EKL]/.test(hcpcs) || /^A[4-9]/.test(hcpcs)) return "Durable Medical Equipment";
  if (/^A0/.test(hcpcs)) return "Ambulance (Emergency & Non-Emergency)";
  if (/^G01[56]/.test(hcpcs) || /^G027[79]/.test(hcpcs)) return "Home Health";
  if (/^97/.test(hcpcs)) return "Physical & Occupational Therapy";
  if (/^8[0-9]{4}$/.test(hcpcs)) return "Clinical Laboratory (Billing Independently)";
  return null;
}

// Precompute the saturation row for every (state, service-type) the corpus touches. Returns
// Map<"state|type", row> containing only rows CMS itself flagged High / under moratorium.
export async function precomputeSaturation(quarter, claims, nppes) {
  const keys = new Set();
  for (const c of claims) {
    const npi = c.billingNpi;
    const rec = nppes && nppes.get && nppes.get(npi);
    const st = rec && rec.state;
    if (!st) continue;
    for (const l of c.lines || []) {
      const t = serviceType(l.hcpcs);
      if (t) keys.add(`${st}|${t}`);
    }
  }
  const out = new Map();
  for (const k of keys) {
    const [st, t] = k.split("|");
    const rows = await query(
      `SELECT state, county, type_of_service, number_of_providers, average_number_of_users_per_provider,
              number_of_providers_description, moratorium
       FROM market_saturation_county
       WHERE state = $st AND type_of_service = $t
         AND (number_of_providers_description = 'High' OR (moratorium IS NOT NULL AND trim(moratorium) <> ''))
       LIMIT 1`,
      { st, t },
      { db: refDb(quarter) },
    );
    if (rows.length) out.set(k, rows[0]);
  }
  return out;
}

export const detector = {
  id: "D17",
  tier: 2,
  scheme: "market-saturation",
  label: "Market saturation",
  cat: "stat",
  needsJudgment: false,
  run(claims, ctx) {
    const sat = ctx.saturation;
    const nppes = ctx.nppes;
    if (!sat || !sat.size || !nppes) return [];

    // one finding per (provider, service-type) that maps to a CMS-flagged saturation row
    const seen = new Set();
    const findings = [];
    for (const c of claims) {
      const npi = c.billingNpi;
      const rec = nppes.get && nppes.get(npi);
      const st = rec && rec.state;
      if (!st) continue;
      for (const l of c.lines || []) {
        const t = serviceType(l.hcpcs);
        if (!t) continue;
        const row = sat.get(`${st}|${t}`);
        if (!row) continue;
        const k = `${npi}|${t}`;
        if (seen.has(k)) continue;
        seen.add(k);
        const moratorium = row.moratorium && String(row.moratorium).trim();
        findings.push({
          detectorId: "D17",
          npi,
          scheme: "market-saturation",
          claimIds: [c.claimId],
          citation: {
            rule: `CMS Market Saturation — ${t} in ${st} flagged ${moratorium ? "under enrollment moratorium" : '"High" provider density'}`,
            ruleVersion: ctx.quarter,
            computed: row.number_of_providers_description || moratorium,
            threshold: "High",
          },
          exposureUsd: 0, // supporting context only
          evidence: {
            basis: "CMS Market Saturation & Utilization — State-County",
            state: st,
            county: row.county,
            typeOfService: t,
            numberOfProviders: row.number_of_providers,
            avgUsersPerProvider: row.average_number_of_users_per_provider,
            providersDescription: row.number_of_providers_description,
            moratorium: moratorium || null,
            note: "Supporting signal only — provider operates in a CMS-flagged saturated market.",
          },
        });
      }
    }
    return findings;
  },
};
