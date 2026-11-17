// D18 — Ownership ring (SUPPORTING, tier 2). Common owners across multiple corpus providers — the
// asset-shielding / shell-entity pattern. Builds an owner→NPI index from the four CMS PECOS
// "All Owners" files (hospice / hospital / HHA / SNF) joined to ffs_enrollment on ENROLLMENT ID,
// and flags any owner Associate ID linked to ≥2 NPIs in the corpus. Exposure is $0 — supporting
// network signal; the finding's npi is the first linked NPI, evidence lists the full ring.

import { query, refDb } from "./duck.js";

const OWNER_TABLES = [
  "owners_hospice",
  "owners_hospital",
  "owners_home_health_agency",
  "owners_skilled_nursing_facility",
];

// Precompute owner→corpus-NPI index. Queries UNION ALL of the four owners_* tables joined to
// ffs_enrollment (ENROLLMENT ID ↔ ENRLMT_ID) for the corpus NPIs only. Returns
// Map<ownerAssociateId, { ownerName, npis:Set<string> }>.
export async function precomputeOwnerIndex(quarter, npis) {
  const out = new Map();
  if (!npis || !npis.size) return out;
  const inList = [...npis].map((n) => `'${String(n).replace(/'/g, "''")}'`).join(",");
  const union = OWNER_TABLES.map(
    (t) =>
      `SELECT "ENROLLMENT ID" AS enrlmt_id, "ASSOCIATE ID - OWNER" AS owner_id,
              coalesce("ORGANIZATION NAME - OWNER",
                       trim(coalesce("FIRST NAME - OWNER",'') || ' ' || coalesce("LAST NAME - OWNER",''))) AS owner_name
       FROM ${t}`,
  ).join(" UNION ALL ");
  const sql = `
    SELECT e.NPI AS npi, o.owner_id, o.owner_name
    FROM (${union}) o
    JOIN ffs_enrollment e ON e.ENRLMT_ID = o.enrlmt_id
    WHERE e.NPI IN (${inList}) AND o.owner_id IS NOT NULL`;
  const rows = await query(sql, {}, { db: refDb(quarter) });
  for (const r of rows) {
    const e = out.get(r.owner_id) || { ownerName: r.owner_name, npis: new Set() };
    e.npis.add(String(r.npi));
    if (!e.ownerName && r.owner_name) e.ownerName = r.owner_name;
    out.set(r.owner_id, e);
  }
  return out;
}

export const detector = {
  id: "D18",
  tier: 2,
  scheme: "ownership-ring",
  label: "Common ownership",
  cat: "stat",
  needsJudgment: false,
  run(claims, ctx) {
    const idx = ctx.ownerIndex;
    if (!idx || !idx.size) return [];

    // map NPI → one corpus claimId so the finding cites a real claim
    const claimByNpi = new Map();
    for (const c of claims)
      if (!claimByNpi.has(c.billingNpi)) claimByNpi.set(c.billingNpi, c.claimId);

    const findings = [];
    for (const [ownerId, e] of idx) {
      if (e.npis.size < 2) continue;
      const linked = [...e.npis];
      const npi = linked[0];
      const claimId = claimByNpi.get(npi);
      if (!claimId) continue;
      findings.push({
        detectorId: "D18",
        npi,
        scheme: "ownership-ring",
        claimIds: [claimId],
        citation: {
          rule: `Common owner "${e.ownerName || ownerId}" controls ${e.npis.size} corpus providers (PECOS All Owners)`,
          ruleVersion: ctx.quarter,
          computed: e.npis.size,
          threshold: 2,
        },
        exposureUsd: 0, // supporting network signal only
        evidence: {
          basis: "CMS PECOS Ownership — Hospice/Hospital/HHA/SNF All Owners",
          ownerAssociateId: ownerId,
          ownerName: e.ownerName || null,
          linkedNpis: linked,
          note: "Supporting signal only — shared ownership across multiple corpus billers.",
        },
      });
    }
    return findings;
  },
};
