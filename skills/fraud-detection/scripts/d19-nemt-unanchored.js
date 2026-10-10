// D19 — Unanchored NEMT (tier 1, Medicaid). Non-emergency medical transport must "anchor" to a
// covered medical service for the same beneficiary on the same date. A transport line (A0080–A0999
// ambulance, T2001–T2005 NEMT) with NO non-transport service for the same beneId on the same DOS
// anywhere in the corpus is unanchored — the canonical NEMT-fraud pattern. Pure corpus computation;
// no reference table. Exposure = the transport line's allowed amount.

const isTransport = (h) => /^A0[0-9]{3}$/.test(h) || /^T200[1-5]$/.test(h);

export const detector = {
  id: "D19",
  tier: 1,
  scheme: "nemt-unanchored",
  label: "NEMT unanchored",
  cat: "edit",
  needsJudgment: false,
  run(claims, ctx) {
    // index every (beneId, DOS) that carries a NON-transport service — the anchor set
    const anchors = new Set();
    for (const c of claims) {
      if (!c.beneId) continue;
      for (const l of c.lines || []) {
        if (!isTransport(l.hcpcs)) anchors.add(`${c.beneId}|${l.dosFrom}`);
      }
    }

    const findings = [];
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      if (!c.beneId) continue;
      for (const l of c.lines || []) {
        if (!isTransport(l.hcpcs)) continue;
        if (anchors.has(`${c.beneId}|${l.dosFrom}`)) continue; // anchored — skip
        findings.push({
          detectorId: "D19",
          npi: c.billingNpi,
          scheme: "nemt-unanchored",
          claimIds: [c.claimId],
          citation: {
            rule: "NEMT/ambulance billed with no anchoring medical service for beneficiary on the same DOS",
            ruleVersion: ctx.quarter,
            hcpcs: l.hcpcs,
            dos: l.dosFrom,
            computed: 0, // anchoring services found
            threshold: 1, // ≥1 required
          },
          exposureUsd: Math.round((l.allowedAmount || 0) * 100) / 100,
          evidence: { beneId: c.beneId, transportHcpcs: l.hcpcs },
        });
      }
    }
    return findings;
  },
};
