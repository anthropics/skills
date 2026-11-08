// D20 — HCBS / personal-care overlap. Home- and community-based service hours billed for a
// beneficiary on a date that falls INSIDE a recorded inpatient/SNF stay for that beneficiary. The
// bene cannot be at home receiving aide services and admitted to a facility on the same day, so the
// HCBS line is improper on its face. Medicaid-specific (HCBS waivers are Medicaid-only).
// HCBS/personal-care HCPCS: T1019/T1020 (personal care per 15-min/per-diem), S5125 (attendant care),
// S5130/S5135 (homemaker), G0156 (HHA aide). The inpatient-stay feed comes from the payer's own
// institutional claims / ADT, surfaced as ctx.inpatientStays (overlay-merged in buildContext).

const HCBS = new Set(["T1019", "T1020", "S5125", "S5130", "S5135", "G0156"]);

export const detector = {
  id: "D20",
  tier: 1,
  scheme: "hcbs-overlap",
  label: "HCBS / inpatient overlap",
  cat: "edit",
  needsJudgment: false,
  run(claims, ctx) {
    const stays = ctx.inpatientStays;
    if (!stays || !stays.size) return [];
    const findings = [];
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      const stay = stays.get(c.beneId);
      if (!stay) continue;
      for (const l of c.lines || []) {
        if (!HCBS.has(l.hcpcs)) continue;
        if (l.dosFrom < stay.admitDate || l.dosFrom > stay.dischargeDate) continue;
        findings.push({
          detectorId: "D20",
          npi: c.billingNpi,
          scheme: "hcbs-overlap",
          claimIds: [c.claimId],
          citation: {
            rule: `HCBS service ${l.hcpcs} billed during inpatient stay ${stay.admitDate}–${stay.dischargeDate}`,
            ruleVersion: ctx.quarter,
            hcpcs: l.hcpcs,
            dos: l.dosFrom,
            computed: l.dosFrom,
            threshold: stay.dischargeDate,
          },
          exposureUsd: l.allowedAmount || 0,
          evidence: {
            beneId: c.beneId,
            admitDate: stay.admitDate,
            dischargeDate: stay.dischargeDate,
            facilityNpi: stay.facilityNpi,
            note: "Beneficiary was inpatient on the HCBS date of service — home-based aide hours cannot have been rendered.",
          },
        });
      }
    }
    return findings;
  },
};
