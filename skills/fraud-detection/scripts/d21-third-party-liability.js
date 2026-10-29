// D21 — Third-party liability (payer of last resort). Medicaid is statutorily the payer of last
// resort (42 CFR 433.139): if a beneficiary has other primary coverage (Medicare, commercial,
// TRICARE) effective on the date of service, the claim must be billed to that primary first and
// Medicaid pays only the residual. A paid claim with no COB adjustment, for a bene whose
// enrollment shows an overlapping span in a DIFFERENT program on the DOS, is improper. The
// other-program enrollment span IS the COB record — there is no separate cob table.

export const detector = {
  id: "D21",
  tier: 1,
  scheme: "third-party-liability",
  label: "Third-party liability",
  cat: "edit",
  needsJudgment: false,
  run(claims, ctx) {
    if (ctx.lob !== "medicaid") return [];
    if (!ctx.enrollment || !ctx.enrollment.size) return [];
    const findings = [];
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      // a claim that already carries a COB adjustment (primary paid first) is compliant
      if (c.adjudication && c.adjudication.cobPaidAmount > 0) continue;
      const dos = (c.lines || []).map((l) => l.dosFrom).sort()[0];
      if (!dos) continue;
      const spans = ctx.enrollment.get(c.beneId) || [];
      const other = spans.find(
        (s) =>
          s.program !== ctx.lob && dos >= s.effectiveFrom && dos <= (s.effectiveTo || "9999-12-31"),
      );
      if (!other) continue;
      const exposure = (c.lines || []).reduce((s, l) => s + (l.allowedAmount || 0), 0);
      findings.push({
        detectorId: "D21",
        npi: c.billingNpi,
        scheme: "third-party-liability",
        claimIds: [c.claimId],
        citation: {
          rule: `Primary coverage (${other.program}) active on DOS — ${ctx.lob} is payer of last resort (42 CFR 433.139)`,
          ruleVersion: ctx.quarter,
          dos,
          computed: dos,
          threshold: other.effectiveTo,
        },
        exposureUsd: Math.round(exposure * 100) / 100,
        evidence: {
          beneId: c.beneId,
          program: ctx.lob,
          primaryProgram: other.program,
          planId: other.planId,
          effectiveFrom: other.effectiveFrom,
          effectiveTo: other.effectiveTo,
          note: "No COB adjustment on a paid claim while other-program coverage is active.",
        },
      });
    }
    return findings;
  },
};
