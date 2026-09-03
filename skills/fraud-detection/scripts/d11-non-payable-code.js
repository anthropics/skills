// D11 — Non-payable / discontinued code. A line for a code that is never separately payable
// to a practitioner: rationale "Drug discontinued" / "Oral Medication; Not Payable" /
// "Compounded Drug Policy", or an absolute (MUE MAI-2) cap of 0. Billing ANY quantity is per se
// improper — distinct from D1's "exceeds a positive cap".
// IMPORTANT: does NOT fire on bare MUE=0 — ~2,529 of those are routine "CMS Policy" bundling
// denials, not fraud (see DESIGN.md §4). lib.nonPayableCodes() applies the correct filter (~112 codes).
import { nonPayableCodes } from "./reference-data.js";

export const detector = {
  id: "D11",
  tier: 1,
  scheme: "non-payable-code",
  label: "Non-payable code",
  cat: "edit",
  needsJudgment: false,
  link: {
    label: "HCPCS Level II — status",
    url: "https://www.cms.gov/medicare/coding-billing/healthcare-common-procedure-system",
  },
  run(claims, ctx) {
    const findings = [];
    const program = ctx.lob;
    const np = ctx.nonPayable?.[program] || nonPayableCodes(ctx.mue[program]);
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      for (const l of c.lines) {
        const v = np.get(l.hcpcs);
        if (!v) continue;
        findings.push({
          detectorId: "D11",
          npi: c.billingNpi,
          scheme: "non-payable-code",
          claimIds: [c.claimId],
          citation: {
            rule: `Non-payable code — ${v.rationale}${v.mai === 2 ? " (MUE MAI-2 absolute cap 0)" : ""}`,
            ruleVersion: ctx.quarter,
            hcpcs: l.hcpcs,
            dos: l.dosFrom,
            computed: l.units, // any quantity is improper
            threshold: 0,
          },
          exposureUsd: Math.round((l.allowedAmount || 0) * 100) / 100,
          evidence: { rationale: v.rationale, mai: v.mai, program },
        });
      }
    }
    return findings;
  },
};
