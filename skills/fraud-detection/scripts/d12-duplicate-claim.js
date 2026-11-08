// D12 — Duplicate service line. The same line billed more than once: identical
// (renderingNpi, beneId, HCPCS, modifiers, DOS, units), whether across separate claims or repeated
// within one claim. Exposure = the duplicate (extra) allowed amount: total minus the one payable copy.
// Repeat/bilateral modifiers (76, 77, 91, 50) legitimize an identical line and are excluded.

const REPEAT_MODS = new Set(["76", "77", "91", "50"]);

export const detector = {
  id: "D12",
  tier: 1,
  scheme: "duplicate-claim",
  label: "Duplicate claim",
  cat: "edit",
  needsJudgment: false,
  link: {
    label: "Medicare Claims Processing Manual ch.1",
    url: "https://www.cms.gov/regulations-and-guidance/guidance/manuals/downloads/clm104c01.pdf",
  },
  run(claims, ctx) {
    const seen = new Map();
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      // 837 claim frequency: 1=original, 7=replacement, 8=void. Replacement/void legitimately
      // resubmit identical lines after voiding the original — excluding them avoids false duplicates.
      const freq = c.frequencyCode || "1";
      if (freq === "7" || freq === "8") continue;
      for (const l of c.lines) {
        const mods = (l.modifiers || []).map(String);
        // repeat/bilateral modifiers legitimize an identical line — not a duplicate
        if (mods.some((m) => REPEAT_MODS.has(m))) continue;
        const key = [c.renderingNpi, c.beneId, l.hcpcs, mods.join("+"), l.dosFrom, l.units].join(
          "|",
        );
        const e = seen.get(key) || {
          npi: c.renderingNpi,
          hcpcs: l.hcpcs,
          dos: l.dosFrom,
          copies: 0,
          claimIds: new Set(),
          allowed: 0,
        };
        e.copies += 1; // count every occurrence, even two identical lines on one claim
        e.claimIds.add(c.claimId);
        e.allowed += l.allowedAmount || 0;
        seen.set(key, e);
      }
    }
    const findings = [];
    for (const e of seen.values()) {
      const n = e.copies;
      if (n > 1) {
        const dupExposure = (e.allowed * (n - 1)) / n; // all but one copy
        findings.push({
          detectorId: "D12",
          npi: e.npi,
          scheme: "duplicate-claim",
          claimIds: [...e.claimIds],
          citation: {
            rule: "Duplicate service line (same NPI/bene/HCPCS/modifier/DOS/units)",
            ruleVersion: ctx.quarter,
            hcpcs: e.hcpcs,
            dos: e.dos,
            computed: n, // identical copies billed
            threshold: 1, // only one is payable
          },
          exposureUsd: Math.round(dupExposure * 100) / 100,
          evidence: { copies: n, distinctClaims: e.claimIds.size },
        });
      }
    }
    return findings;
  },
};
