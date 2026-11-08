// D4 — Medical necessity. A service is billed with a diagnosis the Medicare coverage policy
// (LCD / Billing & Coding Article) EXPLICITLY lists as non-covered for that service. CMS keeps these
// lists in companion Articles; a HCPCS may be governed by several (one per MAC jurisdiction). We use
// the explicit non-covered list rather than "absent from the covered list" on purpose: the former is
// an unambiguous, defensible allegation ("policy says this dx does not support this service") and does
// not over-fire on codes that merely appear in some jurisdiction's coverage article. To stay safe we
// flag only when the billed dx is non-covered AND not covered by any governing article. Exposure =
// the line's allowed amount.

export const detector = {
  id: "D4",
  tier: 1,
  scheme: "medical-necessity",
  label: "Medical necessity",
  cat: "edit",
  needsJudgment: true,
  link: {
    label: "Medicare Coverage Database",
    url: "https://www.cms.gov/medicare-coverage-database",
  },
  run(claims, ctx) {
    const cov = ctx.coverage;
    if (!cov || !cov.hcpcToArticles.size) return [];
    const findings = [];
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      const npi = c.renderingNpi || c.billingNpi;
      const claimDx = (c.diagnoses || []).map((d) => d.code).filter(Boolean);
      if (!claimDx.length) continue;

      for (const l of c.lines) {
        if (!l.hcpcs) continue;
        const articles = cov.hcpcToArticles.get(l.hcpcs);
        if (!articles) continue; // no coverage policy governs this code — cannot assert necessity

        // covered + non-covered dx unions across all governing articles
        const covered = new Set();
        const noncovered = new Set();
        for (const a of articles) {
          for (const x of cov.coveredByArticle.get(a) || []) covered.add(x);
          for (const x of cov.noncoveredByArticle.get(a) || []) noncovered.add(x);
        }
        // a billed dx the policy explicitly lists as non-covered, and not covered anywhere
        const noncoveredHit = claimDx.filter((d) => noncovered.has(d) && !covered.has(d));
        if (!noncoveredHit.length) continue;

        findings.push({
          detectorId: "D4",
          npi,
          scheme: "medical-necessity",
          claimIds: [c.claimId],
          citation: {
            rule: `Diagnosis listed as non-covered for this service by Medicare coverage policy (${noncoveredHit.join(", ")})`,
            ruleVersion: ctx.quarter,
            hcpcs: l.hcpcs,
            dos: l.dosFrom,
            computed: noncoveredHit.length, // billed dx explicitly non-covered
            threshold: 0, // none should be
          },
          exposureUsd: Math.round((l.allowedAmount || 0) * 100) / 100,
          evidence: {
            articleIds: [...articles],
            // LCDs whose HCPCS list includes this code (lcd_x_hcpc_code) — the adjudicate stage
            // reads lcd.indication for these IDs to weigh the clinical-necessity prose. Empty when
            // no LCD governs the code (Articles alone are the policy basis then).
            lcdIds: ctx.lcdByHcpcs?.get(l.hcpcs) ?? [],
            noncoveredHit,
            claimDx,
          },
        });
      }
    }
    return findings;
  },
};
