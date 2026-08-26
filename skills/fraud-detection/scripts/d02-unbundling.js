// D2 — Unbundling. Two codes of an NCCI PTP (procedure-to-procedure) edit pair billed for the
// same provider + beneficiary + date of service, where the edit does not permit them together.
// PTP modifier indicator: "0" = never allowed (no modifier bypasses); "1" = allowed only when an
// appropriate bypass modifier (59 / X{EPSU} / 91) is appended to the component line. The Column 2
// code is the component that should have been bundled into the Column 1 comprehensive code, so the
// exposure is the Column 2 line's allowed amount.

const BYPASS = new Set(["59", "91", "XE", "XS", "XP", "XU"]);

export const detector = {
  id: "D2",
  tier: 1,
  scheme: "unbundling",
  label: "Unbundling",
  cat: "edit",
  needsJudgment: true,
  link: {
    label: "CMS NCCI — PTP edits",
    url: "https://www.cms.gov/medicare/coding-billing/national-correct-coding-initiative-ncci-edits",
  },
  run(claims, ctx) {
    if (!ctx.ptp) return [];
    const findings = [];
    const program = ctx.lob;
    const ptp = ctx.ptp[program];
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      const npi = c.renderingNpi || c.billingNpi;

      // group net-payable lines by DOS (PTP applies within a single date of service)
      const byDos = new Map();
      for (const l of c.lines) {
        if (!l.hcpcs || !l.dosFrom) continue;
        if (!byDos.has(l.dosFrom)) byDos.set(l.dosFrom, []);
        byDos.get(l.dosFrom).push(l);
      }

      for (const [dos, lines] of byDos) {
        for (let i = 0; i < lines.length; i++) {
          for (let j = 0; j < lines.length; j++) {
            if (i === j) continue;
            const a = lines[i],
              b = lines[j];
            // a = Column 1 (comprehensive), b = Column 2 (component) — directional lookup
            const edit = ptp.get(`${a.hcpcs}|${b.hcpcs}`);
            if (!edit) continue;
            // a bypass modifier on EITHER line of the pair authorizes a mod-1 edit
            const mods = [...(a.modifiers || []), ...(b.modifiers || [])].map(String);
            const bypassed = mods.some((m) => BYPASS.has(m));
            if (edit.mod === "1" && bypassed) continue; // allowed when a bypass modifier is present
            findings.push({
              detectorId: "D2",
              npi,
              scheme: "unbundling",
              claimIds: [c.claimId],
              citation: {
                rule: `NCCI PTP edit (${program}) — ${edit.rationale || "column1/column2"} (modifier indicator ${edit.mod})`,
                ruleVersion: ctx.quarter,
                hcpcs: b.hcpcs, // the component code that should have been bundled
                dos,
                computed: 1, // one disallowed pair billed together
                threshold: 0, // none allowed
              },
              exposureUsd: Math.round((b.allowedAmount || 0) * 100) / 100,
              evidence: {
                column1: a.hcpcs,
                column2: b.hcpcs,
                modifierIndicator: edit.mod,
                rationale: edit.rationale,
                bypassModifierPresent: bypassed,
                program,
              },
            });
          }
        }
      }
    }
    return findings;
  },
};
