// D13 — Global-surgical-period violation. An E/M visit billed within a procedure's 010/090-day
// global period (same provider + beneficiary) WITHOUT modifier 24/25/57. The global package already
// pays for routine pre/post-op E/M; an unmodified E/M inside the window is separately-billed and
// improper. Self-citing from the PFS global-period indicator.

const EM = /^992(0[2-5]|1[1-5]|8[1-5])$/; // office new/established + ED E/M
const BYPASS = new Set(["24", "25", "57"]);
const daysBetween = (a, b) => (Date.parse(b) - Date.parse(a)) / 86400000;

export const detector = {
  id: "D13",
  tier: 1,
  scheme: "global-period-violation",
  label: "Global period",
  cat: "edit",
  needsJudgment: true,
  link: {
    label: "CMS Global Surgery booklet",
    url: "https://www.cms.gov/files/document/mln907166-global-surgery-booklet.pdf",
  },
  run(claims, ctx) {
    const pfs = ctx.pfs;
    const groups = new Map(); // renderingNpi|beneId -> { procs:[], ems:[] }
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      const key = `${c.renderingNpi}|${c.beneId}`;
      const g = groups.get(key) || { procs: [], ems: [] };
      for (const l of c.lines) {
        const p = pfs.get(l.hcpcs);
        if (p && (p.globalDays === "010" || p.globalDays === "090")) {
          g.procs.push({
            hcpcs: l.hcpcs,
            dos: l.dosFrom,
            days: Number(p.globalDays),
            claimId: c.claimId,
          });
        }
        if (EM.test(l.hcpcs)) g.ems.push({ line: l, claimId: c.claimId });
      }
      groups.set(key, g);
    }

    const findings = [];
    for (const [key, g] of groups) {
      const npi = key.split("|")[0];
      for (const em of g.ems) {
        const mods = new Set(em.line.modifiers || []);
        if ([...BYPASS].some((m) => mods.has(m))) continue;
        const hit = g.procs.find((p) => {
          const d = daysBetween(p.dos, em.line.dosFrom);
          // major-surgery (090) global includes the 1 pre-operative day; minor (010) does not
          const lower = p.days === 90 ? -1 : 0;
          return d >= lower && d <= p.days;
        });
        if (hit) {
          findings.push({
            detectorId: "D13",
            npi,
            scheme: "global-period-violation",
            claimIds: [em.claimId], // dollars belong to the E/M line only; proc claim is in evidence
            citation: {
              rule: `E/M within the ${hit.days}-day global period of ${hit.hcpcs} without modifier 24/25/57`,
              ruleVersion: ctx.quarter,
              hcpcs: em.line.hcpcs,
              dos: em.line.dosFrom,
              computed: daysBetween(hit.dos, em.line.dosFrom), // days after the procedure
              threshold: hit.days, // global period length
            },
            exposureUsd: Math.round((em.line.allowedAmount || 0) * 100) / 100,
            evidence: {
              procedure: hit.hcpcs,
              procedureDos: hit.dos,
              procedureClaimId: hit.claimId,
            },
          });
        }
      }
    }
    return findings;
  },
};
