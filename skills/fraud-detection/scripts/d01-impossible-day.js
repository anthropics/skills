// D1 — Impossible day. Units exceed the NCCI MUE per-day cap.
//   MAI 2/3 = date-of-service edits → sum units per (renderingNpi, DOS, HCPCS) before comparing.
//   MAI 1   = line edit → evaluate each line on its own (the 41 MAI-1 codes carry huge drug-unit
//             caps; summing legitimately separate lines manufactures false positives).
// Cites the MUE MAI value + computed units vs cap. Skips non-net-payable (denied/reversed) lines.

export const detector = {
  id: "D1",
  tier: 1,
  scheme: "impossible-day",
  label: "Impossible day",
  cat: "edit",
  needsJudgment: false,
  link: {
    label: "CMS NCCI — MUE tables",
    url: "https://www.cms.gov/medicare/coding-billing/national-correct-coding-initiative-ncci-edits/medicare-ncci-medically-unlikely-edits",
  },
  run(claims, ctx) {
    const findings = [];
    const dosGroups = new Map(); // key -> aggregate for MAI 2/3
    const program = ctx.lob;
    const mue = ctx.mue[program];

    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue; // net-payable only
      for (const l of c.lines) {
        const m = mue.get(l.hcpcs);
        if (!m || !m.mue) continue;
        if (m.mai === 1) {
          if (l.units > m.mue) {
            const perUnit = l.units ? (l.allowedAmount || 0) / l.units : 0;
            findings.push(
              mkFinding(
                ctx,
                c.renderingNpi,
                [c.claimId],
                l.hcpcs,
                l.dosFrom,
                m,
                l.units,
                (l.units - m.mue) * perUnit,
                program,
              ),
            );
          }
        } else {
          const key = `${c.renderingNpi}|${l.dosFrom}|${l.hcpcs}`;
          const g = dosGroups.get(key) || {
            npi: c.renderingNpi,
            dos: l.dosFrom,
            hcpcs: l.hcpcs,
            m,
            units: 0,
            allowed: 0,
            claimIds: new Set(),
          };
          g.units += l.units;
          g.allowed += l.allowedAmount || 0;
          g.claimIds.add(c.claimId);
          dosGroups.set(key, g);
        }
      }
    }

    for (const g of dosGroups.values()) {
      if (g.units > g.m.mue) {
        const perUnit = g.units ? g.allowed / g.units : 0;
        // MAI-2 is an "absolute" per-day edit: the whole over-cap line is non-payable, so exposure
        // is the full allowed amount. MAI-3 (clinical) is appealable → expose only the excess units.
        const exposure = g.m.mai === 2 ? g.allowed : (g.units - g.m.mue) * perUnit;
        findings.push(
          mkFinding(ctx, g.npi, [...g.claimIds], g.hcpcs, g.dos, g.m, g.units, exposure, program),
        );
      }
    }
    return findings;
  },
};

function mkFinding(ctx, npi, claimIds, hcpcs, dos, m, computed, exposure, program) {
  const tier =
    m.mai === 2 ? "absolute per-day cap" : m.mai === 1 ? "per-line cap" : "per-day clinical cap";
  return {
    detectorId: "D1",
    npi,
    scheme: "impossible-day",
    claimIds,
    citation: {
      rule: `NCCI MUE (${program}) ${m.mai ? `MAI-${m.mai} ` : ""}(${tier})`,
      ruleVersion: ctx.quarter,
      hcpcs,
      dos,
      computed, // units billed
      threshold: m.mue, // the cap
    },
    exposureUsd: Math.round(exposure * 100) / 100,
    evidence: { excessUnits: computed - m.mue, mai: m.mai, program },
  };
}
