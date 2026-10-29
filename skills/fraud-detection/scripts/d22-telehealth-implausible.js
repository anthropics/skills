// D22 — Telehealth implausible day (tier 1). Claims lack a POS field, so use the telehealth
// modifiers (95 / GT / GQ) as the marker. For each (renderingNpi, DOS), sum typical minutes across
// time-based E/M lines billed with a telehealth modifier; flag if the day exceeds 12 hours (720
// min). Exposure = allowed dollars on the over-threshold day's telehealth E/M lines.

const TH_MODS = new Set(["95", "GT", "GQ"]);
const THRESHOLD_MIN = 720; // 12 hours

// Typical-time map for time-based outpatient E/M + telephone E/M (CPT typical minutes).
const MINUTES = {
  99202: 15,
  99203: 30,
  99204: 45,
  99205: 60,
  99211: 5,
  99212: 10,
  99213: 15,
  99214: 25,
  99215: 40,
  99441: 5,
  99442: 15,
  99443: 30,
};

export const detector = {
  id: "D22",
  tier: 1,
  scheme: "telehealth-implausible",
  label: "Telehealth implausible",
  cat: "stat",
  needsJudgment: false,
  run(claims, ctx) {
    const days = new Map(); // key (npi|dos) → { npi, dos, minutes, allowed, claimIds:Set, codes:Set }
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      const npi = c.renderingNpi || c.billingNpi;
      for (const l of c.lines || []) {
        const m = MINUTES[l.hcpcs];
        if (!m) continue;
        if (!(l.modifiers || []).map(String).some((x) => TH_MODS.has(x))) continue;
        const key = `${npi}|${l.dosFrom}`;
        const g = days.get(key) || {
          npi,
          dos: l.dosFrom,
          minutes: 0,
          allowed: 0,
          claimIds: new Set(),
          codes: new Set(),
        };
        g.minutes += m * (l.units || 1);
        g.allowed += l.allowedAmount || 0;
        g.claimIds.add(c.claimId);
        g.codes.add(l.hcpcs);
        days.set(key, g);
      }
    }

    const findings = [];
    for (const g of days.values()) {
      if (g.minutes <= THRESHOLD_MIN) continue;
      findings.push({
        detectorId: "D22",
        npi: g.npi,
        scheme: "telehealth-implausible",
        claimIds: [...g.claimIds],
        citation: {
          rule: `Telehealth E/M minutes ${g.minutes} exceed 12-hour day (modifier 95/GT/GQ)`,
          ruleVersion: ctx.quarter,
          // hcpcs is set when the day's telehealth E/M is a single code so the pipeline's per-line
          // exposure dedup (claimId|hcpcs|dos) recognizes overlap with D1 (MUE) on that same line.
          hcpcs: g.codes.size === 1 ? [...g.codes][0] : undefined,
          dos: g.dos,
          computed: g.minutes,
          threshold: THRESHOLD_MIN,
        },
        exposureUsd: Math.round(g.allowed * 100) / 100,
        evidence: { codes: [...g.codes], minutes: g.minutes },
      });
    }
    return findings;
  },
};
