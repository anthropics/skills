// D14 — Opted-out provider billing. A provider who has filed an Opt-Out Affidavit with CMS may NOT
// submit claims to Medicare during the opt-out period (SSA §1802(b); 42 CFR 405.410). Any claim with
// a date of service inside [Optout_Effective_Date, Optout_End_Date] is improper on its face. Distinct
// from D10 (revocation) — opt-out is voluntary, but the billing bar is just as absolute.

// Tolerate both column-name styles: the legacy data-api JSON uses Optout_Effective_Date /
// Optout_End_Date; the cms-catalog parquet uses the human-readable headers ("Optout Effective Date").
function col(row, re) {
  for (const k of Object.keys(row)) if (re.test(k)) return k;
}
function indexByNpi(rows) {
  const m = new Map();
  if (!rows || !rows.length) return m;
  const r0 = rows[0];
  const kNpi = col(r0, /^NPI$/i);
  const kEff = col(r0, /Opt.?out.*Eff/i);
  const kEnd = col(r0, /Opt.?out.*End/i);
  for (const r of rows) {
    const npi = String(r[kNpi] || "").trim();
    if (npi) m.set(npi, { effective: r[kEff], end: r[kEnd] });
  }
  return m;
}

export const detector = {
  id: "D14",
  tier: 1,
  scheme: "opt-out-billing",
  label: "Opted-out provider",
  cat: "elig",
  needsJudgment: false,
  link: {
    label: "CMS Opt Out Affidavits",
    url: "https://data.cms.gov/provider-characteristics/medicare-provider-supplier-enrollment/opt-out-affidavits",
  },
  run(claims, ctx) {
    const out = ctx.optOutByNpi || indexByNpi(ctx.optOut);
    const findings = [];
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      const o = out.get(c.billingNpi);
      if (!o) continue;
      for (const l of c.lines) {
        const dos = l.dosFrom;
        const afterEff = !o.effective || dos >= o.effective;
        const beforeEnd = !o.end || dos <= o.end;
        if (!(afterEff && beforeEnd)) continue;
        findings.push({
          detectorId: "D14",
          npi: c.billingNpi,
          scheme: "opt-out-billing",
          claimIds: [c.claimId],
          citation: {
            rule: "Opted-out provider may not bill Medicare (SSA §1802(b))",
            ruleVersion: ctx.quarter,
            computed: dos, // claim DOS
            threshold: `${o.effective} – ${o.end}`, // opt-out window
          },
          exposureUsd: Math.round((l.allowedAmount || 0) * 100) / 100,
          evidence: { npi: c.billingNpi, effective: o.effective, end: o.end },
        });
      }
    }
    return findings;
  },
};
