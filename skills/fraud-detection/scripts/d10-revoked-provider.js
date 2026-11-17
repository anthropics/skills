// D10 — Revoked-provider billing. A claim billed by a provider whose CMS Medicare enrollment was
// REVOKED, with a date of service inside the revocation / reenrollment-bar window. A SEPARATE
// authority from the OIG exclusion list (D3) — many revoked providers are not on the LEIE.
// Cites the revocation reason + effective and bar-expiration dates.

// Tolerate both column-name styles: the legacy data-api JSON uses UPPER_SNAKE
// (REVOCATION_EFCTV_DT), the cms-catalog parquet uses the human-readable headers
// ("Revocation Effective Date"). Resolve once from the first row.
function col(row, re) {
  for (const k of Object.keys(row)) if (re.test(k)) return k;
}
function indexByNpi(rows) {
  const m = new Map();
  if (!rows || !rows.length) return m;
  const r0 = rows[0];
  const kNpi = col(r0, /^NPI$/i);
  const kRev = col(r0, /REVOCATION.*EF(FE)?CTV|Revocation Effective/i);
  const kBar = col(r0, /REENROLL.*BAR.*EXP/i);
  const kRsn = col(r0, /REVOCATION.*R(EA)?S/i);
  for (const r of rows) {
    const npi = String(r[kNpi] || "").trim();
    if (npi) m.set(npi, { revDate: r[kRev], barExp: r[kBar], reason: r[kRsn] });
  }
  return m;
}

export const detector = {
  id: "D10",
  tier: 1,
  scheme: "revoked-provider",
  label: "Revoked provider",
  cat: "elig",
  needsJudgment: false,
  link: {
    label: "42 CFR 424.535",
    url: "https://www.ecfr.gov/current/title-42/chapter-IV/subchapter-B/part-424/subpart-D/section-424.535",
  },
  run(claims, ctx) {
    const rev = ctx.revokedByNpi || indexByNpi(ctx.revoked);
    const findings = [];
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      const r = rev.get(c.billingNpi);
      if (!r) continue;
      const dos = c.lines.map((l) => l.dosFrom).sort()[0];
      const afterRev = !r.revDate || dos >= r.revDate;
      const beforeBarExp = !r.barExp || dos <= r.barExp;
      if (afterRev && beforeBarExp) {
        findings.push({
          detectorId: "D10",
          npi: c.billingNpi,
          scheme: "revoked-provider",
          claimIds: [c.claimId],
          citation: {
            rule: `CMS-revoked provider — ${r.reason || "enrollment revoked"}`,
            ruleVersion: ctx.quarter,
            computed: r.revDate, // revocation effective
            threshold: dos, // claim DOS inside the bar window
            barExpires: r.barExp,
          },
          exposureUsd:
            Math.round(c.lines.reduce((s, l) => s + (l.allowedAmount || 0), 0) * 100) / 100,
          evidence: { revocationReason: r.reason, barExpires: r.barExp },
        });
      }
    }
    return findings;
  },
};
