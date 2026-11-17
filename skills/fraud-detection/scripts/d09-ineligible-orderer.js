// D9 — Ineligible ordering/referring provider. For services that require a valid orderer
// (DME, home health, etc.), the claim's referring NPI must appear in the CMS Order & Referring
// file with the relevant category eligible, and must not be excluded (LEIE). Catches the DME/lab
// kickback pattern where the "ordering" doctor isn't even eligible to order. Subject = the billing
// provider (who relied on the bad orderer); evidence names the referring NPI. CMS PECOS edit.

// Tolerate both the legacy JSON dump and the parquet-backed rows (DuckDB may hand back the
// CMS column names verbatim or lower-cased depending on the writer) — normalize keys to upper.
export function indexOrd(rows) {
  const m = new Map();
  for (const r of rows || []) {
    const u = {};
    for (const k of Object.keys(r)) u[k.toUpperCase()] = r[k];
    if (u.NPI) m.set(String(u.NPI).trim(), u);
  }
  return m;
}

// Only categories that genuinely require an enrolled ordering/referring provider. Returns null
// otherwise — D9 must NOT fire on ordinary referred Part B care (the orderer-eligibility edit is
// scoped to ordered services). DME set excludes A0xxx ambulance; uses DMEPOS supply ranges A4-A8.
export function category(lines) {
  for (const l of lines) {
    const h = l.hcpcs || "";
    if (/^G015[1-6]$|^G0299$|^G0300$/.test(h)) return "HHA";
    if (/^E\d{4}$|^K\d{4}$|^L\d{4}$|^A[4-8]\d{3}$/.test(h)) return "DME";
  }
  return null;
}

export const detector = {
  id: "D9",
  tier: 1,
  scheme: "ineligible-orderer",
  label: "Ineligible orderer",
  cat: "elig",
  needsJudgment: false,
  link: {
    label: "CMS Order & Referring file",
    url: "https://data.cms.gov/provider-characteristics/medicare-provider-supplier-enrollment/order-and-referring",
  },
  run(claims, ctx) {
    const ord = ctx.orderRefByNpi || indexOrd(ctx.orderReferring);
    const leie = ctx.leie && ctx.leie.byNpi;
    const findings = [];
    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      if (!c.referringNpi) continue; // only services that carry an orderer
      const cat = category(c.lines);
      if (!cat) continue; // not an orderer-required service → eligibility edit does not apply
      const o = ord.get(c.referringNpi);
      // LEIE only counts when the orderer was already excluded as of the date of service (mirror D3 —
      // an exclusion dated after the DOS does not make a clean prior service improper).
      const dos = c.lines.map((l) => l.dosFrom).sort()[0];
      const ex = leie && leie.get(c.referringNpi);
      let reason;
      if (ex && Number(String(dos).replace(/-/g, "")) >= Number(ex.exclDate))
        reason = "OIG-excluded (LEIE) as of the date of service";
      else if (!o) reason = "absent from the CMS Order & Referring file";
      else if (o[cat] !== "Y") reason = `not eligible in PECOS to order ${cat}`;
      if (!reason) continue;
      findings.push({
        detectorId: "D9",
        npi: c.billingNpi,
        scheme: "ineligible-orderer",
        claimIds: [c.claimId],
        citation: {
          rule: `Ordering/referring provider ineligible — ${reason}`,
          ruleVersion: ctx.quarter,
          computed: c.referringNpi, // the bad orderer
          threshold: `PECOS-eligible to order ${cat}`,
        },
        exposureUsd:
          Math.round(c.lines.reduce((s, l) => s + (l.allowedAmount || 0), 0) * 100) / 100,
        evidence: { orderingNpi: c.referringNpi, category: cat, reason },
      });
    }
    return findings;
  },
};
