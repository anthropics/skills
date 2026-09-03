// Citation gate — deterministic, no model. Two jobs:
//  1. assertFinding: shape contract check at the detector→gate boundary (catches the
//     silent-drop bug where a detector emits a malformed finding that vanishes).
//  2. recompute: re-derive every cited number from the raw claim lines + reference rows
//     carried in the finding; any row that doesn't reproduce exactly is zeroed.
//
// Finding shape (the contract every detector returns):
//   { detectorId, npi, scheme, claimIds:[...], exposureUsd,
//     citation:{ rule, ruleVersion, computed, threshold, ... }, evidence:{...} }

import { cohortStats } from "./d07-outlier.js";
import { category, indexOrd } from "./d09-ineligible-orderer.js";
const prog = (f) => (f.evidence && f.evidence.program) || "medicare";

const REQUIRED = ["detectorId", "npi", "scheme", "claimIds", "citation", "exposureUsd"];
const daysBetween = (a, b) => (Date.parse(b) - Date.parse(a)) / 86400000;
const dosNum = (d) => Number(String(d).replace(/-/g, ""));

export function assertFinding(f, id) {
  for (const k of REQUIRED) {
    if (f[k] === undefined || f[k] === null) {
      throw new Error(`${id} emitted a finding missing "${k}": ${JSON.stringify(f)}`);
    }
  }
  if (Array.isArray(f.claimIds) === false || f.claimIds.length === 0) {
    throw new Error(`${id} finding has no claimIds`);
  }
  const c = f.citation;
  if (c.rule === undefined || c.computed === undefined || c.threshold === undefined) {
    throw new Error(`${id} citation missing rule/computed/threshold`);
  }
  return f;
}

// Independent recompute of a finding's cited number from the raw cited claims. Re-derives the value
// a different way than the detector, so a wrong/uncited number is caught. Schemes without a cheap
// independent check pass on shape+claim-existence only (flagged in the result).
const RECOMPUTE = {
  // D1: respect the MAI tier. MAI-1 is a per-LINE cap — re-confirm a single line of the cited code/DOS
  // has units === computed and over the cap (summing would manufacture a mismatch when two MAI-1 lines
  // share a code/DOS). MAI-2/3 are per-DAY edits — sum units across the cited code/DOS.
  D1: (f, claims) => {
    if (f.evidence && f.evidence.mai === 1) {
      return claims.some((c) =>
        c.lines.some(
          (l) =>
            l.hcpcs === f.citation.hcpcs &&
            l.dosFrom === f.citation.dos &&
            l.units === f.citation.computed &&
            l.units > f.citation.threshold,
        ),
      );
    }
    let sum = 0;
    for (const c of claims)
      for (const l of c.lines)
        if (l.hcpcs === f.citation.hcpcs && l.dosFrom === f.citation.dos) sum += l.units;
    return sum === f.citation.computed && f.citation.computed > f.citation.threshold;
  },
  // D3: independently re-confirm the cited phantom sub-signal against the source tables.
  D3: (f, claims, ctx) => {
    const c = claims[0];
    if (!c) return false;
    const sig = f.evidence && f.evidence.signal;
    if (sig === "excluded-provider") {
      if (!ctx || !ctx.leie || !ctx.leie.byNpi) return true; // shape-only without the table
      const party = f.evidence.role === "rendering" ? c.renderingNpi : c.billingNpi;
      const ex = ctx.leie.byNpi.get(party);
      if (!ex || ex.exclDate !== f.citation.computed) return false;
      return c.lines.some((l) => dosNum(l.dosFrom) >= Number(ex.exclDate));
    }
    if (sig === "state-medicaid-excluded") {
      if (!ctx || !ctx.stateExclusions) return true;
      const party = f.evidence.role === "rendering" ? c.renderingNpi : c.billingNpi;
      const ex = ctx.stateExclusions.get(party);
      if (!ex) return false;
      return !ex.sanctionDate || c.lines.some((l) => l.dosFrom >= ex.sanctionDate);
    }
    if (sig === "after-death") {
      if (!ctx || !ctx.members) return true;
      const dod = ctx.members.get(c.beneId)?.dod;
      return Boolean(dod && dod === f.citation.threshold && c.lines.some((l) => l.dosFrom > dod));
    }
    if (sig === "orphan-add-on") {
      if (!ctx || !ctx.aoc) return true;
      const a = ctx.aoc.get(f.citation.hcpcs);
      if (!a || a.primaries.size === 0) return false;
      const sameDos = c.lines.filter((l) => l.dosFrom === f.citation.dos).map((l) => l.hcpcs);
      return ![...a.primaries].some((p) => sameDos.includes(p));
    }
    return false;
  },
  // D9: independently re-confirm the cited orderer is ineligible (LEIE-as-of-DOS, absent, or not
  // PECOS-eligible for the service category) for an orderer-required service.
  D9: (f, claims, ctx) => {
    const c = claims[0];
    if (!c) return false;
    const cat = category(c.lines);
    if (!cat) return false;
    const ref = f.evidence && f.evidence.orderingNpi;
    if (ref !== c.referringNpi) return false;
    const dos = c.lines.map((l) => l.dosFrom).sort()[0];
    const ex = ctx && ctx.leie && ctx.leie.byNpi && ctx.leie.byNpi.get(ref);
    if (ex && dosNum(dos) >= Number(ex.exclDate)) return true;
    const ord = (ctx && ctx.orderRefByNpi) || indexOrd(ctx && ctx.orderReferring);
    const o = ord.get(ref);
    return !o || o[cat] !== "Y";
  },
  // D10: independently re-confirm the billing NPI is in the revoked file with DOS inside the bar window.
  D10: (f, claims, ctx) => {
    const c = claims[0];
    if (!c) return false;
    let r = null;
    for (const x of (ctx && ctx.revoked) || []) {
      if ((x.NPI || "").trim() === c.billingNpi) {
        r = { revDate: x.REVOCATION_EFCTV_DT, barExp: x.REENROLLMENT_BAR_EXPRTN_DT };
        break;
      }
    }
    if (!r || r.revDate !== f.citation.computed) return false;
    const dos = c.lines.map((l) => l.dosFrom).sort()[0];
    if (dos !== f.citation.threshold) return false;
    return (!r.revDate || dos >= r.revDate) && (!r.barExp || dos <= r.barExp);
  },
  // D2: the cited PTP edit must exist in the base table, and both the Column 1 and Column 2 codes
  // must actually be billed on the cited DOS of the cited claim.
  D2: (f, claims, ctx) => {
    if (!ctx || !ctx.ptp) return true; // can't independently check without the table; shape-only
    const c1 = f.evidence && f.evidence.column1;
    const c2 = f.evidence && f.evidence.column2;
    if (!ctx.ptp[prog(f)].has(`${c1}|${c2}`)) return false;
    if (f.citation.hcpcs !== c2) return false;
    return claims.some((cl) => {
      const onDos = cl.lines.filter((l) => l.dosFrom === f.citation.dos).map((l) => l.hcpcs);
      return onDos.includes(c1) && onDos.includes(c2);
    });
  },
  // D4: a cited claim diagnosis must be in the cited HCPCS's NON-covered union across governing
  // articles, and not also covered anywhere.
  D4: (f, claims, ctx) => {
    if (!ctx || !ctx.coverage || !ctx.coverage.hcpcToArticles.size) return true; // shape-only
    const cov = ctx.coverage;
    const articles = cov.hcpcToArticles.get(f.citation.hcpcs);
    if (!articles) return false;
    const covered = new Set();
    const noncovered = new Set();
    for (const a of articles) {
      for (const x of cov.coveredByArticle.get(a) || []) covered.add(x);
      for (const x of cov.noncoveredByArticle.get(a) || []) noncovered.add(x);
    }
    const claimDx = claims.flatMap((cl) => (cl.diagnoses || []).map((d) => d.code));
    return claimDx.some((d) => noncovered.has(d) && !covered.has(d));
  },
  // D7: re-derive the provider's services-per-beneficiary from the cited claims, recompute the cohort
  // robust-z from the real by-provider table, and confirm it matches the cited z and clears threshold.
  D7: (f, claims, ctx) => {
    if (!ctx || !ctx.partbByProvider) return true; // shape-only without the cohort table
    const specialty = f.evidence && f.evidence.specialty;
    const stats = cohortStats(ctx.partbByProvider, specialty);
    if (!stats) return false;
    let srvcs = 0;
    const benes = new Set();
    for (const c of claims) {
      for (const l of c.lines || []) srvcs += l.units || 1;
      if (c.beneId) benes.add(c.beneId);
    }
    if (!benes.size) return false;
    const z = (srvcs / benes.size - stats.median) / (1.4826 * stats.mad);
    return Math.round(z * 10) / 10 === f.citation.computed && z >= f.citation.threshold;
  },
  // D12: re-count identical copies of the cited line (HCPCS + DOS) across the cited net-payable claims;
  // must equal the cited copy count and be > 1.
  D12: (f, claims) => {
    let copies = 0;
    for (const cl of claims) {
      const status = cl.adjudication && cl.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      for (const l of cl.lines || []) {
        if (l.hcpcs === f.citation.hcpcs && l.dosFrom === f.citation.dos) copies += 1;
      }
    }
    return copies === f.citation.computed && f.citation.computed > 1;
  },
  // D11: the cited HCPCS must actually be in the non-payable set re-derived from the MUE table.
  D11: (f, claims, ctx) => {
    if (!ctx || !ctx.nonPayable) return true; // can't independently check without the table; shape-only
    return ctx.nonPayable[prog(f)].has(f.citation.hcpcs);
  },
  // D13: days-between(procedure DOS, E/M DOS) must equal the cited value and sit in the global window
  // (−1 pre-op for 090, else 0 .. threshold); AND re-confirm the procedure actually carries that global
  // period in PFS and the cited E/M line lacks a bypass modifier (24/25/57).
  D13: (f, claims, ctx) => {
    const proc = f.evidence && f.evidence.procedureDos;
    if (!proc || !f.citation.dos) return true;
    const d = daysBetween(proc, f.citation.dos);
    const lower = f.citation.threshold === 90 ? -1 : 0;
    if (!(d === f.citation.computed && d >= lower && d <= f.citation.threshold)) return false;
    if (ctx && ctx.pfs) {
      const p = ctx.pfs.get(f.evidence.procedure);
      if (!p || Number(p.globalDays) !== f.citation.threshold) return false;
    }
    const BYPASS = new Set(["24", "25", "57"]);
    for (const c of claims)
      for (const l of c.lines || [])
        if (l.hcpcs === f.citation.hcpcs && l.dosFrom === f.citation.dos)
          if ((l.modifiers || []).map(String).some((m) => BYPASS.has(m))) return false;
    return true;
  },
};

export function gateFindings(findings, claims, ctx) {
  const byId = new Map(claims.map((c) => [c.claimId, c]));
  const kept = [];
  const dropped = [];
  for (const f of findings) {
    assertFinding(f, f.detectorId);
    // Drop zero-recovery findings: a $0 referral reads as noise to an SIU and inflates findingCount
    // and scheme breadth (which drives ranking) without representing recoverable dollars.
    if (!(f.exposureUsd > 0)) {
      dropped.push({ id: f.detectorId, npi: f.npi, why: "zero exposure" });
      continue;
    }
    if (!f.claimIds.every((id) => byId.has(id))) {
      dropped.push({ id: f.detectorId, npi: f.npi, why: "cited claim not in corpus" });
      continue;
    }
    const check = RECOMPUTE[f.detectorId];
    if (
      check &&
      !check(
        f,
        f.claimIds.map((id) => byId.get(id)),
        ctx,
      )
    ) {
      dropped.push({ id: f.detectorId, npi: f.npi, why: "recompute mismatch" });
      continue;
    }
    kept.push(f);
  }
  return { kept, dropped };
}
