// D3 — Phantom billing: services that couldn't have been legitimately rendered/billed.
// Three deterministic sub-signals, each as-of the date of service:
//   (a) billing NPI on the OIG LEIE (excluded) — BY NPI only (Tier-1). Name+DOB matches are
//       lead-only and never authored here (DESIGN.md §4).
//   (b) a service dated after the beneficiary's date of death.
//   (c) orphan Type-1 add-on code — billed with none of its listed primary codes on the same DOS.
// Skips non-net-payable (denied/reversed) claims.

import { enrollmentAt } from "./reference-data.js";

export const detector = {
  id: "D3",
  tier: 1,
  scheme: "phantom-billing",
  label: "Phantom billing",
  cat: "elig",
  needsJudgment: false,
  link: {
    label: "OIG LEIE exclusions database",
    url: "https://oig.hhs.gov/exclusions/exclusions_list.asp",
  },
  run(claims, ctx) {
    const leie = ctx.leie && ctx.leie.byNpi;
    const members = ctx.members; // Map<beneId, { dod: "YYYY-MM-DD", ... }>
    const aoc = ctx.aoc;
    const findings = [];

    for (const c of claims) {
      const status = c.adjudication && c.adjudication.status;
      if (status === "denied" || status === "reversed") continue;
      const allClaimIds = [c.claimId];
      const earliestDos = c.lines.map((l) => l.dosFrom).sort()[0];
      const sumAllowed = c.lines.reduce((s, l) => s + (l.allowedAmount || 0), 0);

      // (a) excluded provider — check BOTH billing and rendering NPI (the canonical scheme is an
      // excluded individual rendering under a clean group's billing NPI). Exposure counts only lines
      // dated on/after the exclusion (a claim straddling the exclusion date isn't fully exposed).
      if (leie) {
        for (const party of [...new Set([c.billingNpi, c.renderingNpi].filter(Boolean))]) {
          const ex = leie.get(party);
          if (!ex) continue;
          const afterLines = c.lines.filter((l) => dosNum(l.dosFrom) >= Number(ex.exclDate));
          if (afterLines.length === 0) continue;
          const role = party === c.renderingNpi && party !== c.billingNpi ? "rendering" : "billing";
          findings.push(
            mk(
              party,
              allClaimIds,
              afterLines.reduce((s, l) => s + (l.allowedAmount || 0), 0),
              {
                rule: `OIG LEIE exclusion (${ex.exclType}) — ${role} provider`,
                ruleVersion: ctx.quarter,
                computed: ex.exclDate,
                threshold: afterLines.map((l) => l.dosFrom).sort()[0],
              },
              { signal: "excluded-provider", role },
            ),
          );
        }
      }

      // (a′) state-Medicaid-excluded provider — same shape as LEIE but sourced from the per-state
      // Medicaid exclusion lists (OpenSanctions). Only fires on Medicaid runs; LEIE already covers
      // federal exclusions across programs. enrolled_state comes from the bene's enrollment span.
      if (ctx.stateExclusions && ctx.lob === "medicaid") {
        const enrolledState = enrollmentAt(ctx, c.beneId, earliestDos)?.enrolledState;
        for (const party of [...new Set([c.billingNpi, c.renderingNpi].filter(Boolean))]) {
          const ex = ctx.stateExclusions.get(party);
          if (!ex) continue;
          const afterLines = ex.sanctionDate
            ? c.lines.filter((l) => l.dosFrom >= ex.sanctionDate)
            : c.lines;
          if (afterLines.length === 0) continue;
          const role = party === c.renderingNpi && party !== c.billingNpi ? "rendering" : "billing";
          findings.push(
            mk(
              party,
              allClaimIds,
              afterLines.reduce((s, l) => s + (l.allowedAmount || 0), 0),
              {
                rule: `State Medicaid exclusion (${ex.state || "?"}) — ${role} provider`,
                ruleVersion: ctx.quarter,
                computed: ex.sanctionDate || "on list",
                threshold: afterLines.map((l) => l.dosFrom).sort()[0],
              },
              { signal: "state-medicaid-excluded", role, state: ex.state, enrolledState },
            ),
          );
        }
      }

      // (b) service after date of death
      if (members) {
        const dod = members.get(c.beneId)?.dod;
        if (dod) {
          const after = c.lines.filter((l) => l.dosFrom > dod);
          if (after.length) {
            findings.push(
              mk(
                c.billingNpi,
                allClaimIds,
                after.reduce((s, l) => s + (l.allowedAmount || 0), 0),
                {
                  rule: "Service billed after beneficiary date of death",
                  ruleVersion: ctx.quarter,
                  computed: after[0].dosFrom,
                  threshold: dod,
                },
                { signal: "after-death", dod },
              ),
            );
          }
        }
      }

      // (c) orphan Type-1 add-on
      if (aoc) {
        for (const l of c.lines) {
          const a = aoc.get(l.hcpcs);
          if (!a || a.primaries.size === 0) continue;
          const sameDosCodes = c.lines.filter((x) => x.dosFrom === l.dosFrom).map((x) => x.hcpcs);
          const hasPrimary = [...a.primaries].some((p) => sameDosCodes.includes(p));
          if (!hasPrimary) {
            findings.push(
              mk(
                c.billingNpi,
                allClaimIds,
                l.allowedAmount || 0,
                {
                  rule: "NCCI add-on edit: Type-1 add-on billed with no listed primary on same DOS",
                  ruleVersion: ctx.quarter,
                  hcpcs: l.hcpcs,
                  dos: l.dosFrom,
                  computed: "no listed primary present",
                  threshold: "a listed primary required",
                },
                { signal: "orphan-add-on" },
              ),
            );
          }
        }
      }
    }
    return findings;
  },
};

function mk(npi, claimIds, exposure, citation, evidence) {
  return {
    detectorId: "D3",
    npi,
    scheme: "phantom-billing",
    claimIds,
    citation,
    exposureUsd: Math.round((exposure || 0) * 100) / 100,
    evidence,
  };
}

const dosNum = (d) => Number(d.replaceAll("-", ""));
