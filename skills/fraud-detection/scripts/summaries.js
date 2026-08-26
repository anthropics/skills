// One plain-English, investigator-facing sentence per finding, built from its citation + evidence.
// Centralizes the "what did we find" wording so every renderer (dashboard / packet / xlsx) shows the
// same defensible statement instead of a generic computed-vs-threshold column. Factual statements —
// the "indicators consistent with" framing lives in the surrounding artifact, not each sentence.

const BY_SCHEME = {
  "impossible-day": (c, e) =>
    `Billed ${c.computed} units of ${c.hcpcs} on ${c.dos}; NCCI MUE MAI-${e.mai} caps ${c.threshold}/day.`,
  "duplicate-claim": (c, e) =>
    `${e.copies} identical claims for ${c.hcpcs} on ${c.dos} (same provider + member); only one is payable.`,
  "global-period-violation": (c, e) =>
    `E/M ${c.hcpcs} billed ${c.computed} day(s) from ${e.procedure} (within its ${c.threshold}-day global period) without modifier 24/25/57.`,
  "non-payable-code": (c, e) =>
    `${c.hcpcs} is a non-payable code (${e.rationale || c.rule}); ${c.computed} unit(s) billed.`,
  "revoked-provider": (c, e) =>
    `Billing NPI was CMS-revoked (effective ${c.computed}${e.barExpires ? `, bar through ${e.barExpires}` : ""}); date of service ${c.threshold} falls inside the bar window.`,
  "ineligible-orderer": (c, e) => `Ordering NPI ${e.orderingNpi} — ${e.reason} (${e.category}).`,
  "phantom-billing": (c, e) => {
    if (e.signal === "excluded-provider")
      return `${e.role === "rendering" ? "Rendering" : "Billing"} provider is on the OIG LEIE exclusion list (excluded ${c.computed}); service dated ${c.threshold}.`;
    if (e.signal === "after-death")
      return `Service dated ${c.computed} is after the beneficiary's date of death (${e.dod || c.threshold}).`;
    if (e.signal === "orphan-add-on")
      return `Type-1 add-on ${c.hcpcs || ""} billed with no listed primary procedure on the same date of service.`
        .replace(/\s+/g, " ")
        .trim();
    return c.rule;
  },
};

export function summarize(finding) {
  const fn = BY_SCHEME[finding.scheme];
  if (!fn) return finding.citation.rule;
  try {
    return fn(finding.citation, finding.evidence || {});
  } catch {
    return finding.citation.rule;
  }
}
