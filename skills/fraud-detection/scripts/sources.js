// Public-authority citation for each finding (deterministic, no model, no network). Maps a finding to
// the public rulebook page it rests on, plus a short human "locator" naming the exact token that
// tripped it and the substrings a renderer should highlight. Where the target page renders the
// triggering code inline (CMS MCD articles, eCFR), we append a Chrome scroll-to-text fragment
// (#:~:text=) so the link opens already scrolled to and highlighting that text.
//
// Tier-1 (this file) gives every finding a working external link + on-page highlight from codes the
// deterministic floor already knows. Tier-2 (the per-provider agent) may later UPGRADE source with a
// verbatim `excerpt` + `highlight` pulled from the page it actually read — see investigate.js.
//
// Contract returned per finding:
//   { authority, url|null, locator, highlight:[...] }   (highlight = literal substrings to <mark>)
// All values are plain text/URLs; renderers MUST HTML-escape before DOM insertion (untrusted in T2).

// Chrome scroll-to-text fragment for a single phrase. Spec: encode each phrase, prefix `#:~:text=`.
// PDFs do not support text fragments — callers linking to a .pdf should use a `#page=N` anchor instead.
const textFragment = (phrase) => (phrase ? `#:~:text=${encodeURIComponent(phrase)}` : "");
// PDF deep link: open at a page. Chrome's viewer ignores `search=` (chromium #40483153 — only
// page/view/zoom/nameddest are parsed), so we don't emit it; the dashboard renders source.highlight
// as a "find on page" hint instead.
const pdfFragment = (page) => `#page=${page}`;
// CMS Physician Fee Schedule Look-Up Tool, pre-filled to one HCPCS — shows the GLOB DAYS / status
// indicator / RVU columns for that code. This is the code-specific proof; the policy doc is context.
const pfsLookup = (hcpcs) =>
  `https://www.cms.gov/medicare/physician-fee-schedule/search?Y=0&T=0&HT=0&CT=3&H1=${encodeURIComponent(hcpcs)}&M=5`;

// data.cms.gov interactive viewer deep-link. The viewer reads a single ?query= param carrying
// URL-encoded JSON; this opens the by-Provider table pre-filtered to the specialty cohort, narrowed
// to the six columns a reviewer needs (NPI, name, state, type, Tot_Benes, Tot_Srvcs), 50/page,
// sorted by Tot_Srvcs DESC so the high-volume peers are on top. "Look at the doctors like you."
const CMS_BY_PROVIDER =
  "https://data.cms.gov/provider-summary-by-type-of-service/medicare-physician-other-practitioners/" +
  "medicare-physician-other-practitioners-by-provider/data";
export function cmsByProviderUrl(specialty) {
  if (!specialty) return CMS_BY_PROVIDER;
  const q = {
    filters: {
      list: [
        {
          conditions: [
            {
              column: { value: "Rndrng_Prvdr_Type" },
              comparator: { value: "=" },
              filterValue: [specialty],
            },
            { column: { value: "Tot_Benes" }, comparator: { value: ">=" }, filterValue: ["11"] },
          ],
        },
      ],
      rootConjunction: { value: "AND" },
    },
    keywords: "",
    offset: 0,
    limit: 50,
    sort: { sortBy: "Tot_Srvcs", sortOrder: "DESC" },
    columns: [
      "Rndrng_NPI",
      "Rndrng_Prvdr_Last_Org_Name",
      "Rndrng_Prvdr_State_Abrvtn",
      "Rndrng_Prvdr_Type",
      "Tot_Benes",
      "Tot_Srvcs",
    ],
  };
  return `${CMS_BY_PROVIDER}?query=${encodeURIComponent(JSON.stringify(q))}`;
}

// Stable public rulebook landing pages (the authority for each detector family).
const NCCI_MUE =
  "https://www.cms.gov/medicare/coding-billing/national-correct-coding-initiative-ncci-edits/medicare-ncci-medically-unlikely-edits";
const NCCI_PTP =
  "https://www.cms.gov/medicare/coding-billing/national-correct-coding-initiative-ncci-edits/medicare-ncci-procedure-procedure-ptp-edits";
const LEIE = "https://oig.hhs.gov/exclusions/exclusions_list.asp";
const ORDER_REFERRING =
  "https://data.cms.gov/provider-characteristics/medicare-provider-supplier-enrollment/order-and-referring";
const OPT_OUT =
  "https://data.cms.gov/provider-characteristics/medicare-provider-supplier-enrollment/opt-out-affidavits";
const PFS = "https://www.cms.gov/medicare/payment/fee-schedules/physician";
const GLOBAL_SURGERY = "https://www.cms.gov/files/document/mln907166-global-surgery-booklet.pdf";
const CLAIMS_MANUAL_CH1 =
  "https://www.cms.gov/regulations-and-guidance/guidance/manuals/downloads/clm104c01.pdf";
const CFR_424_535 =
  "https://www.ecfr.gov/current/title-42/chapter-IV/subchapter-B/part-424/subpart-D/section-424.535#p-424.535(a)(1)";

// One resolver per detector. Each takes (citation, evidence) and returns the source contract.
// Wrapped in try/catch by resolveSource, so a missing field degrades to the rule text, never throws.
const BY_DETECTOR = {
  D1: (c) => ({
    authority: "CMS NCCI Medically Unlikely Edits (MUE)",
    url: NCCI_MUE,
    locator: `${c.hcpcs}: ${c.computed} units billed; MUE caps ${c.threshold}/day`,
    highlight: [c.hcpcs],
  }),
  D2: (c, e) => ({
    authority: "CMS NCCI Procedure-to-Procedure (PTP) edits",
    url: NCCI_PTP,
    locator: `PTP pair ${e.column1} / ${e.column2} (modifier indicator ${e.modifierIndicator})`,
    highlight: [e.column1, e.column2].filter(Boolean),
  }),
  D3: (c, e) => {
    if (e.signal === "after-death") {
      return {
        authority: "SSA § 1862(a) — no payment for items/services furnished after death",
        url: "https://www.ssa.gov/OP_Home/ssact/title18/1862.htm" + textFragment("death"),
        locator: `Service ${c.computed} after date of death ${e.dod || c.threshold}`,
        highlight: [c.computed, e.dod || c.threshold].filter(Boolean),
      };
    }
    // excluded-provider (and any other phantom signal): OIG LEIE
    return {
      authority: "OIG List of Excluded Individuals/Entities (LEIE)",
      url: LEIE,
      locator: `${e.role === "rendering" ? "Rendering" : "Billing"} provider on LEIE (excluded ${c.computed})`,
      highlight: [c.computed].filter(Boolean),
    };
  },
  D4: (c, e) => {
    const article = e.articleIds && e.articleIds[0];
    const code = e.noncoveredHit && e.noncoveredHit[0];
    const base = article
      ? `https://www.cms.gov/medicare-coverage-database/view/article.aspx?articleid=${article}`
      : "https://www.cms.gov/medicare-coverage-database";
    return {
      authority: article
        ? `CMS Medicare Coverage Database — Article ${article}`
        : "CMS Medicare Coverage Database",
      url: code ? base + textFragment(code) : base,
      locator: `Dx ${(e.noncoveredHit || []).join(", ")} non-covered for HCPCS ${c.hcpcs}`,
      highlight: [...(e.noncoveredHit || []), c.hcpcs].filter(Boolean),
    };
  },
  D7: (c, e) => ({
    // statistical outlier — a cohort comparison, not a rule clause. The link is the BENCHMARK
    // DATASET the cohort was drawn from, not a page that states z. The reviewer's validation
    // surface is evidence.{cohortN, cohortMedian, cohortMad, providerValue, cohortFile} — rendered
    // as the "Cohort computation" panel in finding-view.js.
    authority: `Benchmark dataset — CMS Physician & Other Practitioners by-Provider (${e.specialty})`,
    url: cmsByProviderUrl(e.specialty),
    locator: `${e.providerValue} services/bene vs ${e.specialty} median ${e.cohortMedian} (robust z ${c.computed})`,
    highlight: [e.specialty].filter(Boolean),
  }),
  D9: (c, e) => ({
    authority: "CMS Order and Referring dataset (PECOS eligibility)",
    url: ORDER_REFERRING,
    locator: `Ordering NPI ${e.orderingNpi} ineligible — ${e.reason} (${e.category})`,
    highlight: [e.orderingNpi].filter(Boolean),
  }),
  D10: (c, e) => ({
    authority: "42 CFR § 424.535(a)(1) — revocation of Medicare billing privileges",
    url: CFR_424_535,
    locator: `Billing NPI revoked ${c.computed} (${e.revocationReason}); DOS ${c.threshold} within bar window`,
    highlight: [],
  }),
  D11: (c, e) => ({
    authority: "CMS Physician Fee Schedule — payment status indicators",
    url: PFS,
    locator: `${c.hcpcs} non-payable (${e.rationale || c.rule})`,
    highlight: [c.hcpcs],
  }),
  D12: (c, e) => ({
    authority: "CMS Medicare Claims Processing Manual (Pub. 100-04, Ch. 1) — duplicate claims",
    url: CLAIMS_MANUAL_CH1 + pdfFragment(260),
    locator: `${e.copies} identical lines of ${c.hcpcs} on ${c.dos} (same provider + member)`,
    highlight: [c.hcpcs],
  }),
  D13: (c, e) => ({
    // Primary link = the code-specific data point: PFS row for the surgical HCPCS, GLOB DAYS column
    // shows 090. That is what proves "11450 has a 90-day global" — the booklet only explains the rule.
    authority: `CMS Physician Fee Schedule — ${e.procedure} GLOB DAYS = ${c.threshold}`,
    url: pfsLookup(e.procedure),
    locator: `E/M ${c.hcpcs} within the ${c.threshold}-day global period of ${e.procedure} (no modifier 24/25/57)`,
    highlight: [e.procedure, "GLOB DAYS"],
    // Secondary link = the policy explaining why E/M without 24/25/57 inside a global period is bundled.
    policy: {
      label: "Global Surgery booklet (MLN907166) p.4",
      url: GLOBAL_SURGERY + pdfFragment(4),
    },
  }),
  D14: (c, e) => ({
    authority: "CMS Opt Out Affidavits dataset (SSA §1802(b))",
    url: OPT_OUT + textFragment(e.npi),
    locator: `Billing NPI ${e.npi} opted out ${e.effective} – ${e.end}; DOS ${c.computed} inside window`,
    highlight: [e.npi].filter(Boolean),
  }),
};

// Resolve a finding to its public-authority source. Degrades to the rule text with no link if the
// detector is unmapped or a resolver throws — a finding always carries SOME authority string.
export function resolveSource(finding) {
  const fn = BY_DETECTOR[finding.detectorId];
  // Optional-chain the citation so a finding with a missing/null citation degrades to a generic label
  // instead of throwing out of the whole citation pass (the gate normally guarantees citation, but the
  // header contract promises this never throws).
  const rule = finding.citation?.rule || "Cited public rule";
  const fallback = { authority: rule, url: null, locator: rule, highlight: [] };
  if (!fn) return fallback;
  try {
    const s = fn(finding.citation, finding.evidence || {});
    // de-dup highlight substrings, drop empties
    s.highlight = [...new Set((s.highlight || []).filter(Boolean).map(String))];
    return s;
  } catch {
    return fallback;
  }
}
