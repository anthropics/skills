// Shared presentation core for the dashboard and provider-packet renderers — ONE source of truth for
// the scheme taxonomy, per-detector evidence highlighting, authority links, provider directory, brand
// fonts, and the finding "record card" HTML. Both renderers build cards server-side via findingCardHtml
// so the highlighting logic never drifts between the two artifacts.
//
// SECURITY: every value that reaches HTML is escaped via esc(); source.excerpt is untrusted scraped
// text and is escaped-then-marked via markHtml() (escape the full string, then insert only literal
// <mark> tags around escaped highlight substrings).
import { existsSync, readFileSync } from "node:fs";
import path from "node:path";

import { LINKS, SCHEME } from "./registry.js";

// Re-export for render-dashboard.js / render-packet.js — the maps themselves are derived from each
// dNN-*.js detector file's own export (see registry.js).
export { LINKS, SCHEME };

export const esc = (s) =>
  String(s ?? "").replace(
    /[&<>"]/g,
    (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" })[c],
  );

export const usd = (n) =>
  "$" +
  Number(n).toLocaleString("en-US", {
    minimumFractionDigits: Number(n) % 1 ? 2 : 0,
    maximumFractionDigits: 2,
  });

export const ymd = (s) =>
  typeof s === "string" && /^\d{8}$/.test(s)
    ? `${s.slice(0, 4)}-${s.slice(4, 6)}-${s.slice(6, 8)}`
    : s;

// Escape the full string FIRST, then wrap highlight substrings in literal <mark> tags in a SINGLE
// left-to-right pass (a global regex never re-scans inserted text), so overlapping highlights — e.g.
// ["29877","298"] from Tier-2 scraped excerpts — can't produce nested/broken <mark> markup. Longest
// alternatives first so the regex prefers the most specific match.
const reEscape = (s) => s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
export const markHtml = (s, hls) => {
  const out = esc(s);
  const needles = [...new Set((hls || []).map((h) => esc(h)).filter(Boolean))].sort(
    (a, b) => b.length - a.length,
  );
  if (!needles.length) return out;
  const re = new RegExp(needles.map(reEscape).join("|"), "g");
  return out.replace(re, (m) => `<mark>${m}</mark>`);
};

export const CAT = {
  edit: { label: "Coding / claim edits", short: "Coding edit" },
  elig: { label: "Provider eligibility", short: "Eligibility" },
  stat: { label: "Statistical indicators", short: "Statistical" },
};
export const CONF_RANK = { high: 3, medium: 2, low: 1 };
export const schemeMeta = (s) => SCHEME[s] || { cat: "edit", label: String(s).replace(/-/g, " ") };

// Synthetic provider directory — 9-prefix NPIs are NPPES-reserved (never issued) and never resolve,
// so this keeps fixture output legible. Real names/specialty/state come from Tier-2 NPPES enrichment
// (out/providers.json), merged on top by mergeProviders(). Precedence: NPPES > synthetic > Unknown.
export const SYNTHETIC_PROVIDERS = {
  9000000070: {
    name: "Cascade Orthopaedic Associates",
    specialty: "Orthopaedic surgery",
    state: "OR",
  },
  9000000010: { name: "Apex Reference Laboratory", specialty: "Clinical laboratory", state: "TX" },
  9000000020: { name: "Riverside Imaging Center", specialty: "Nuclear medicine", state: "IL" },
  9000000060: { name: "Helix Genomic Diagnostics", specialty: "Molecular pathology", state: "CA" },
  9000000230: { name: "HomeCare Medical Supply LLC", specialty: "DME supplier", state: "FL" },
  9000000030: { name: "Lakeside Family Medicine", specialty: "Family medicine", state: "MN" },
  9000000040: { name: "Summit Dermatology Group", specialty: "Dermatology", state: "CO" },
  9000000210: { name: "Beacon Home Health Services", specialty: "Home health agency", state: "OH" },
  9000000200: { name: "Northgate Medical Clinic", specialty: "General practice", state: "NV" },
  9000000220: { name: "Pioneer Pain Management", specialty: "Pain medicine", state: "AZ" },
  9000000090: { name: "Harold T. Vance, MD", specialty: "Internal medicine", state: "PA" },
};

// Merge the synthetic directory with the optional NPPES sidecar (out/providers.json). Returns
// { providers, source } where source is "nppes" if the sidecar was applied, else "synthetic".
export function mergeProviders(outDir) {
  const providers = { ...SYNTHETIC_PROVIDERS };
  let source = "synthetic";
  const p = path.join(outDir, "providers.json");
  if (existsSync(p)) {
    try {
      const real = JSON.parse(readFileSync(p, "utf8"));
      for (const [npi, prov] of Object.entries(real))
        if (prov && prov.name) providers[npi] = { ...providers[npi], ...prov, real: true };
      source = "nppes";
    } catch {
      /* malformed sidecar — keep synthetic */
    }
  }
  return { providers, source };
}
export const providerOf = (providers, npi) =>
  providers[npi] || { name: "Unknown provider", specialty: "—", state: "—" };

// Merge the optional source-excerpt sidecar (out/source-excerpts.json) onto each finding's source.
export function mergeExcerpts(data, outDir) {
  const p = path.join(outDir, "source-excerpts.json");
  if (!existsSync(p)) return;
  try {
    const overlay = JSON.parse(readFileSync(p, "utf8"));
    for (const r of data.referrals)
      for (const f of r.findings) {
        const ex = overlay?.[r.npi]?.[f.detectorId];
        if (ex && f.source) {
          if (typeof ex.excerpt === "string") f.source.excerpt = ex.excerpt;
          if (Array.isArray(ex.highlight) && ex.highlight.length)
            f.source.highlight = [
              ...new Set([...(f.source.highlight || []), ...ex.highlight.map(String)]),
            ];
        }
      }
  } catch {
    /* malformed sidecar — render deterministic source only */
  }
}

// Brand fonts → CDN. Anthropic Sans (body/headings) from assets.claude.ai; JetBrains Mono (code/tables/evidence)
// from Google Fonts. @import must precede other rules, so callers interpolate this at the very top of <style>.
const SANS_CDN = "https://assets.claude.ai/Fonts/AnthropicSans-Text";
const SANS_WEIGHTS = { Regular: 400, Medium: 500, Semibold: 600, Bold: 700 };
export function fontFaceCss() {
  const sans = Object.entries(SANS_WEIGHTS)
    .map(
      ([name, w]) =>
        `@font-face{font-family:"Anthropic Sans";src:url("${SANS_CDN}-${name}-Static.otf") format("opentype");font-weight:${w};font-style:normal;font-display:swap;}`,
    )
    .join("");
  return `@import url("https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@400;500&display=swap");${sans}`;
}

export const ICONS = {
  shield:
    '<svg viewBox="0 0 16 16" width="1em" height="1em" fill="none" stroke="currentColor" stroke-width="1.4" aria-hidden="true" style="vertical-align:-.15em"><path d="M8 1.5 13 3.2v4.3c0 3.2-2.1 5.8-5 6.9-2.9-1.1-5-3.7-5-6.9V3.2z"/><path d="M8 5.2v3.1M8 10.4v.1"/></svg>',
  warning:
    '<svg viewBox="0 0 16 16" width="1em" height="1em" fill="none" stroke="currentColor" stroke-width="1.4" aria-hidden="true" style="vertical-align:-.15em"><path d="M8 2.2 14.5 13.3H1.5z"/><path d="M8 6.5v3M8 11.3v.1"/></svg>',
  search:
    '<svg viewBox="0 0 16 16" width="1em" height="1em" fill="none" stroke="currentColor" stroke-width="1.4" aria-hidden="true" style="vertical-align:-.15em"><circle cx="7" cy="7" r="4.3"/><path d="m10.3 10.3 3 3"/></svg>',
};

const isEstimate = (f) =>
  f.scheme === "utilization-outlier" ||
  /estimate|supporting/i.test((f.evidence && f.evidence.note) || "");

// Token builders + renderer for inline evidence highlighting.
const T = {
  t: (s) => ({ k: "t", s }),
  v: (s) => ({ k: "v", s }),
  vs: (s) => ({ k: "vs", s }),
  r: (s) => ({ k: "r", s }),
  c: (s) => ({ k: "c", s }),
  a: () => ({ k: "a" }),
  l: (s) => ({ k: "l", s }),
  n: (s) => ({ k: "n", s }),
};
const inline = (tokens) =>
  (tokens || [])
    .map((tk) => {
      switch (tk.k) {
        case "t":
          return esc(tk.s);
        case "v":
          return `<span class="pi-v">${esc(tk.s)}</span>`;
        case "vs":
          return `<span class="pi-v pi-vs">${esc(tk.s)}</span>`;
        case "r":
          return `<span class="pi-ref">${esc(tk.s)}</span>`;
        case "c":
          return `<span class="pi-code">${esc(tk.s)}</span>`;
        case "a":
          return `<span class="pi-arrow">▸</span>`;
        case "l":
          return `<span class="pi-label">${esc(tk.s)}</span>`;
        case "n":
          return `<span class="pi-note">${esc(tk.s)}</span>`;
        default:
          return "";
      }
    })
    .join("");

// Per-detector evidence model: summary + tripwire token arrays + metadata. The fallback degrades a new
// detector to computed-vs-threshold until given a bespoke template.
export function findingModel(f, quarter) {
  const c = f.citation || {},
    ev = f.evidence || {},
    stat = isEstimate(f),
    m = schemeMeta(f.scheme);
  const V = stat ? T.vs : T.v;
  let summary = [],
    trip = [];
  switch (f.detectorId) {
    case "D1":
      summary = [
        T.t("Billed "),
        V(c.computed + " units"),
        T.t(" of "),
        T.c(c.hcpcs),
        T.t(
          " on " +
            c.dos +
            ". NCCI MUE MAI-" +
            (ev.mai ?? 2) +
            " caps this code at " +
            c.threshold +
            "/day.",
        ),
      ];
      trip = [
        T.l("Units over cap"),
        V(c.computed),
        T.a(),
        T.t("per-day cap "),
        T.r(c.threshold),
        T.n("+" + (ev.excessUnits ?? c.computed - c.threshold) + " excess unit(s)"),
      ];
      break;
    case "D2":
      summary = [
        T.t("Code "),
        T.c(ev.column2),
        T.t(" was billed with "),
        T.c(ev.column1),
        T.t(
          " — an NCCI PTP pair flagged " +
            (ev.rationale || "mutually exclusive") +
            ", modifier indicator " +
            ev.modifierIndicator +
            ".",
        ),
      ];
      trip = [
        T.l("Conflicting pair"),
        V(ev.column1),
        T.t("+"),
        V(ev.column2),
        T.n(
          "mutually exclusive · " +
            (ev.bypassModifierPresent ? "bypass modifier present" : "no bypass modifier present"),
        ),
      ];
      break;
    case "D3":
      if (ev.signal === "after-death") {
        summary = [
          T.t("Date of service "),
          V(c.computed),
          T.t(" falls after the beneficiary's date of death "),
          T.r(ev.dod || c.threshold),
          T.t("."),
        ];
        trip = [
          T.l("Service after death"),
          T.t("DOS "),
          V(c.computed),
          T.a(),
          T.t("date of death "),
          T.r(ev.dod || c.threshold),
        ];
      } else {
        summary = [
          T.t("Billing provider appears on the "),
          V("OIG LEIE"),
          T.t(" exclusion list (excluded " + ymd(c.computed) + "); service billed "),
          T.c(c.threshold),
          T.t(" while excluded."),
        ];
        trip = [
          T.l("Excluded provider"),
          V("OIG LEIE — " + (ev.role || "billing")),
          T.t("excluded "),
          T.r(ymd(c.computed)),
          T.a(),
          T.t("service "),
          T.r(c.threshold),
        ];
      }
      break;
    case "D4": {
      const dx = (ev.noncoveredHit || ev.claimDx || []).join(", ");
      summary = [
        T.t("Diagnosis "),
        V(dx),
        T.t(" is listed non-covered for HCPCS "),
        T.c(c.hcpcs),
        T.t(" under Medicare coverage article "),
        T.c(ev.articleIds && ev.articleIds[0]),
        T.t(" on " + c.dos + "."),
      ];
      trip = [
        T.l("Non-covered ICD-10"),
        V(dx),
        T.t("not covered for "),
        T.r(c.hcpcs),
        T.n("coverage article " + ((ev.articleIds && ev.articleIds[0]) || "")),
      ];
      break;
    }
    case "D7":
      summary = [
        T.t("Services-per-beneficiary "),
        V(ev.providerValue + ".0"),
        T.t(" vs " + ev.specialty + " cohort median "),
        T.r(ev.cohortMedian),
        T.t(" (n=" + ev.cohortN + ") — robust z "),
        V(c.computed),
        T.t("."),
      ];
      trip = [
        T.l("Robust z-score"),
        V(c.computed),
        T.a(),
        T.t("flag threshold "),
        T.r(c.threshold),
        T.n(
          ev.providerValue + ".0 svc/bene vs median " + ev.cohortMedian + " · supporting estimate",
        ),
      ];
      break;
    case "D9":
      summary = [
        T.t("Ordering NPI "),
        V(ev.orderingNpi || c.computed),
        T.t(
          " is " +
            (ev.reason || "absent from the CMS Order & Referring file") +
            " (" +
            ev.category +
            ").",
        ),
      ];
      trip = [
        T.l("Ineligible orderer"),
        T.t("ordering NPI "),
        V(ev.orderingNpi || c.computed),
        T.n("absent from CMS Order & Referring file · " + ev.category),
      ];
      break;
    case "D10":
      summary = [
        T.t("Billing NPI was CMS-revoked effective "),
        V(c.computed),
        T.t(" (bar through "),
        T.r(ev.barExpires || c.barExpires),
        T.t("); date of service "),
        V(c.threshold),
        T.t(" falls inside the bar window. Reason: " + ev.revocationReason + "."),
      ];
      trip = [
        T.l("Inside revocation bar"),
        V("revoked " + c.computed),
        T.a(),
        T.r("bar to " + (ev.barExpires || c.barExpires)),
        T.n("DOS " + c.threshold + " inside window · " + ev.revocationReason),
      ];
      break;
    case "D11":
      summary = [
        T.t("HCPCS "),
        V(c.hcpcs),
        T.t(
          " is a non-payable code (" +
            ev.rationale +
            "); " +
            c.computed +
            " unit(s) billed on " +
            c.dos +
            ".",
        ),
      ];
      trip = [
        T.l("Non-payable code"),
        V(c.hcpcs),
        T.t("status "),
        T.r(ev.rationale),
        T.n("threshold " + c.threshold + " payable"),
      ];
      break;
    case "D12":
      summary = [
        V(c.computed + " identical claims"),
        T.t(" for "),
        T.c(c.hcpcs),
        T.t(" on " + c.dos + " (same provider and member) — only " + c.threshold + " is payable."),
      ];
      trip = [
        T.l("Duplicate lines"),
        V(c.computed),
        T.t("identical claims, payable "),
        T.r(c.threshold),
        T.n((f.claimIds || []).join(" / ")),
      ];
      break;
    case "D13":
      summary = [
        T.t("E/M "),
        T.c(c.hcpcs),
        T.t(" billed "),
        V(c.computed + " days"),
        T.t(" after "),
        T.c(ev.procedure),
        T.t(" (" + ev.procedureDos + ") — within its "),
        T.r(c.threshold + "-day"),
        T.t(" global period, with no modifier "),
        V("24/25/57"),
        T.t("."),
      ];
      trip = [
        T.l("In global period"),
        V(c.computed + "d"),
        T.t("after " + ev.procedure + ", within "),
        T.r(c.threshold + "d global"),
        T.n("missing modifier 24/25/57"),
      ];
      break;
    default:
      summary = [T.t(f.summary || c.rule || "")];
      trip = [T.l("Computed"), V(c.computed), T.a(), T.t("threshold "), T.r(c.threshold)];
  }
  const metas = [];
  if (c.hcpcs) metas.push({ k: "HCPCS", v: c.hcpcs, code: true });
  if (c.dos) metas.push({ k: "Date of service", v: c.dos });
  metas.push({
    k: "Claim" + ((f.claimIds || []).length > 1 ? "s" : ""),
    v: (f.claimIds || []).join("  "),
    code: true,
  });
  metas.push({ k: "Detector", v: f.detectorId, code: true });
  const fallback = LINKS[f.detectorId];
  const link =
    f.source && f.source.url
      ? {
          label: (fallback && fallback.label) || f.source.authority || "Public rule",
          url: f.source.url,
        }
      : fallback;
  // Statistical detectors carry a cohort-computation panel — the reviewer's validation surface.
  // The robust z is recomputable from these inputs alone; cohortFile is the local CSV slice
  // (sibling file in the run dir) of the exact rows the median/MAD were drawn from.
  const cohort =
    ev && ev.cohortN
      ? {
          specialty: ev.specialty,
          n: ev.cohortN,
          median: ev.cohortMedian,
          mad: ev.cohortMad,
          value: ev.providerValue,
          z: c.computed,
          threshold: c.threshold,
          file: ev.cohortFile || null,
          basis: ev.basis,
        }
      : null;
  return {
    detector: f.detectorId,
    scheme: f.scheme,
    label: m.label,
    cat: m.cat,
    catLabel: CAT[m.cat].short,
    est: stat,
    exposure: f.exposureUsd,
    summary,
    trip,
    ruleText: c.rule || "",
    ruleVersion: c.ruleVersion || quarter,
    metas,
    // Primary link = code-specific lookup (proves the data point); optional source.policy = the
    // explanatory rule doc. Both render side by side so the reviewer can verify "this code has this
    // property" AND "here's why that property matters".
    links: [link, f.source && f.source.policy].filter(Boolean),
    // For PDF links Chrome ignores #search=, so surface the highlight terms as a copyable
    // "find on page" hint instead. Shown when any link is a PDF and there's something to find.
    findHint:
      ((link && /\.pdf(?:[#?]|$)/i.test(link.url || "")) ||
        (f.source?.policy && /\.pdf(?:[#?]|$)/i.test(f.source.policy.url || ""))) &&
      (f.source?.highlight || []).length
        ? f.source.highlight
        : null,
    excerpt: f.source && f.source.excerpt,
    highlight: (f.source && f.source.highlight) || [],
    cohort,
    sourceRow: ev && ev.sourceRow,
  };
}

// Generic "Source row" panel: the literal reference-table row that triggered a table-backed finding,
// plus a download link to the one-row CSV slice and the upstream CMS dataset URL.
function sourceRowHtml(sr) {
  if (!sr) return "";
  const safeHref = (u) => (/^https?:\/\//i.test(String(u)) ? String(u) : "#");
  const head =
    `<span class="k">Source row</span><code>${esc(sr.table)}</code>` +
    `<span class="rel">${esc(sr.release || "")}</span>` +
    (sr.file ? `<a class="ext dl" href="./${esc(sr.file)}" download>⤓ ${esc(sr.file)}</a>` : "") +
    (sr.sourceUrl
      ? `<a class="ext" href="${esc(safeHref(sr.sourceUrl))}" target="_blank" rel="noopener noreferrer">${esc(sr.sourceLabel || "CMS dataset")}</a>`
      : "");
  if (sr.absenceIsFinding) {
    return (
      `<div class="srcrow"><div class="srh">${head}</div>` +
      `<div class="srabs">No row in <code>${esc(sr.table)}</code> for ` +
      `${Object.entries(sr.key)
        .map(([k, v]) => `<code>${esc(k)}=${esc(v)}</code>`)
        .join(" ")} — <b>that absence is the finding.</b></div></div>`
    );
  }
  if (!sr.row) return "";
  const cols = Object.keys(sr.row);
  return (
    `<div class="srcrow"><div class="srh">${head}</div>` +
    `<table class="srt"><thead><tr>${cols.map((c) => `<th>${esc(c)}</th>`).join("")}</tr></thead>` +
    `<tbody><tr>${cols.map((c) => `<td>${esc(sr.row[c] ?? "")}</td>`).join("")}</tr></tbody></table></div>`
  );
}

// The "record card" HTML for one finding — the shared evidence block used by both renderers.
export function findingCardHtml(f, quarter) {
  const M = findingModel(f, quarter);
  const metas = M.metas
    .map(
      (x) =>
        `<span class="fld"><i>${esc(x.k)}</i>${x.code ? `<span class="pi-code">${esc(x.v)}</span>` : esc(x.v)}</span>`,
    )
    .join("");
  // Only emit http(s) hrefs — strip javascript:/data:/other schemes so a non-conforming source.url
  // can never execute on click (esc() guards HTML metachars but not the URL scheme).
  const safeHref = (u) => (/^https?:\/\//i.test(String(u)) ? String(u) : "#");
  const links = M.links
    .map(
      (l) =>
        `<a class="ext" href="${esc(safeHref(l.url))}" target="_blank" rel="noopener noreferrer">${esc(l.label)}</a>`,
    )
    .join("");
  const findHint = M.findHint
    ? `<span class="find-hint"><i>⌘F</i>${M.findHint.map((t) => `<code>${esc(t)}</code>`).join("")}</span>`
    : "";
  const excerpt = M.excerpt
    ? `<div class="excerpt"><span class="k">Source excerpt</span><q>${markHtml(M.excerpt, M.highlight)}</q></div>`
    : "";
  const co = M.cohort;
  const cohort = co
    ? `<div class="cohort">` +
      `<span class="k">Cohort computation — recompute it yourself</span>` +
      `<div class="cgrid">` +
      `<span><i>Specialty cohort</i><b>${esc(co.specialty)}</b></span>` +
      `<span><i>Cohort n</i><b>${esc(co.n)}</b></span>` +
      `<span><i>Median svc/bene</i><b>${esc(co.median)}</b></span>` +
      `<span><i>MAD</i><b>${esc(co.mad)}</b></span>` +
      `<span><i>This provider</i><b class="hot">${esc(co.value)}</b></span>` +
      `<span><i>Robust z</i><b class="hot">${esc(co.z)}</b> <small>flag ≥ ${esc(co.threshold)}</small></span>` +
      `</div>` +
      `<div class="cform"><code>z = (value − median) / (1.4826 × MAD) = (${esc(co.value)} − ${esc(co.median)}) / (1.4826 × ${esc(co.mad)}) = ${esc(co.z)}</code></div>` +
      (co.file
        ? `<div class="csrc"><a class="ext" href="./${esc(co.file)}" download>⤓ Cohort slice (${esc(co.n)} rows) — ${esc(co.file)}</a>` +
          `<span class="t">exact rows from ${esc(co.basis || "benchmark table")}; sort Srvcs_Per_Bene, take median &amp; MAD</span></div>`
        : "") +
      `</div>`
    : "";
  return (
    `<div class="rec cat-${M.cat}">` +
    `<div class="rec-h"><span class="det">${esc(M.detector)}</span><span class="nm">${esc(M.label)}</span><span class="ct">${esc(M.catLabel)}</span>` +
    `<span class="amt">${usd(M.exposure)}<small>${M.est ? "estimate" : "rule-based"}</small></span></div>` +
    `<div class="rec-sum">${inline(M.summary)}</div>` +
    `<div class="trip">${inline(M.trip)}</div>` +
    `<div class="ruleline"><span class="k">${co ? "Benchmark" : "Rule"}</span>${esc(M.ruleText)}<span class="rv">v${esc(M.ruleVersion)}</span>${links}${findHint}</div>` +
    sourceRowHtml(M.sourceRow) +
    excerpt +
    cohort +
    `<div class="fields">${metas}</div>` +
    `</div>`
  );
}

// The shared CSS for the record card + inline-highlight spans (identical in both artifacts).
export const RECORD_CSS = `
  .rec{border:1px solid var(--line2);border-left:3px solid var(--rc);background:var(--surf);}
  .rec.cat-edit{--rc:#2f6383;} .rec.cat-elig{--rc:#a23b1f;} .rec.cat-stat{--rc:#5a4d86;}
  .rec-h{display:flex;align-items:center;gap:11px;padding:9px 13px;border-bottom:1px solid var(--line);background:var(--head);}
  .rec-h .det{color:#fff;background:var(--rc);padding:1px 7px;font-weight:600;font-size:11px;}
  .rec-h .nm{font-family:var(--ui);font-weight:600;color:var(--ink);font-size:13.5px;}
  .rec-h .ct{font-size:10px;letter-spacing:.05em;text-transform:uppercase;color:var(--t3);}
  .rec-h .amt{margin-left:auto;font-weight:600;font-variant-numeric:tabular-nums;}
  .rec-h .amt small{color:var(--t3);font-weight:400;margin-left:6px;font-size:10px;text-transform:uppercase;letter-spacing:.04em;}
  .rec-sum{padding:11px 13px 0;color:var(--ink);font-size:12.5px;line-height:1.62;}
  .trip{margin:11px 13px 0;border:1px solid var(--vbd);border-left:3px solid var(--red);background:var(--vbg);padding:9px 12px;display:flex;flex-wrap:wrap;align-items:center;gap:7px 9px;}
  .rec.cat-stat .trip{border-color:var(--sbd);border-left-color:var(--stx);background:var(--sbg);}
  .ruleline{padding:11px 13px 0;font-size:11.5px;color:var(--t2);}
  .ruleline .k{color:var(--t3);text-transform:uppercase;letter-spacing:.05em;font-size:10px;margin-right:8px;}
  .ruleline .rv{color:var(--amber);margin-left:7px;}
  .ruleline .ext{margin-left:8px;} .ruleline .ext::after{content:" ↗";font-size:10px;}
  .find-hint{margin-left:10px;color:var(--t3);font-size:10.5px;}
  .find-hint i{font-style:normal;letter-spacing:.04em;margin-right:5px;}
  .find-hint code{background:var(--head);border:1px solid var(--line);padding:0 5px;margin-left:3px;font-size:10px;}
  .srcrow{margin:11px 13px 0;border:1px solid var(--line);background:var(--head);font-size:11px;}
  .srcrow .srh{display:flex;align-items:center;gap:8px;padding:6px 10px;border-bottom:1px solid var(--line);}
  .srcrow .srh .k{color:var(--t3);text-transform:uppercase;letter-spacing:.05em;font-size:10px;}
  .srcrow .srh code{background:var(--surf);padding:0 5px;}
  .srcrow .srh .rel{color:var(--t3);font-size:10px;}
  .srcrow .srh .ext{margin-left:auto;font-size:10.5px;} .srcrow .srh .ext + .ext{margin-left:8px;}
  .srcrow .srt{width:100%;border-collapse:collapse;font-variant-numeric:tabular-nums;}
  .srcrow .srt th{text-align:left;padding:4px 10px;font-size:9.5px;color:var(--t3);text-transform:uppercase;letter-spacing:.04em;border-bottom:1px solid var(--line);}
  .srcrow .srt td{padding:6px 10px;font-family:var(--mono);font-size:11px;color:var(--ink);}
  .srcrow .srabs{padding:8px 10px;color:var(--t2);}
  .srcrow .srabs code{background:var(--surf);padding:0 5px;font-size:10.5px;}
  .excerpt{margin:11px 13px 0;padding:9px 12px;border-left:2px solid var(--line2);background:var(--surf2);font-size:11.5px;line-height:1.6;color:var(--t2);}
  .excerpt .k{display:block;color:var(--t3);text-transform:uppercase;letter-spacing:.05em;font-size:10px;margin-bottom:4px;}
  mark{background:var(--vbg);color:var(--vtx);padding:0 3px;border:1px solid var(--vbd);font-weight:600;}
  .fields{padding:11px 13px 13px;display:flex;flex-wrap:wrap;gap:5px 26px;border-top:1px solid var(--line);margin-top:11px;}
  .fld{font-size:11.5px;} .fld i{font-style:normal;color:var(--t3);text-transform:uppercase;letter-spacing:.05em;font-size:10px;margin-right:7px;}
  .pi-v{color:var(--vtx);background:var(--vbg);border:1px solid var(--vbd);padding:1px 7px;font-weight:600;font-variant-numeric:tabular-nums;white-space:nowrap;}
  .pi-v.pi-vs{color:var(--stx);background:var(--sbg);border-color:var(--sbd);}
  .pi-ref{color:var(--t2);background:var(--surf2);border:1px solid var(--line2);padding:1px 7px;font-variant-numeric:tabular-nums;white-space:nowrap;}
  .pi-code{color:var(--ink);background:#eee9dd;padding:1px 6px;border:1px solid #ded8c9;}
  .pi-arrow{color:var(--red);font-weight:700;} .rec.cat-stat .pi-arrow{color:var(--stx);}
  .pi-label{font-size:10px;letter-spacing:.06em;text-transform:uppercase;color:var(--vtx);font-weight:700;margin-right:2px;}
  .rec.cat-stat .pi-label{color:var(--stx);}
  .pi-note{color:var(--t3);font-style:italic;font-size:11px;}
  .cohort{margin:11px 13px 0;padding:10px 12px;border:1px solid var(--sbd);border-left:3px solid var(--stx);background:var(--sbg);}
  .cohort .k{display:block;color:var(--stx);text-transform:uppercase;letter-spacing:.05em;font-size:10px;font-weight:700;margin-bottom:7px;}
  .cohort .cgrid{display:grid;grid-template-columns:repeat(auto-fit,minmax(130px,1fr));gap:6px 18px;font-size:11.5px;}
  .cohort .cgrid i{display:block;font-style:normal;color:var(--t3);text-transform:uppercase;letter-spacing:.04em;font-size:9.5px;}
  .cohort .cgrid b{font-variant-numeric:tabular-nums;color:var(--ink);}
  .cohort .cgrid b.hot{color:var(--stx);}
  .cohort .cgrid small{color:var(--t3);font-size:10px;margin-left:4px;}
  .cohort .cform{margin-top:8px;font-size:11px;color:var(--t2);}
  .cohort .cform code{background:var(--surf);padding:2px 6px;border:1px solid var(--line);}
  .cohort .csrc{margin-top:8px;font-size:11px;display:flex;flex-wrap:wrap;align-items:center;gap:6px 12px;}
  .cohort .csrc .t{color:var(--t3);font-style:italic;}`;

// The shared design-token :root block (palette + font stacks).
export const ROOT_CSS = `
  :root{
    --paper:#efece3; --surf:#fbfaf5; --surf2:#f4f1e8; --head:#f0ece1;
    --line:#d8d3c5; --line2:#c4bfae; --rule:#1c1a14;
    --ink:#1c1a14; --t2:#585345; --t3:#8b8675; --faint:#a8a392;
    --amber:#9a6a1c; --green:#5d7438; --red:#a23b1f;
    --vbg:#f5ddd1; --vtx:#9c3a20; --vbd:#e0ad97;
    --sbg:#e3ebf1; --stx:#345c7b; --sbd:#aac3d6;
    --mono:"JetBrains Mono",ui-monospace,"SF Mono",Menlo,Consolas,monospace;
    --ui:"Anthropic Sans",ui-sans-serif,-apple-system,"Segoe UI",sans-serif;
  }`;
