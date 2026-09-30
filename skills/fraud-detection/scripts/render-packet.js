// Renders a single-provider findings packet → out/provider-packet-<npi>.html, in the same
// "adjudication terminal" aesthetic as the dashboard (shared via finding-view.js). Self-contained
// (fonts inlined, zero network) and print-friendly. RENDER-ONLY — never emailed/sent/uploaded
// (public-safety guardrail); the externally-toned language is strictly "indicators consistent with".
//
//   node scripts/render-packet.js         render a packet for every referral
//   node scripts/render-packet.js <npi>   render one provider only
import { readFileSync, writeFileSync } from "node:fs";
import path from "node:path";

import {
  CAT,
  ICONS,
  RECORD_CSS,
  ROOT_CSS,
  esc,
  findingCardHtml,
  fontFaceCss,
  mergeExcerpts,
  mergeProviders,
  providerOf,
  schemeMeta,
  usd,
} from "./finding-view.js";
import { outDir as resolveOutDir } from "./paths.js";

const outDir = resolveOutDir();
const data = JSON.parse(readFileSync(path.join(outDir, "referrals.json"), "utf8"));
if (!data.meta.runDate) data.meta.runDate = new Date().toISOString().slice(0, 10);
mergeExcerpts(data, outDir);
const { providers } = mergeProviders(outDir);

const fontFace = fontFaceCss();

function renderPacket(r) {
  const p = providerOf(providers, r.npi);
  const provTag = p.real ? "NPPES" : "synthetic";
  const cards = r.findings.map((f) => findingCardHtml(f, data.meta.quarter)).join("");
  const estimate = r.statisticalEstimateUsd ?? 0;

  const html = `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Pre-Investigation Findings — ${esc(p.name)}</title>
<style>
  ${fontFace}
  ${ROOT_CSS}
  *{box-sizing:border-box;}
  body{margin:0;background:var(--paper);color:var(--ink);font-family:var(--mono);font-size:13px;line-height:1.5;-webkit-font-smoothing:antialiased;}
  a{color:var(--amber);text-decoration:none;} a:hover{text-decoration:underline;}
  .sys{display:flex;align-items:center;background:var(--surf);border-bottom:1px solid var(--line2);font-size:11.5px;letter-spacing:.03em;}
  .sys .seg{padding:7px 14px;border-right:1px solid var(--line);color:var(--t2);white-space:nowrap;}
  .sys .seg b{color:var(--ink);font-weight:600;}
  .sys .seg.mark{color:var(--amber);font-weight:700;letter-spacing:.06em;}
  .sys .seg.mark svg{margin-right:7px;}
  .sys .spacer{flex:1;border-right:0;}
  .sys .back{color:var(--amber);}
  .disc{background:var(--vbg);color:#7c2e16;border-bottom:1px solid var(--vbd);padding:6px 18px;font-size:11.5px;letter-spacing:.02em;display:flex;gap:9px;align-items:center;}
  .disc b{color:#641f0c;}
  .wrap{max-width:880px;margin:0 auto;padding:18px 18px 64px;}
  .mast{border-bottom:1px solid var(--rule);padding-bottom:14px;margin-bottom:16px;}
  .mast .t1{font-size:11px;letter-spacing:.2em;color:var(--amber);text-transform:uppercase;}
  .mast h1{font-family:var(--ui);font-weight:600;font-size:23px;letter-spacing:-.015em;margin:7px 0 3px;}
  .mast .who{font-family:var(--ui);font-weight:600;font-size:15px;color:var(--ink);margin-top:8px;}
  .mast .who-sub{font-size:11.5px;color:var(--t2);margin-top:2px;}
  .mast .who-sub .npi{color:var(--amber);} .mast .who-sub .syn{color:var(--t3);}
  .readouts{display:grid;grid-template-columns:repeat(4,1fr);gap:1px;background:var(--line);border:1px solid var(--line);margin-bottom:16px;}
  .ro{background:var(--surf);padding:13px 16px;}
  .ro .k{font-size:10px;letter-spacing:.07em;color:var(--t3);text-transform:uppercase;}
  .ro .val{font-size:24px;font-weight:600;letter-spacing:-.01em;margin-top:7px;color:var(--ink);font-variant-numeric:tabular-nums;}
  .ro.amber .val{color:var(--amber);} .ro.stat .val{color:var(--stx);}
  .ro .sub{font-size:10.5px;color:var(--t3);margin-top:5px;}
  .lede{margin:0 0 16px;padding:11px 14px;border:1px solid var(--line2);border-left:3px solid var(--amber);background:var(--surf);font-size:12.5px;line-height:1.6;color:var(--t2);}
  .lede b{color:var(--ink);}
  .sec{font-size:10px;letter-spacing:.08em;text-transform:uppercase;color:var(--t3);margin:0 0 9px;font-weight:700;}
  .recs{display:flex;flex-direction:column;gap:10px;margin-bottom:18px;}
  ${RECORD_CSS}
  .resp{padding:12px 14px;border:1px solid var(--line2);background:var(--surf);font-size:12px;line-height:1.6;color:var(--t2);}
  .resp b{color:var(--ink);}
  footer.disc-foot{margin-top:16px;font-family:var(--ui);font-size:12px;color:var(--t3);font-style:italic;line-height:1.6;max-width:720px;}
  @media print{
    @page{margin:12mm;}
    body{background:#fff;font-size:11px;}
    .sys .back{display:none;}
    .disc,*{-webkit-print-color-adjust:exact;print-color-adjust:exact;}
    .wrap{max-width:none;padding:0;}
    .rec,.trip{break-inside:avoid;}
  }
</style></head><body>
  <div class="sys">
    <div class="seg mark">${ICONS.shield}PROGRAM INTEGRITY</div>
    <div class="seg">MODULE <b>SIU / PROVIDER PACKET</b></div>
    <div class="seg">RULE-Q <b>${esc(data.meta.quarter)}</b></div>
    <div class="seg">RUN <b>${esc(data.meta.runDate)}</b></div>
    <div class="seg spacer"></div>
    <div class="seg"><a class="back" href="dashboard.html">◂ BACK TO QUEUE</a></div>
  </div>
  ${data.meta.disclaimer ? `<div class="disc">${ICONS.warning}<span><b>${esc(data.meta.disclaimer)}</b> ${esc(data.meta.language)}</span></div>` : ""}
  <div class="wrap">
    <div class="mast">
      <div class="t1">Pre-investigation findings</div>
      <h1>Notice of Identified Billing Patterns</h1>
      <div class="who">${esc(p.name)}</div>
      <div class="who-sub"><span class="npi">${esc(r.npi)}</span> <span class="syn">· ${esc(p.specialty)} · ${esc(p.state)} · ${provTag}</span> · confidence: ${esc(r.confidence)}</div>
    </div>
    <div class="readouts">
      <div class="ro"><div class="k">Findings</div><div class="val">${r.findings.length}</div><div class="sub">flagged claim lines</div></div>
      <div class="ro"><div class="k">Claims</div><div class="val">${r.claimIds.length}</div><div class="sub">distinct claims cited</div></div>
      <div class="ro amber"><div class="k">Recoverable · rule-based</div><div class="val">${usd(r.recoverableUsd ?? r.exposureUsd)}</div><div class="sub">line-level, de-duplicated</div></div>
      <div class="ro stat"><div class="k">Statistical estimate</div><div class="val">${usd(estimate)}</div><div class="sub">supporting — not determined</div></div>
    </div>
    <div class="lede">
      Automated claims screening identified billing patterns <b>consistent with</b>
      ${r.schemes.map((s) => esc(schemeMeta(s).label)).join(", ")}. <b>This notice is not a determination of fraud</b> —
      it identifies patterns for review. Each finding below cites the specific public rule, the exact value that
      tripped it, and a link to the governing authority.
    </div>
    <div class="sec">Findings · ${CAT.edit.short} / ${CAT.elig.short} / ${CAT.stat.short}</div>
    <div class="recs">${cards}</div>
    <div class="resp">
      <b>If you believe these patterns are explained by your records:</b> compile supporting documentation
      (medical records, modifiers, eligibility) for the cited claims and respond through your normal
      program-integrity correspondence channel.
    </div>
    <footer class="disc-foot">${esc(data.meta.language)}</footer>
  </div>
</body></html>`;

  const file = path.join(outDir, `provider-packet-${r.npi}.html`);
  writeFileSync(file, html);
  return { file, html };
}

const arg = process.argv[2];
const targets =
  !arg || arg === "--all" ? data.referrals : [data.referrals.find((x) => x.npi === arg)];
if (targets.some((t) => !t)) {
  console.error(`No referral for NPI ${arg}`);
  process.exit(1);
}
for (const r of targets) {
  const { html } = renderPacket(r);
  console.log(
    `provider-packet-${r.npi}.html (${(html.length / 1024).toFixed(1)} KB) — ${r.schemes.join(", ")}, exposure ${usd(r.exposureUsd)}`,
  );
}
