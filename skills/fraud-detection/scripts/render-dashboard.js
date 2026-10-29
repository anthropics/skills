// Renders out/referrals.json → out/dashboard.html — a self-contained SIU "adjudication terminal" triage
// view. Single file: brand fonts inlined (base64), icons inlined (SVG), referral data embedded as a JSON
// blob, vanilla JS for filter/sort/search/expand. No framework, no CDN, no network — opens/prints anywhere.
//
//   node scripts/render-dashboard.js
//
// The per-finding evidence cards are PRE-RENDERED server-side via the shared finding-view.js (same module
// the packet uses, so highlighting never drifts) and embedded per referral. Clicking a provider opens its
// provider-packet-<npi>.html in a new tab (sibling file in out/ — render packets with render-packet.js --all).
//
// Optional Tier-2 overlays (the model never writes the deterministic floor; the skill materializes these
// from the workflow return): out/source-excerpts.json and out/providers.json.
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import path from "node:path";

import {
  CAT,
  ICONS,
  RECORD_CSS,
  ROOT_CSS,
  SCHEME,
  findingCardHtml,
  fontFaceCss,
  mergeExcerpts,
  mergeProviders,
} from "./finding-view.js";
import { outDir as resolveOutDir } from "./paths.js";

const outDir = resolveOutDir();
const data = JSON.parse(readFileSync(path.join(outDir, "referrals.json"), "utf8"));

// runDate is presentational chrome — stamp today if the floor didn't set it.
if (!data.meta.runDate) data.meta.runDate = new Date().toISOString().slice(0, 10);

mergeExcerpts(data, outDir);
const { providers, source: providerSource } = mergeProviders(outDir);
data.providers = providers;

// Pre-render each referral's evidence cards (shared module) + embed the taxonomy the client needs for
// pills / filter chips. The client renders rows/filtering/sort; the detail cards are static HTML.
for (const r of data.referrals) {
  r.cards = r.findings.map((f) => findingCardHtml(f, data.meta.quarter)).join("");
  // Only link the provider row to its packet if that packet was actually rendered (render-packet.js
  // --all). Without this guard a row would link to a 404 when packets weren't generated.
  r.hasPacket = existsSync(path.join(outDir, `provider-packet-${r.npi}.html`));
}
data.scheme = SCHEME;
data.cat = CAT;

// Escape JSON for safe embedding in a <script> block: neutralize </script> breakout + invalid U+2028/9.
const jsonForScript = (v) =>
  JSON.stringify(v)
    .replace(/</g, "\\u003c")
    .replace(/>/g, "\\u003e")
    .replace(/&/g, "\\u0026")
    .replace(new RegExp(String.fromCharCode(0x2028), "g"), "\\u2028")
    .replace(new RegExp(String.fromCharCode(0x2029), "g"), "\\u2029");

const html = `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Program Integrity — Investigation Referrals</title>
<style>
  ${fontFaceCss()}
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
  .sys .live{color:var(--green);} .sys .live::before{content:"●";margin-right:6px;font-size:9px;vertical-align:1px;}
  .disc{background:var(--vbg);color:#7c2e16;border-bottom:1px solid var(--vbd);padding:6px 18px;font-size:11.5px;letter-spacing:.02em;display:flex;gap:9px;align-items:center;}
  .disc b{color:#641f0c;}
  .wrap{max-width:1340px;margin:0 auto;padding:18px 18px 64px;}
  .mast{display:flex;justify-content:space-between;align-items:flex-end;border-bottom:1px solid var(--rule);padding-bottom:14px;margin-bottom:16px;}
  .mast .t1{font-size:11px;letter-spacing:.2em;color:var(--amber);text-transform:uppercase;}
  .mast h1{font-family:var(--ui);font-weight:600;font-size:25px;letter-spacing:-.015em;margin:7px 0 3px;}
  .mast .t2{font-size:12px;color:var(--t2);}
  .mast .right{text-align:right;font-size:11.5px;color:var(--t2);line-height:1.9;}
  .mast .right b{color:var(--ink);}
  .readouts{display:grid;grid-template-columns:repeat(4,1fr);gap:1px;background:var(--line);border:1px solid var(--line);margin-bottom:18px;}
  .ro{background:var(--surf);padding:13px 16px;}
  .ro .k{font-size:10px;letter-spacing:.07em;color:var(--t3);text-transform:uppercase;}
  .ro .val{font-size:26px;font-weight:600;letter-spacing:-.01em;margin-top:7px;color:var(--ink);}
  .ro.amber .val{color:var(--amber);} .ro.stat .val{color:var(--stx);}
  .ro .sub{font-size:10.5px;color:var(--t3);margin-top:5px;}
  .cmd{border:1px solid var(--line2);background:var(--surf);margin-bottom:14px;}
  .cmd .grp{display:flex;align-items:stretch;border-bottom:1px solid var(--line);}
  .cmd .grp:last-child{border-bottom:0;}
  .cmd .lab{flex-shrink:0;width:128px;padding:0 14px;font-size:10px;letter-spacing:.07em;text-transform:uppercase;color:var(--t3);background:var(--surf2);border-right:1px solid var(--line2);display:flex;align-items:center;gap:7px;}
  .cmd .lab .dot{width:7px;height:7px;border-radius:2px;}
  .cmd .opts{display:flex;flex-wrap:wrap;gap:7px;flex:1;padding:8px 12px;align-items:center;}
  .tog{padding:5px 11px;border:1px solid var(--line2);border-radius:5px;background:var(--surf);color:var(--t2);cursor:pointer;font-family:var(--mono);font-size:12px;letter-spacing:.01em;display:inline-flex;gap:8px;align-items:center;transition:background .1s,color .1s,border-color .1s;}
  .tog:hover{background:var(--surf2);color:var(--ink);border-color:var(--t3);}
  .tog .ct{color:var(--faint);font-size:11px;}
  .tog.on{background:var(--ink);color:var(--paper);border-color:var(--ink);} .tog.on .ct{color:rgba(239,236,227,.6);}
  .tog.all.on{background:var(--amber);color:#fff;border-color:var(--amber);} .tog.all.on .ct{color:rgba(255,255,255,.7);}
  .metaline{display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;font-size:11.5px;color:var(--t2);}
  .metaline .right{display:flex;gap:8px;align-items:center;}
  .srch{display:flex;align-items:center;gap:7px;border:1px solid var(--line2);background:var(--surf);padding:0 10px;height:28px;}
  .srch svg{color:var(--t3);font-size:13px;} .srch input{border:0;background:transparent;color:var(--ink);font-family:var(--mono);font-size:12px;outline:0;width:160px;}
  .srch input::placeholder{color:var(--faint);}
  .xbtn{height:28px;padding:0 11px;border:1px solid var(--line2);background:var(--surf);color:var(--t2);cursor:pointer;font-family:var(--mono);font-size:11.5px;letter-spacing:.03em;}
  .xbtn:hover{color:var(--ink);border-color:var(--amber);}
  table{width:100%;border-collapse:collapse;border:1px solid var(--line2);background:var(--surf);}
  thead th{background:var(--head);border-bottom:1px solid var(--rule);text-align:left;padding:9px 14px;font-size:10px;letter-spacing:.07em;text-transform:uppercase;color:var(--t2);white-space:nowrap;font-weight:700;}
  thead th.so{cursor:pointer;} thead th.so:hover{color:var(--ink);}
  thead th .ar{color:var(--amber);margin-left:4px;opacity:0;font-size:10px;} thead th.act .ar{opacity:1;}
  th.num,td.num{text-align:right;}
  tbody tr.row>td{border-bottom:1px solid var(--line);padding:11px 14px;vertical-align:middle;cursor:pointer;}
  tbody tr.row:nth-child(4n+1)>td{background:rgba(28,26,20,.018);}
  tbody tr.row:hover>td{background:var(--surf2);}
  tbody tr.row.open>td{background:#f3efe5;border-bottom-color:var(--line2);}
  .car{color:var(--faint);display:inline-block;transition:transform .12s;width:12px;}
  tr.row.open .car{transform:rotate(90deg);color:var(--amber);}
  .prov a.provlink{font-family:var(--ui);font-weight:600;color:var(--ink);font-size:13.5px;}
  .prov a.provlink:hover{color:var(--amber);text-decoration:none;}
  .prov a.provlink .go{color:var(--faint);font-size:10px;margin-left:4px;} .prov a.provlink:hover .go{color:var(--amber);}
  .prov .provlink-off{font-family:var(--ui);font-weight:600;color:var(--ink);font-size:13.5px;}
  .prov-sub{font-size:11px;color:var(--t2);margin-top:2px;}
  .prov-sub .npi{color:var(--amber);} .prov-sub .syn{color:var(--t3);}
  .stags{display:flex;flex-wrap:wrap;gap:4px;}
  .stag{font-size:11px;padding:2px 8px;border:1px solid var(--mk);letter-spacing:.01em;white-space:nowrap;display:inline-flex;gap:6px;align-items:center;color:var(--mk);}
  .stag .d{width:6px;height:6px;border-radius:50%;background:var(--mk);}
  .cat-edit{--mk:#2f6383;} .cat-elig{--mk:#a23b1f;} .cat-stat{--mk:#5a4d86;}
  .cl{font-variant-numeric:tabular-nums;}
  .conf{font-size:11px;letter-spacing:.05em;text-transform:uppercase;display:inline-flex;gap:7px;align-items:center;font-weight:600;}
  .conf .d{width:8px;height:8px;border-radius:50%;}
  .conf-high{color:var(--green);} .conf-high .d{background:var(--green);}
  .conf-medium{color:var(--amber);} .conf-medium .d{background:var(--amber);}
  .conf-low{color:var(--t3);} .conf-low .d{background:var(--faint);}
  .exp{font-weight:600;font-variant-numeric:tabular-nums;color:var(--ink);}
  .exp .e{display:block;font-size:9.5px;letter-spacing:.05em;color:var(--stx);text-transform:uppercase;margin-top:2px;}
  tfoot td{background:var(--head);border-top:1px solid var(--rule);padding:11px 14px;font-size:11.5px;color:var(--t2);}
  tfoot .ft{color:var(--ink);font-weight:700;font-variant-numeric:tabular-nums;font-size:14px;}
  tr.det{display:none;} tr.det.show{display:table-row;}
  tr.det>td{padding:0;border-bottom:1px solid var(--line);background:#f3efe4;}
  .recs{padding:6px 14px 16px 38px;display:flex;flex-direction:column;gap:10px;}
  ${RECORD_CSS}
  .empty{padding:30px;text-align:center;color:var(--t3);}
  footer.disc-foot{margin-top:18px;font-family:var(--ui);font-size:12px;color:var(--t3);font-style:italic;line-height:1.6;max-width:780px;}
  @media print{
    @page{margin:12mm;}
    body{background:#fff;font-size:11px;}
    .disc{-webkit-print-color-adjust:exact;print-color-adjust:exact;}
    .wrap{max-width:none;padding:0;}
    .cmd,.metaline .right{display:none;}
    tr.det{display:table-row !important;}
    .rec,tr.row,.trip{break-inside:avoid;}
    *{-webkit-print-color-adjust:exact;print-color-adjust:exact;}
  }
</style></head><body>
  <div class="sys">
    <div class="seg mark">${ICONS.shield}PROGRAM INTEGRITY</div>
    <div class="seg">MODULE <b>SIU / CLAIMS-ADJUDICATION</b></div>
    <div class="seg">RULE-Q <b id="s-q"></b></div>
    <div class="seg">RUN <b id="s-run"></b></div>
    <div class="seg spacer"></div>
    <div class="seg live">SCREENING ACTIVE</div>
  </div>
  ${data.meta.disclaimer ? `<div class="disc">${ICONS.warning}<span><b>${data.meta.disclaimer}</b> ${data.meta.language}</span></div>` : ""}
  <div class="wrap">
    <div class="mast">
      <div>
        <div class="t1">Investigation queue</div>
        <h1>Investigation Referrals</h1>
        <div class="t2">Medicare / Medicaid claims screening · automated indicators of improper payment</div>
      </div>
      <div class="right">
        DETECTORS&nbsp;&nbsp;<b id="s-det"></b><br>
        RECORDS&nbsp;&nbsp;<b id="s-n"></b> &nbsp;·&nbsp; GATE-DROP&nbsp;&nbsp;<b id="s-g"></b>
      </div>
    </div>
    <div class="readouts" id="readouts"></div>
    <div class="cmd" id="cmd"></div>
    <div class="metaline">
      <div id="count"></div>
      <div class="right">
        <label class="srch">${ICONS.search}<input id="q" placeholder="search NPI / provider / scheme" autocomplete="off"></label>
        <button class="xbtn" id="expAll">EXPAND ALL</button>
      </div>
    </div>
    <table>
      <thead><tr>
        <th style="width:26px"></th>
        <th>Provider</th>
        <th>Schemes</th>
        <th class="so num" data-sort="claims">Claims<span class="ar">▼</span></th>
        <th class="so" data-sort="confidence">Confidence<span class="ar">▼</span></th>
        <th class="so num act" data-sort="exposure">Exposure<span class="ar">▼</span></th>
      </tr></thead>
      <tbody id="rows"></tbody>
      <tfoot id="foot"></tfoot>
    </table>
    <footer class="disc-foot" id="disc"></footer>
  </div>
<script id="data" type="application/json">${jsonForScript(data)}</script>
<script>
const DATA = JSON.parse(document.getElementById("data").textContent);
const PROVIDERS = DATA.providers || {}, SCHEME = DATA.scheme || {}, CAT = DATA.cat || {};
const CONF_RANK = { high: 3, medium: 2, low: 1 };
const providerOf = npi => PROVIDERS[npi] || { name: "Unknown provider", specialty: "—", state: "—" };
const schemeMeta = s => SCHEME[s] || { cat: "edit", label: String(s).replace(/-/g, " ") };
const e = s => String(s ?? "").replace(/[&<>"]/g, c => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
const usd = n => "$" + Number(n).toLocaleString("en-US", { minimumFractionDigits: (Number(n) % 1 ? 2 : 0), maximumFractionDigits: 2 });

const active = new Set(); let sortKey="exposure", sortDir=-1, query="", allOpen=false;
const $ = id => document.getElementById(id);

function head(){
  const m=DATA.meta;
  $("s-q").textContent=m.quarter; $("s-run").textContent=m.runDate;
  $("s-det").textContent=(m.detectors||[]).join(" "); $("s-n").textContent=m.referralCount; $("s-g").textContent=(m.gate&&m.gate.droppedAtGate)||0;
  $("readouts").innerHTML=
    '<div class="ro"><div class="k">Referrals</div><div class="val">'+m.referralCount+'</div><div class="sub">distinct providers flagged</div></div>'+
    '<div class="ro amber"><div class="k">Recoverable · rule-based</div><div class="val">'+usd(m.recoverableUsd||0)+'</div><div class="sub">line-level overpayment, de-duplicated</div></div>'+
    '<div class="ro stat"><div class="k">Statistical estimate</div><div class="val">'+usd(m.statisticalEstimateUsd||0)+'</div><div class="sub">supporting — not a determined overpayment</div></div>'+
    '<div class="ro"><div class="k">Total exposure</div><div class="val">'+usd(m.totalExposureUsd||0)+'</div><div class="sub">rule-based + estimate</div></div>';
  $("disc").textContent=m.language;
}

function schemeStats(){ const map={}; DATA.referrals.forEach(r=>r.schemes.forEach(s=>{(map[s]=map[s]||{count:0});map[s].count++;})); return map; }

function cmd(){
  const st=schemeStats(); const byCat={edit:[],elig:[],stat:[]};
  Object.keys(st).forEach(s=>byCat[schemeMeta(s).cat].push(s));
  const dotc={edit:"#2f6383",elig:"#a23b1f",stat:"#5a4d86"};
  let h='<div class="grp"><div class="lab">Scope</div><div class="opts">'+
    '<button class="tog all'+(active.size===0?" on":"")+'" data-all="1">▸ ALL<span class="ct">'+DATA.referrals.length+'</span></button></div></div>';
  ["edit","elig","stat"].forEach(cat=>{ if(!byCat[cat].length) return;
    h+='<div class="grp"><div class="lab"><span class="dot" style="background:'+dotc[cat]+'"></span>'+(CAT[cat]?CAT[cat].short:cat)+'</div><div class="opts">';
    byCat[cat].sort().forEach(s=>{ h+='<button class="tog'+(active.has(s)?" on":"")+'" data-s="'+e(s)+'">'+e(schemeMeta(s).label)+'<span class="ct">'+st[s].count+'</span></button>'; });
    h+='</div></div>';
  });
  $("cmd").innerHTML=h;
  $("cmd").querySelectorAll(".tog").forEach(b=>b.onclick=()=>{ if(b.dataset.all){active.clear();} else {const s=b.dataset.s; active.has(s)?active.delete(s):active.add(s);} render(); });
}

document.querySelectorAll("th.so").forEach(th=>th.onclick=()=>{ const k=th.dataset.sort;
  if(sortKey===k) sortDir*=-1; else {sortKey=k;sortDir=-1;}
  document.querySelectorAll("th.so").forEach(x=>{x.classList.toggle("act",x===th); x.querySelector(".ar").textContent=sortDir<0?"▼":"▲";}); render(); });
$("q").addEventListener("input",ev=>{query=ev.target.value.trim().toLowerCase();render();});
$("expAll").onclick=()=>{ allOpen=!allOpen;
  document.querySelectorAll("tr.row").forEach(r=>r.classList.toggle("open",allOpen));
  document.querySelectorAll("tr.det").forEach(d=>d.classList.toggle("show",allOpen));
  $("expAll").textContent=allOpen?"COLLAPSE ALL":"EXPAND ALL"; };

function render(){
  cmd();
  let list=DATA.referrals.filter(r=>active.size===0||r.schemes.some(s=>active.has(s)));
  if(query) list=list.filter(r=>{const p=providerOf(r.npi); return r.npi.toLowerCase().includes(query)||p.name.toLowerCase().includes(query)||r.schemes.some(s=>s.includes(query)||schemeMeta(s).label.toLowerCase().includes(query));});
  list=list.slice().sort((a,b)=>{let av,bv;
    if(sortKey==="exposure"){av=a.exposureUsd;bv=b.exposureUsd;}
    else if(sortKey==="claims"){av=a.claimIds.length;bv=b.claimIds.length;}
    else {av=CONF_RANK[a.confidence]||0;bv=CONF_RANK[b.confidence]||0;}
    return (av-bv)*sortDir||(b.exposureUsd-a.exposureUsd);});
  const rows=$("rows"); rows.innerHTML=""; let tot=0,rec=0,est=0;
  if(!list.length) rows.innerHTML='<tr><td colspan="6" class="empty">// no records match filter</td></tr>';
  list.forEach(r=>{
    tot+=r.exposureUsd; rec+=r.recoverableUsd||0; est+=r.statisticalEstimateUsd||0;
    const p=providerOf(r.npi); const estRow=(r.recoverableUsd||0)===0&&(r.statisticalEstimateUsd||0)>0;
    const tag = p.real ? "NPPES" : "synthetic";
    const packet = "provider-packet-"+encodeURIComponent(r.npi)+".html";
    // Link to the packet only if it was rendered; otherwise show the name as plain text (no dead link).
    const provCell = r.hasPacket
      ? '<a class="provlink" href="'+packet+'" target="_blank" rel="noopener" title="Open provider packet in a new tab">'+e(p.name)+'<span class="go">↗</span></a>'
      : '<span class="provlink-off">'+e(p.name)+'</span>';
    const tr=document.createElement("tr"); tr.className="row";
    tr.innerHTML='<td><span class="car">▸</span></td>'+
      '<td><div class="prov">'+provCell+'</div>'+
        '<div class="prov-sub"><span class="npi">'+e(r.npi)+'</span> <span class="syn">· '+e(p.specialty)+' · '+e(p.state)+' · '+tag+'</span></div></td>'+
      '<td><div class="stags">'+r.schemes.map(s=>{const m=schemeMeta(s);return '<span class="stag cat-'+m.cat+'"><span class="d"></span>'+e(m.label)+'</span>';}).join("")+'</div></td>'+
      '<td class="num"><span class="cl">'+r.claimIds.length+'</span></td>'+
      '<td><span class="conf conf-'+e(r.confidence)+'"><span class="d"></span>'+e(r.confidence)+'</span></td>'+
      '<td class="num"><span class="exp">'+usd(r.exposureUsd)+(estRow?'<span class="e">estimate</span>':'')+'</span></td>';
    const det=document.createElement("tr"); det.className="det";
    det.innerHTML='<td colspan="6"><div class="recs">'+(r.cards||"")+'</div></td>';
    // Row toggles detail — but clicking the provider link opens the packet instead of toggling.
    tr.onclick=(ev)=>{ if(ev.target.closest("a.provlink")) return; const o=tr.classList.toggle("open");det.classList.toggle("show",o); };
    rows.appendChild(tr); rows.appendChild(det);
  });
  $("count").textContent='SHOWING '+list.length+' / '+DATA.referrals.length+' RECORDS'+(active.size?' · FILTER {'+[...active].join(", ")+'}':"");
  $("foot").innerHTML=list.length?'<tr><td colspan="5">Σ shown exposure · '+usd(rec)+' rule-based + '+usd(est)+' estimate</td><td class="num"><span class="ft">'+usd(tot)+'</span></td></tr>':"";
  if(allOpen){document.querySelectorAll("tr.row").forEach(r=>r.classList.add("open"));document.querySelectorAll("tr.det").forEach(d=>d.classList.add("show"));}
}
head(); render();
</script>
</body></html>`;

writeFileSync(path.join(outDir, "index.html"), html);
console.log(
  `index.html written (${(html.length / 1024).toFixed(1)} KB, self-contained, ${data.referrals.length} referrals, providers: ${providerSource})`,
);
