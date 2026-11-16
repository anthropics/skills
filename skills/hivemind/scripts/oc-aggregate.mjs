import { readFileSync } from "node:fs";

function readInput() {
  const args = process.argv.slice(2).filter(a => a !== "--findings-only");
  const findingsOnly = process.argv.includes("--findings-only");
  let raw = "";
  if (args.length) {
    for (const f of args) {
      try { raw += readFileSync(f, "utf8") + "\n"; }
      catch { console.log(JSON.stringify({ ok: false, stage: "aggregate", error: `cannot read file: ${f}` })); process.exit(0); }
    }
  } else raw = readFileSync(0, "utf8");
  return { raw, findingsOnly };
}

function normalizeLine(s) {
  return s.toLowerCase().replace(/[\s\p{P}]+/gu, " ").trim();
}

function extractFindings(text) {
  const out = [];
  for (const line of text.split(/\r?\n/)) {
    const t = line.trim();
    if (/^([-*•]|\d+[.)])\s+/.test(t) && t.length > 12) out.push(t.replace(/^([-*•]|\d+[.)])\s+/, "").trim());
    else if (/^(file|path|src|lib)\b.*:\d+/i.test(t) && t.length > 12) out.push(t);
  }
  return out;
}

function main() {
  const { raw, findingsOnly } = readInput();
  const workers = [];
  for (const line of raw.split(/\r?\n/).filter(l => l.trim())) {
    try {
      const j = JSON.parse(line.trim());
      if (!("ok" in j)) continue;
      workers.push(j);
    } catch {}
  }
  if (!workers.length) { console.log(JSON.stringify({ ok: false, stage: "aggregate", error: "no worker JSON lines found in input" })); return; }

  const ok = workers.filter(w => w.ok === true);
  const failed = workers.filter(w => w.ok !== true);
  const totalTokens = ok.reduce((n, w) => n + (w.tokens?.total ?? 0), 0);

  const seen = new Map();
  let anonIdx = 0;
  for (const w of ok) {
    const src = w.label || w.agent || `worker-${++anonIdx}`;
    for (const f of extractFindings(w.result || "")) {
      const key = normalizeLine(f);
      if (!seen.has(key)) seen.set(key, { finding: f, sources: [src] });
      else if (!seen.get(key).sources.includes(src)) seen.get(key).sources.push(src);
    }
  }
  const unique = [...seen.values()].sort((a, b) => b.sources.length - a.sources.length).slice(0, 60);

  const digest = {
    ok: true,
    workers: workers.length,
    succeeded: ok.length,
    failed: failed.length,
    total_tokens: totalTokens,
    unique_findings: unique.length,
    failures: failed.map(w => ({ label: w.label || w.agent, error: (w.error || "unknown").slice(0, 120) })),
    consensus: unique.filter(u => u.sources.length > 1),
    findings: unique,
  };

  if (findingsOnly) {
    console.log(digest.consensus.map(c => `[${c.sources.join("+")}] ${c.finding}`).join("\n"));
    console.log("---");
    console.log(digest.findings.filter(f => f.sources.length === 1).map(c => `[${c.sources[0]}] ${c.finding}`).join("\n"));
    return;
  }
  console.log(JSON.stringify(digest, null, 1));
}

main();
