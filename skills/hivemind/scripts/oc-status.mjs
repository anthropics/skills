import { readdirSync, readFileSync, existsSync } from "node:fs";
import { join, dirname } from "node:path";
import { fileURLToPath } from "node:url";

const RUNS_DIR = join(dirname(dirname(fileURLToPath(import.meta.url))), ".runs");

function loadRun(path) {
  const workers = new Map();
  for (const line of readFileSync(path, "utf8").split(/\r?\n/).filter(Boolean)) {
    let ev;
    try { ev = JSON.parse(line); } catch { continue; }
    const key = ev.label || "worker";
    const w = workers.get(key) || { label: key, agent: ev.agent || null, status: "running", tokens_total: null, duration_ms: null, error: null };
    if (ev.event === "start") { w.status = "running"; w.agent = ev.agent || w.agent; }
    if (ev.event === "done") { w.status = "done"; w.tokens_total = ev.tokens_total ?? w.tokens_total; w.duration_ms = ev.duration_ms ?? w.duration_ms; }
    if (ev.event === "fail") { w.status = "failed"; w.error = ev.error || ev.stage; }
    workers.set(key, w);
  }
  return [...workers.values()];
}

function summarize(runId, workers) {
  const done = workers.filter(w => w.status === "done");
  const failed = workers.filter(w => w.status === "failed");
  const running = workers.filter(w => w.status === "running");
  const lines = [
    `run ${runId}: ${done.length}/${workers.length} done, ${failed.length} failed, ${running.length} in flight`,
  ];
  for (const w of workers) {
    const tok = w.tokens_total != null ? `, ${w.tokens_total} tok` : "";
    lines.push(`  [${w.status.toUpperCase().padEnd(6)}] ${w.label}${w.agent ? ` (${w.agent})` : ""}${tok}${w.status === "failed" ? ` - ${w.error}` : ""}`);
  }
  return lines.join("\n");
}

function main() {
  if (!existsSync(RUNS_DIR)) { console.log("no runs recorded"); return; }
  const ids = process.argv.slice(2).filter(a => !a.startsWith("-"));
  const files = ids.length
    ? ids.map(id => ({ id, path: join(RUNS_DIR, `${id}.jsonl`) })).filter(f => existsSync(f.path))
    : readdirSync(RUNS_DIR).filter(f => f.endsWith(".jsonl")).sort().map(f => ({ id: f.replace(/\.jsonl$/, ""), path: join(RUNS_DIR, f) }));
  if (!files.length) { console.log("no matching runs"); return; }
  for (const f of files) console.log(summarize(f.id, loadRun(f.path)));
}

main();
