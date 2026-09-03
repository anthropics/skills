import { spawnSync } from "node:child_process";
import { appendFileSync, existsSync } from "node:fs";
import { resolve, dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const __dirname = dirname(fileURLToPath(import.meta.url));
const WORKER = join(__dirname, "..", "oc-worker.mjs");
const RESULTS_FILE = process.env.HIVEMIND_BENCH_RESULTS || "bench-results.jsonl";

function parseArgs(argv) {
  const out = { repo: process.cwd(), configs: "a,b,c", tasks: null };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--repo") out.repo = resolve(argv[++i]);
    else if (a === "--configs") out.configs = argv[++i].toLowerCase();
    else if (a === "--task") out.tasks = [Number(argv[++i])];
  }
  return out;
}

function resolveBin(name) {
  const probe = spawnSync("where.exe", [name], { encoding: "utf8" });
  if (probe.status === 0) {
    const first = probe.stdout.split(/\r?\n/).map(s => s.trim()).filter(Boolean)[0];
    if (first) return first;
  }
  return name;
}

const TASKS = [
  { id: 1, kind: "explain", prompt: "Read the main entry point of this repository and explain in under 200 words what the project does, how it starts, and its three most important files. Cite file paths." },
  { id: 2, kind: "tests", prompt: "Find one small, pure utility function in this codebase and write a unit test file for it using the project's existing test framework and conventions. Do not modify source files." },
  { id: 3, kind: "bugfix", prompt: "Scan for a TODO or FIXME comment that marks a small, self-contained fix (under ~30 lines). Implement exactly that fix. If none is suitable, fix the smallest real bug you can identify instead." },
  { id: 4, kind: "refactor", prompt: "Pick ONE function longer than 40 lines with high cyclomatic complexity and extract 1-2 well-named helper functions from it. Behavior must be unchanged. Touch nothing else." },
  { id: 5, kind: "review", prompt: "Review the most recently modified source file in this repository as a senior engineer. Report only defects that would actually occur at runtime, each with the input that triggers it, plus file:line references. If there are none, say so in one line." },
];

function runA(task, bin) {
  const t0 = Date.now();
  const r = spawnSync(bin, ["-p", task.prompt, "--output-format", "json"], {
    cwd: task.cwd, encoding: "utf8", maxBuffer: 256 * 1024 * 1024,
    timeout: 900000, windowsHide: true,
    env: { ...process.env },
  });
  let usage = null, costUsd = null, result = "";
  try {
    const j = JSON.parse(r.stdout.trim().split(/\r?\n/).filter(Boolean).pop());
    result = j.result || "";
    costUsd = j.total_cost_usd ?? null;
    usage = j.usage ? { in: j.usage.input_tokens, out: j.usage.output_tokens } : null;
  } catch {
    result = ((r.stdout || "") + (r.stderr || "")).trim().slice(-2000);
  }
  return { ok: Boolean(result), result, tokens: usage, cost_usd: costUsd, duration_ms: Date.now() - t0 };
}

function runB(task, node) {
  const t0 = Date.now();
  const r = spawnSync(node, [WORKER, "--dir", task.cwd, "--timeout", "900", task.prompt], {
    cwd: task.cwd, encoding: "utf8", maxBuffer: 256 * 1024 * 1024,
    timeout: 960000, windowsHide: true,
  });
  try {
    const j = JSON.parse((r.stdout || "").trim().split(/\r?\n/).filter(Boolean).pop());
    return { ok: j.ok === true, result: j.result || "", tokens: j.tokens ? { in: j.tokens.input, out: j.tokens.output } : null, cost_usd: j.cost_usd, duration_ms: j.duration_ms ?? Date.now() - t0 };
  } catch {
    return { ok: false, result: ((r.stderr || "") + (r.error || "")).slice(0, 500), tokens: null, cost_usd: null, duration_ms: Date.now() - t0 };
  }
}

function runC(task, claudeBin, node) {
  const orchestratorPrompt =
    `You are an orchestrator with access to Bash. Complete this task by delegating to TWO free opencode workers ` +
    `using parallel Bash tool calls in one message:\n` +
    `node "${WORKER}" --dir "${task.cwd}" --timeout 900 "<SUBTASK_A>"\n` +
    `node "${WORKER}" --dir "${task.cwd}" --timeout 900 "<SUBTASK_B>"\n` +
    `Split the work sensibly, wait for both compact JSON results, then integrate their outputs yourself ` +
    `and produce the final answer. Never paste raw streams into your context.\nTASK: ${task.prompt}`;
  const t0 = Date.now();
  const r = spawnSync(claudeBin, ["-p", orchestratorPrompt, "--output-format", "json",
    "--allowedTools", "Bash(node:*) Read(*) Grep(*) Glob(*)"], {
    cwd: task.cwd, encoding: "utf8", maxBuffer: 256 * 1024 * 1024,
    timeout: 1200000, windowsHide: true, env: { ...process.env },
  });
  let usage = null, costUsd = null, result = "";
  try {
    const j = JSON.parse(r.stdout.trim().split(/\r?\n/).filter(Boolean).pop());
    result = j.result || "";
    costUsd = j.total_cost_usd ?? null;
    usage = j.usage ? { in: j.usage.input_tokens, out: j.usage.output_tokens } : null;
  } catch {
    result = ((r.stdout || "") + (r.stderr || "")).trim().slice(-2000);
  }
  return { ok: Boolean(result), result, tokens: usage, cost_usd: costUsd, duration_ms: Date.now() - t0 };
}

async function main() {
  const opts = parseArgs(process.argv.slice(2));
  if (!existsSync(opts.repo)) { console.error(`repo not found: ${opts.repo}`); process.exit(1); }
  const configs = opts.configs.split(",").map(s => s.trim()).filter(Boolean);
  const tasks = TASKS.filter(t => !opts.tasks || opts.tasks.includes(t.id))
    .map(t => ({ ...t, cwd: opts.repo }));

  const claudeBin = resolveBin("claude");
  const nodeBin = process.execPath;

  console.log(`hivemind bench | repo=${opts.repo} | configs=${configs.join("+")} | tasks=${tasks.map(t => t.id).join(",")}`);

  for (const task of tasks) {
    for (const cfg of configs) {
      const runner = cfg === "a" ? () => runA(task, claudeBin)
        : cfg === "b" ? () => runB(task, nodeBin)
        : cfg === "c" ? () => runC(task, claudeBin, nodeBin)
        : null;
      if (!runner) continue;
      process.stdout.write(`task ${task.id} (${task.kind}) config ${cfg.toUpperCase()} ... `);
      const res = runner();
      const record = { ts: new Date().toISOString(), task_id: task.id, kind: task.kind, config: cfg.toUpperCase(), repo: opts.repo, ...res };
      appendFileSync(resolve(RESULTS_FILE), JSON.stringify(record) + "\n");
      console.log(`${res.ok ? "ok" : "FAIL"} | ${Math.round(res.duration_ms / 1000)}s | tokens=${JSON.stringify(res.tokens)} | cost=$${res.cost_usd ?? "?"}`);
    }
  }

  console.log(`\nresults appended to ${resolve(RESULTS_FILE)}`);
  console.log("next: grade each artifact blind with scripts/bench/grader-prompt.md, add score field per line.");
}

main().catch(e => { console.error(e); process.exit(1); });
