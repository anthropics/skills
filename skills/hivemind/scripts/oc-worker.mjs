import { spawnSync, spawn } from "node:child_process";
import { setTimeout as delay } from "node:timers/promises";
import { readFileSync, statSync, mkdirSync, appendFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const SERVER = process.env.HIVEMIND_SERVER_URL || "http://127.0.0.1:4096";
// SERVER comes from the environment and PORT is handed to a child process, so validate
// both here - and still emit exactly one JSON line when they are unusable.
const PORT = resolvePort(SERVER);

function bail(error) {
  console.log(JSON.stringify({ ok: false, stage: "args", error, result: "", tokens: null, cost_usd: null, duration_ms: 0 }));
  process.exit(0);
}

function resolvePort(server) {
  let url;
  try { url = new URL(server); } catch { bail("HIVEMIND_SERVER_URL is not a valid URL"); }
  const port = url.port || "4096";
  if (!/^[0-9]{1,5}$/.test(port) || Number(port) < 1 || Number(port) > 65535) bail("HIVEMIND_SERVER_URL has an invalid port");
  return port;
}

const DEFAULT_MODEL = "opencode/mimo-v2.5-free";
const STDERR_TAIL = 300;
const RUNS_DIR = join(dirname(dirname(fileURLToPath(import.meta.url))), ".runs");

let RUN = null, LABEL = null, AGENT = null;

function logRun(event, extra = {}) {
  if (!RUN) return;
  try {
    mkdirSync(RUNS_DIR, { recursive: true });
    appendFileSync(join(RUNS_DIR, `${RUN}.jsonl`), JSON.stringify({ ts: Date.now(), event, label: LABEL, agent: AGENT, ...extra }) + "\n");
  } catch {}
}

function parseArgs(argv) {
  const out = { agent: null, model: null, dir: null, timeoutMs: 600000, run: null, label: null, task: [] };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === "--agent") out.agent = argv[++i] ?? null;
    else if (a === "--model") out.model = argv[++i] ?? null;
    else if (a === "--dir") out.dir = argv[++i] ?? null;
    else if (a === "--timeout") out.timeoutMs = Number(argv[++i]) * 1000 || out.timeoutMs;
    else if (a === "--run") out.run = argv[++i] ?? null;
    else if (a === "--label") out.label = argv[++i] ?? null;
    else out.task.push(a);
  }
  out.task = out.task.join(" ").trim();
  return out;
}

function fail(stage, message, extra = {}) {
  const payload = { ok: false, stage, error: String(message).slice(0, STDERR_TAIL), result: "", tokens: null, cost_usd: null, duration_ms: 0, ...extra };
  if (payload.duration_ms) logRun("fail", { stage, error: payload.error, duration_ms: payload.duration_ms });
  console.log(JSON.stringify(payload));
  process.exit(0);
}

async function alive(url = SERVER, ms = 500) {
  try {
    await fetch(url, { signal: AbortSignal.timeout(ms) });
    return true;
  } catch {
    return false;
  }
}

function resolveOpencode() {
  if (process.platform !== "win32") {
    const posix = spawnSync("which", ["opencode"], { encoding: "utf8" });
    const path = posix.status === 0 ? posix.stdout.trim().split(/\r?\n/)[0] : "";
    return path || "opencode";
  }
  // Windows: npm installs a .cmd shim, and Node's EINVAL policy blocks spawning
  // .cmd directly - so resolve the real .exe (parsing the shim when needed).
  const probe = spawnSync("where.exe", ["opencode"], { encoding: "utf8" });
  if (probe.status === 0) {
    const lines = probe.stdout.split(/\r?\n/).map(s => s.trim()).filter(Boolean);
    const exe = lines.find(l => l.toLowerCase().endsWith(".exe"));
    if (exe) return exe;
    const cmdShim = lines.find(l => l.toLowerCase().endsWith(".cmd"));
    if (cmdShim) {
      try {
        const body = readFileSync(cmdShim, "utf8");
        const m = body.match(/"%dp0%\\(.*?\.exe)"/i);
        if (m) return join(dirname(cmdShim), m[1]);
      } catch {}
    }
  }
  return "opencode";
}

async function ensureServer(bin) {
  if (await alive()) return [];
  // Args array with shell:false - nothing here is shell-interpolated, so a hostile
  // HIVEMIND_SERVER_URL cannot inject syntax and paths with spaces need no quoting.
  const child = spawn(bin, ["serve", "--port", PORT], { shell: false, detached: true, stdio: "ignore", windowsHide: true });
  child.unref();
  for (let i = 0; i < 10; i++) {
    await delay(500);
    if (await alive()) return ["--attach", SERVER];
  }
  return [];
}

async function main() {
  const t0 = Date.now();
  const opts = parseArgs(process.argv.slice(2));
  if (!opts.task) fail("args", "no task given");
  RUN = opts.run; LABEL = opts.label || opts.agent || "worker"; AGENT = opts.agent;
  logRun("start", { model: opts.model, dir: opts.dir });
  if (opts.dir && !existsDir(opts.dir)) fail("args", `--dir does not exist: ${opts.dir}`);

  const bin = resolveOpencode();
  const attachArgs = await ensureServer(bin);

  const baseArgs = ["run"];
  if (opts.agent) baseArgs.push("--agent", opts.agent);
  if (opts.model) baseArgs.push("--model", opts.model);
  if (opts.dir) baseArgs.push("--dir", opts.dir);
  baseArgs.push(...attachArgs);

  let r = spawnSync(bin, [...baseArgs, "--format", "json", opts.task], {
    encoding: "utf8",
    maxBuffer: 256 * 1024 * 1024,
    timeout: opts.timeoutMs,
    env: { ...process.env },
    windowsHide: true,
  });

  if (!r.stdout || !r.stdout.trim()) {
    const tailErr = ((r.stderr || "") + " " + (r.error ? String(r.error) : "")).trim();
    const retry = spawnSync(bin, [...baseArgs, opts.task], {
      encoding: "utf8", maxBuffer: 64 * 1024 * 1024, timeout: opts.timeoutMs, windowsHide: true,
    });
    const text = (retry.stdout || "").trim();
    if (text) {
      logRun("done", { degraded: true, duration_ms: Date.now() - t0 });
      console.log(JSON.stringify({ ok: true, degraded: "plain-format-fallback", result: text.slice(-20000), tokens: null, cost_usd: null, duration_ms: Date.now() - t0, agent: opts.agent, model: opts.model }));
      return;
    }
    fail("exec", tailErr || `opencode exited ${r.status}`, { duration_ms: Date.now() - t0 });
  }

  const parsed = parseNdjson(r.stdout);
  if (!parsed.ok) {
    fail(parsed.stage, parsed.error, { duration_ms: Date.now() - t0, model: opts.model });
  }

  const duration = Date.now() - t0;
  logRun("done", { tokens_total: parsed.tokens?.total ?? null, duration_ms: duration });
  console.log(JSON.stringify({
    ok: true,
    result: parsed.result.slice(-20000),
    tokens: parsed.tokens,
    cost_usd: parsed.costUsd,
    session_id: parsed.sessionId,
    duration_ms: duration,
    label: LABEL,
    agent: opts.agent,
    model: opts.model ?? DEFAULT_MODEL,
  }));
}

function parseNdjson(stdout) {
  const lines = stdout.split(/\r?\n/).filter(l => l.trim());
  const texts = [];
  let tokens = null, costUsd = null, sessionId = null, sawFinish = false;
  for (const line of lines) {
    let ev;
    try { ev = JSON.parse(line); } catch { continue; }
    if (ev.type === "error") {
      const msg = ev.error?.data?.message || ev.error?.message || "APIError";
      return { ok: false, stage: "api", error: msg };
    }
    if (ev.type === "text" && ev.part?.text != null) texts.push(ev.part.text);
    if (ev.type === "step_finish" && ev.part) {
      sawFinish = true;
      sessionId = ev.sessionID || sessionId;
      if (ev.part.tokens) tokens = ev.part.tokens;
      if (typeof ev.part.cost === "number") costUsd = ev.part.cost;
    }
  }
  const result = texts.join("\n").trim();
  if (!result && !sawFinish) return { ok: false, stage: "parse", error: "no text parts and no step_finish in stream" };
  if (!result) return { ok: false, stage: "empty", error: "worker produced no text output" };
  return { ok: true, result, tokens, costUsd, sessionId };
}

function existsDir(p) {
  try { return statSync(p).isDirectory(); } catch { return false; }
}

main().catch(e => fail("crash", e?.stack || e));
