#!/usr/bin/env bun
import { readFile, mkdir, copyFile, stat } from "node:fs/promises";
import { homedir } from "node:os";
import path from "node:path";
import process from "node:process";
import { setTimeout as delay } from "node:timers/promises";
import { GenError, type CliOptions, type GenerateResult } from "./types.ts";
import { runCodexExec } from "./spawn.ts";
import { hasImageGenEvidence, verifyImageGenWasInvoked, verifyOutput } from "./validator.ts";
import { cacheKey, lookupCache, storeCache, FileLock } from "./cache.ts";
import { JsonLogger } from "./logger.ts";

const HELP = `codex-imagegen — generate images via Codex CLI's image_gen tool

Usage:
  codex-imagegen --image <output.png> [--prompt <text> | --prompt-file <path>] [options]

Required:
  --image <path>          Output PNG path
  --prompt <text>         Prompt text (or use --prompt-file)
  --prompt-file <path>    Read prompt from file

Options:
  --aspect <ratio>        Aspect ratio (1:1, 16:9, 9:16, 4:3, 2.35:1). Default: 1:1
  --ref <file>            Reference image (repeatable)
  --timeout <ms>          Codex exec timeout in ms. Default: 300000
  --retries <n>           Retry attempts on retryable errors. Default: 2
  --retry-delay <ms>      Base retry delay (exponential). Default: 1500
  --cache-dir <path>      Enable idempotency cache. Disabled by default.
  --log-file <path>       Append JSONL log
  -v, --verbose           Verbose stderr logging
  -h, --help              Show this help

Stdout: single JSON line on success or failure.
`;

const SHELL_METACHAR = /[;|&`$<>\n\r()'"]/;

function assertSafePath(label: string, value: string): void {
  if (SHELL_METACHAR.test(value)) {
    throw new GenError(
      "invalid_args",
      `${label} contains shell metacharacters and would be unsafe to interpolate into the codex instruction: ${value}`,
      false,
    );
  }
}

function parseArgs(argv: string[]): CliOptions {
  const opts: CliOptions = {
    prompt: "",
    promptFile: null,
    outputPath: "",
    aspect: "1:1",
    refImages: [],
    timeoutMs: 300_000,
    retries: 2,
    retryDelayMs: 1500,
    cacheDir: null,
    logFile: null,
    verbose: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    const next = () => argv[++i];
    switch (a) {
      case "--prompt": opts.prompt = next(); break;
      case "--prompt-file": opts.promptFile = next(); break;
      case "--image": opts.outputPath = next(); break;
      case "--aspect": opts.aspect = next(); break;
      case "--ref": opts.refImages.push(next()); break;
      case "--timeout": opts.timeoutMs = Number(next()); break;
      case "--retries": opts.retries = Number(next()); break;
      case "--retry-delay": opts.retryDelayMs = Number(next()); break;
      case "--cache-dir": opts.cacheDir = next(); break;
      case "--log-file": opts.logFile = next(); break;
      case "-v":
      case "--verbose": opts.verbose = true; break;
      case "-h":
      case "--help": process.stdout.write(HELP); process.exit(0);
      default: throw new GenError("invalid_args", `Unknown argument: ${a}`, false);
    }
  }
  if (!opts.outputPath) throw new GenError("invalid_args", "--image is required", false);
  if (opts.prompt && opts.promptFile) {
    throw new GenError("invalid_args", "--prompt and --prompt-file are mutually exclusive", false);
  }
  if (!opts.prompt && !opts.promptFile) {
    throw new GenError("invalid_args", "--prompt or --prompt-file required", false);
  }

  // Resolve every filesystem path to absolute up front, so behavior is
  // independent of the caller's cwd. This matters when the wrapper is
  // invoked from a skill running in an arbitrary working directory.
  const cwd = process.cwd();
  const toAbs = (p: string) => (path.isAbsolute(p) ? p : path.resolve(cwd, p));

  opts.outputPath = toAbs(opts.outputPath);
  if (opts.promptFile) opts.promptFile = toAbs(opts.promptFile);
  opts.refImages = opts.refImages.map(toAbs);
  if (opts.cacheDir) opts.cacheDir = toAbs(opts.cacheDir);
  if (opts.logFile) opts.logFile = toAbs(opts.logFile);

  // The output and ref paths are interpolated raw into the agent instruction
  // sent to `codex exec --sandbox danger-full-access`. A path containing shell
  // metacharacters could be misread by the agent's shell when it cp's the
  // result into place. Reject upfront rather than trusting the agent to quote.
  assertSafePath("--image path", opts.outputPath);
  for (const ref of opts.refImages) assertSafePath("--ref path", ref);

  return opts;
}

async function loadPrompt(opts: CliOptions): Promise<string> {
  if (opts.prompt) return opts.prompt;
  const file = opts.promptFile!;
  try {
    return await readFile(file, "utf-8");
  } catch {
    throw new GenError("prompt_file_missing", `Prompt file not found: ${file}`, false);
  }
}

function buildInstruction(prompt: string, opts: CliOptions): string {
  const refHint = opts.refImages.length > 0
    ? `\nREFERENCE IMAGES (attached above): ${opts.refImages.length} image(s) provided for style/composition guidance.\n`
    : "";
  return `You have an internal tool called image_gen for image generation. You MUST call it before doing anything else.

TASK: Generate an image with the spec below, then save to disk.

PROMPT:
${prompt}

ASPECT RATIO: ${opts.aspect}
OUTPUT PATH: ${opts.outputPath}
${refHint}
STEPS:
1. Call image_gen with the prompt and aspect ratio above${opts.refImages.length > 0 ? " (using the attached reference images for guidance)" : ""}.
2. Move or copy ONLY the image produced by that image_gen call from Codex default location ($CODEX_HOME/generated_images/...) to: ${opts.outputPath}
3. Verify with: ls -la ${opts.outputPath}
4. Reply with ONLY this JSON line (no markdown fences, no other text):
   {"status":"ok","path":"${opts.outputPath}","bytes":<file_size_in_bytes>}

HARD CONSTRAINTS:
- Do NOT search for, find, inspect, reuse, or copy any pre-existing files from $CODEX_HOME/generated_images/ or any other directory.
- Do NOT run ls/find/rg/grep/glob over $CODEX_HOME/generated_images/ before image_gen has been called.
- You MUST call image_gen first. Only after image_gen completes may you copy the newly created file from this turn.
- Do NOT use curl, wget, Python, or any external API.
- Do NOT use bash to fabricate an image; only image_gen produces real pixels.
- Use ONLY the image_gen internal tool.`;
}

async function attemptGenerate(
  opts: CliOptions,
  instruction: string,
  attempt: number,
  log: JsonLogger,
): Promise<{ bytes: number; threadId: string | null; usage: any; toolCalls: any[] }> {
  await log.info("attempt.start", { attempt, output: opts.outputPath, aspect: opts.aspect });

  const run = await runCodexExec({
    instruction,
    timeoutMs: opts.timeoutMs,
    refImages: opts.refImages,
  });

  await log.info("codex.completed", {
    duration_ms: run.durationMs,
    thread_id: run.threadId,
    tool_calls: run.toolCalls.length,
    usage: run.usage,
    raw_log: run.rawLogPath,
  });

  // verify: thread id must be present
  if (!run.threadId) {
    throw new GenError("agent_refused", "No thread id in event stream");
  }

  // verify image_gen ran in THIS thread. A PNG in this thread's
  // generated_images dir is the real signal (image_gen does not surface as a
  // stream item); the stream check is a forward-compatible fallback. The #185
  // shortcut (copying an unrelated history image) yields neither.
  const ver = await verifyImageGenWasInvoked(run.threadId);
  if (!hasImageGenEvidence(run.toolCalls, ver.ok)) {
    throw new GenError(
      "no_image_gen_tool_use",
      `image_gen was not invoked (no image_gen event in stream; ${ver.reason})`,
    );
  }

  // verify output
  const { bytes } = await verifyOutput(opts.outputPath);

  return {
    bytes,
    threadId: run.threadId,
    usage: run.usage,
    toolCalls: run.toolCalls.map((tc) => ({ tool: tc.tool, status: tc.status })),
  };
}

async function generate(opts: CliOptions, log: JsonLogger): Promise<GenerateResult> {
  const startEpoch = Date.now();
  const prompt = await loadPrompt(opts);

  // Cache lookup
  if (opts.cacheDir) {
    const key = cacheKey(prompt, opts.aspect, opts.refImages);
    const cached = await lookupCache(opts.cacheDir, key);
    if (cached) {
      await mkdir(path.dirname(opts.outputPath), { recursive: true });
      await copyFile(cached, opts.outputPath);
      const s = await stat(opts.outputPath);
      await log.info("cache.hit", { key, source: cached });
      return {
        status: "ok",
        path: opts.outputPath,
        bytes: s.size,
        elapsed_seconds: 0,
        thread_id: null,
        attempts: 0,
        cached: true,
        usage: null,
        tool_calls: [],
      };
    }
    await log.info("cache.miss", { key });
  }

  // lock to prevent concurrent codex exec
  const lockDir = opts.cacheDir ?? path.join(homedir(), ".cache", "baoyu-codex-imagegen");
  const lock = new FileLock(path.join(lockDir, "codex-exec.lock"));
  try {
    await lock.acquire(60_000);
  } catch (e) {
    throw new GenError("lock_busy", String(e), false);
  }

  await mkdir(path.dirname(opts.outputPath), { recursive: true });
  const instruction = buildInstruction(prompt, opts);

  let lastErr: GenError | null = null;
  let lastAttempt = 0;
  try {
    for (let attempt = 1; attempt <= opts.retries + 1; attempt++) {
      lastAttempt = attempt;
      try {
        const result = await attemptGenerate(opts, instruction, attempt, log);

        // write to cache
        if (opts.cacheDir) {
          const key = cacheKey(prompt, opts.aspect, opts.refImages);
          await storeCache(opts.cacheDir, key, opts.outputPath);
          await log.info("cache.stored", { key });
        }

        return {
          status: "ok",
          path: opts.outputPath,
          bytes: result.bytes,
          elapsed_seconds: Math.round((Date.now() - startEpoch) / 1000),
          thread_id: result.threadId,
          attempts: attempt,
          cached: false,
          usage: result.usage,
          tool_calls: result.toolCalls,
        };
      } catch (e) {
        lastErr = e instanceof GenError ? e : new GenError("spawn_failed", String(e));
        await log.warn("attempt.failed", {
          attempt,
          kind: lastErr.kind,
          retryable: lastErr.retryable,
          error: lastErr.message,
        });
        if (!lastErr.retryable || attempt > opts.retries) break;
        const wait = opts.retryDelayMs * Math.pow(2, attempt - 1);
        await log.info("retry.wait", { wait_ms: wait, next_attempt: attempt + 1 });
        await delay(wait);
      }
    }
  } finally {
    await lock.release();
  }

  const err = lastErr ?? new GenError("spawn_failed", "Unknown failure");
  err.attempts = lastAttempt;
  throw err;
}

async function main() {
  let opts: CliOptions;
  try {
    opts = parseArgs(process.argv.slice(2));
  } catch (e) {
    const err = e instanceof GenError ? e : new GenError("invalid_args", String(e), false);
    process.stderr.write(`Error: ${err.message}\n`);
    process.exit(2);
  }

  const log = new JsonLogger(opts.logFile, opts.verbose);
  await log.info("start", { output: opts.outputPath, aspect: opts.aspect, refs: opts.refImages.length });

  try {
    const result = await generate(opts, log);
    await log.info("done", { bytes: result.bytes, attempts: result.attempts, cached: result.cached });
    process.stdout.write(JSON.stringify(result) + "\n");
    process.exit(0);
  } catch (e) {
    const err = e instanceof GenError ? e : new GenError("spawn_failed", String(e));
    await log.error("failed", { kind: err.kind, error: err.message, attempts: err.attempts ?? 0 });
    const out: GenerateResult = {
      status: "error",
      path: opts.outputPath,
      bytes: 0,
      elapsed_seconds: 0,
      thread_id: null,
      attempts: err.attempts ?? 0,
      cached: false,
      usage: null,
      tool_calls: [],
      error: err.message,
      error_kind: err.kind,
    };
    process.stdout.write(JSON.stringify(out) + "\n");
    process.exit(1);
  }
}

main();
