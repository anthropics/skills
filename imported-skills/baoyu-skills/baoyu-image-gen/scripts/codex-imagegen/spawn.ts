import { spawn } from "node:child_process";
import { writeFile, mkdtemp } from "node:fs/promises";
import { tmpdir } from "node:os";
import path from "node:path";
import { GenError, type CodexRunResult } from "./types.ts";
import { parseEventStream } from "./parser.ts";

export interface SpawnInput {
  instruction: string;
  timeoutMs: number;
  refImages?: string[];
}

export async function runCodexExec(input: SpawnInput): Promise<CodexRunResult> {
  const start = Date.now();
  const logDir = await mkdtemp(path.join(tmpdir(), "codex-imggen-"));
  const rawLogPath = path.join(logDir, "stream.jsonl");

  // --skip-git-repo-check: lets the wrapper run from non-git cwds
  //   (e.g. /tmp, or a skill installed under ~/.claude/plugins/...).
  //   Without it, codex refuses with "Not inside a trusted directory".
  const args = [
    "exec",
    "--json",
    "--sandbox",
    "danger-full-access",
    "--skip-git-repo-check",
  ];
  for (const img of input.refImages ?? []) {
    args.push("--image", img);
  }
  args.push("-");

  let timedOut = false;
  const child = spawn("codex", args, { stdio: ["pipe", "pipe", "pipe"] });

  let stdout = "";
  let stderr = "";
  child.stdout.on("data", (chunk) => {
    stdout += chunk.toString();
  });
  child.stderr.on("data", (chunk) => {
    stderr += chunk.toString();
  });

  child.stdin.write(input.instruction);
  child.stdin.end();

  const timer = setTimeout(() => {
    timedOut = true;
    child.kill("SIGTERM");
    setTimeout(() => child.kill("SIGKILL"), 2000);
  }, input.timeoutMs);

  const exit = await new Promise<{ code: number | null; signal: NodeJS.Signals | null }>((resolve) => {
    child.on("close", (code, signal) => resolve({ code, signal }));
  });
  clearTimeout(timer);

  await writeFile(rawLogPath, stdout + (stderr ? `\n--- stderr ---\n${stderr}` : ""));

  if (timedOut) {
    throw new GenError("timeout", `codex exec exceeded ${input.timeoutMs}ms (log: ${rawLogPath})`);
  }
  if (exit.code !== 0) {
    if (stderr.includes("command not found") || stderr.includes("not found: codex")) {
      throw new GenError("codex_not_installed", "codex CLI not installed", false);
    }
    throw new GenError(
      "spawn_failed",
      `codex exec exited ${exit.code} signal=${exit.signal} (log: ${rawLogPath})`,
    );
  }

  const parsed = parseEventStream(stdout);
  return {
    ...parsed,
    rawLogPath,
    durationMs: Date.now() - start,
  };
}
