export interface CliOptions {
  prompt: string;
  promptFile: string | null;
  outputPath: string;
  aspect: string;
  refImages: string[];
  timeoutMs: number;
  retries: number;
  retryDelayMs: number;
  cacheDir: string | null;
  logFile: string | null;
  verbose: boolean;
}

export interface ToolCall {
  id: string;
  tool: string;
  status: string;
  command?: string;
}

export interface TokenUsage {
  input: number;
  cached_input: number;
  output: number;
  reasoning: number;
}

export interface CodexRunResult {
  threadId: string | null;
  toolCalls: ToolCall[];
  agentMessage: string | null;
  usage: TokenUsage | null;
  rawLogPath: string;
  durationMs: number;
}

export interface GenerateResult {
  status: "ok" | "error";
  path: string;
  bytes: number;
  elapsed_seconds: number;
  thread_id: string | null;
  attempts: number;
  cached: boolean;
  usage: TokenUsage | null;
  tool_calls: { tool: string; status: string }[];
  error?: string;
  error_kind?: ErrorKind;
}

export type ErrorKind =
  | "codex_not_installed"
  | "invalid_args"
  | "prompt_file_missing"
  | "spawn_failed"
  | "timeout"
  | "no_image_gen_tool_use"
  | "output_missing"
  | "invalid_png"
  | "agent_refused"
  | "lock_busy";

export const RETRYABLE: ReadonlySet<ErrorKind> = new Set([
  "spawn_failed",
  "timeout",
  "no_image_gen_tool_use",
  "output_missing",
  "invalid_png",
  "agent_refused",
]);

export class GenError extends Error {
  attempts?: number;
  constructor(public kind: ErrorKind, message: string, public retryable?: boolean) {
    super(message);
    this.retryable = retryable ?? RETRYABLE.has(kind);
  }
}
