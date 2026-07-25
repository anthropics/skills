import { appendFile, mkdir } from "node:fs/promises";
import path from "node:path";

export interface LogEntry {
  ts: string;
  level: "info" | "warn" | "error";
  event: string;
  [k: string]: unknown;
}

export class JsonLogger {
  constructor(private logFile: string | null, public verbose: boolean) {}

  async log(level: LogEntry["level"], event: string, extra: Record<string, unknown> = {}): Promise<void> {
    const entry: LogEntry = { ts: new Date().toISOString(), level, event, ...extra };
    const line = JSON.stringify(entry);
    if (this.verbose) process.stderr.write(`[${level}] ${event} ${jsonExtras(extra)}\n`);
    if (this.logFile) {
      await mkdir(path.dirname(this.logFile), { recursive: true });
      await appendFile(this.logFile, line + "\n", "utf-8");
    }
  }

  info(event: string, extra?: Record<string, unknown>) {
    return this.log("info", event, extra);
  }
  warn(event: string, extra?: Record<string, unknown>) {
    return this.log("warn", event, extra);
  }
  error(event: string, extra?: Record<string, unknown>) {
    return this.log("error", event, extra);
  }
}

function jsonExtras(extra: Record<string, unknown>): string {
  const entries = Object.entries(extra);
  if (entries.length === 0) return "";
  return entries.map(([k, v]) => `${k}=${typeof v === "string" ? v : JSON.stringify(v)}`).join(" ");
}
