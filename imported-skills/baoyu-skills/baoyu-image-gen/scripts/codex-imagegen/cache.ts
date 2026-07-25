import { createHash } from "node:crypto";
import { mkdir, readFile, writeFile, copyFile, stat } from "node:fs/promises";
import { existsSync, openSync, closeSync } from "node:fs";
import path from "node:path";
import { setTimeout as delay } from "node:timers/promises";

export function cacheKey(prompt: string, aspect: string, refs: string[]): string {
  const h = createHash("sha256");
  h.update(prompt);
  h.update("|");
  h.update(aspect);
  h.update("|");
  for (const r of [...refs].sort()) h.update(r);
  return h.digest("hex").slice(0, 16);
}

export async function lookupCache(cacheDir: string, key: string): Promise<string | null> {
  const entry = path.join(cacheDir, `${key}.png`);
  try {
    const s = await stat(entry);
    if (s.size > 1000) return entry;
  } catch {}
  return null;
}

export async function storeCache(cacheDir: string, key: string, sourcePath: string): Promise<void> {
  await mkdir(cacheDir, { recursive: true });
  const entry = path.join(cacheDir, `${key}.png`);
  await copyFile(sourcePath, entry);
}

export class FileLock {
  private fd: number | null = null;
  constructor(private lockPath: string) {}

  async acquire(timeoutMs = 30_000): Promise<void> {
    const start = Date.now();
    await mkdir(path.dirname(this.lockPath), { recursive: true });
    while (Date.now() - start < timeoutMs) {
      try {
        this.fd = openSync(this.lockPath, "wx");
        return;
      } catch (e: any) {
        if (e.code !== "EEXIST") throw e;
        if (await this.isStale()) {
          try {
            await this.release(true);
          } catch {}
          continue;
        }
        await delay(200);
      }
    }
    throw new Error(`Failed to acquire lock at ${this.lockPath} within ${timeoutMs}ms`);
  }

  private async isStale(): Promise<boolean> {
    try {
      const s = await stat(this.lockPath);
      return Date.now() - s.mtimeMs > 10 * 60 * 1000;
    } catch {
      return true;
    }
  }

  async release(force = false): Promise<void> {
    if (this.fd != null) {
      try {
        closeSync(this.fd);
      } catch {}
      this.fd = null;
    }
    if (existsSync(this.lockPath) || force) {
      const { unlink } = await import("node:fs/promises");
      try {
        await unlink(this.lockPath);
      } catch {}
    }
  }
}
