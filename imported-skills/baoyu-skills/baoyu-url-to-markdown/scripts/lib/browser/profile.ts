import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import process from "node:process";
import { spawnSync } from "node:child_process";

export interface ResolveSharedChromeProfileDirOptions {
  envNames?: string[];
  appDataDirName?: string;
  profileDirName?: string;
}

export interface FindExistingChromeDebugPortOptions {
  profileDir: string;
  timeoutMs?: number;
}

interface ChromeVersionResponse {
  webSocketDebuggerUrl?: string;
}

const CHROME_LOCK_FILE_NAMES = ["SingletonLock", "SingletonSocket", "SingletonCookie", "chrome.pid"] as const;

function resolveDataBaseDir(): string {
  if (process.platform === "darwin") {
    return path.join(os.homedir(), "Library", "Application Support");
  }
  if (process.platform === "win32") {
    return process.env.APPDATA ?? path.join(os.homedir(), "AppData", "Roaming");
  }
  return process.env.XDG_DATA_HOME ?? path.join(os.homedir(), ".local", "share");
}

export function resolveSharedChromeProfileDir(
  options: ResolveSharedChromeProfileDirOptions = {},
): string {
  for (const envName of options.envNames ?? []) {
    const override = process.env[envName]?.trim();
    if (override) {
      return path.resolve(override);
    }
  }

  const appDataDirName = options.appDataDirName ?? "baoyu-skills";
  const profileDirName = options.profileDirName ?? "chrome-profile";
  return path.join(resolveDataBaseDir(), appDataDirName, profileDirName);
}

export function resolveChromeProfileDir(profileDir?: string): string {
  if (profileDir?.trim()) {
    return path.resolve(profileDir.trim());
  }

  return resolveSharedChromeProfileDir({
    envNames: ["BAOYU_CHROME_PROFILE_DIR"],
    appDataDirName: "baoyu-skills",
    profileDirName: "chrome-profile",
  });
}

export function ensureChromeProfileDir(profileDir: string): string {
  fs.mkdirSync(profileDir, { recursive: true });
  return profileDir;
}

export function hasChromeLockArtifacts(entries: readonly string[]): boolean {
  return CHROME_LOCK_FILE_NAMES.some((name) => entries.includes(name));
}

export function shouldRetryChromeLaunchRecovery(options: {
  hasLockArtifacts: boolean;
  hasLiveOwner: boolean;
}): boolean {
  return options.hasLockArtifacts && !options.hasLiveOwner;
}

export function findChromeProcessUsingProfile(profileDir: string): boolean {
  if (process.platform === "win32") {
    return false;
  }

  try {
    const result = spawnSync("ps", ["aux"], {
      encoding: "utf8",
      timeout: 5_000,
    });
    if (result.status !== 0 || !result.stdout) {
      return false;
    }

    return result.stdout
      .split("\n")
      .some((line) => line.includes(`--user-data-dir=${profileDir}`));
  } catch {
    return false;
  }
}

export function cleanChromeLockArtifacts(profileDir: string): void {
  for (const name of CHROME_LOCK_FILE_NAMES) {
    try {
      fs.unlinkSync(path.join(profileDir, name));
    } catch {
      // Ignore missing files and continue cleaning the remaining artifacts.
    }
  }
}

export async function listChromeProfileEntries(profileDir: string): Promise<string[]> {
  try {
    return await fs.promises.readdir(profileDir);
  } catch {
    return [];
  }
}

async function fetchWithTimeout(url: string, timeoutMs = 3_000): Promise<Response> {
  const controller = new AbortController();
  const timer = setTimeout(() => controller.abort(), timeoutMs);
  try {
    return await fetch(url, {
      redirect: "follow",
      signal: controller.signal,
    });
  } finally {
    clearTimeout(timer);
  }
}

async function fetchJson<T>(url: string, timeoutMs = 3_000): Promise<T> {
  const response = await fetchWithTimeout(url, timeoutMs);
  if (!response.ok) {
    throw new Error(`Request failed: ${response.status} ${response.statusText}`);
  }
  return (await response.json()) as T;
}

async function isDebugPortReady(port: number, timeoutMs = 3_000): Promise<boolean> {
  try {
    const version = await fetchJson<ChromeVersionResponse>(`http://127.0.0.1:${port}/json/version`, timeoutMs);
    return Boolean(version.webSocketDebuggerUrl);
  } catch {
    return false;
  }
}

function parseDevToolsActivePort(filePath: string): { port: number; wsPath: string } | null {
  try {
    const content = fs.readFileSync(filePath, "utf8");
    const lines = content.split(/\r?\n/);
    const port = Number.parseInt(lines[0]?.trim() ?? "", 10);
    const wsPath = lines[1]?.trim() ?? "";
    if (port > 0 && wsPath) {
      return { port, wsPath };
    }
  } catch {
    // Ignore and fall back to process inspection.
  }

  return null;
}

export async function findExistingChromeDebugPort(
  options: FindExistingChromeDebugPortOptions,
): Promise<number | null> {
  const timeoutMs = options.timeoutMs ?? 3_000;
  const activePort = parseDevToolsActivePort(path.join(options.profileDir, "DevToolsActivePort"));
  if (activePort && await isDebugPortReady(activePort.port, timeoutMs)) {
    return activePort.port;
  }

  if (process.platform === "win32") {
    return null;
  }

  try {
    const result = spawnSync("ps", ["aux"], {
      encoding: "utf8",
      timeout: 5_000,
    });
    if (result.status !== 0 || !result.stdout) {
      return null;
    }

    const lines = result.stdout
      .split("\n")
      .filter((line) => line.includes(options.profileDir) && line.includes("--remote-debugging-port="));

    for (const line of lines) {
      const match = line.match(/--remote-debugging-port=(\d+)/);
      const port = Number.parseInt(match?.[1] ?? "", 10);
      if (port > 0 && await isDebugPortReady(port, timeoutMs)) {
        return port;
      }
    }
  } catch {
    // Ignore and report no reusable debugger.
  }

  return null;
}
