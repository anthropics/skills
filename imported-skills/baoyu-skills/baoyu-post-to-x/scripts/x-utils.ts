import { execSync, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

import {
  CdpConnection,
  findChromeExecutable as findChromeExecutableBase,
  findExistingChromeDebugPort as findExistingChromeDebugPortBase,
  getFreePort as getFreePortBase,
  gracefulKillChrome,
  killChrome,
  launchChrome as launchChromeBase,
  openPageSession,
  resolveSharedChromeProfileDir,
  sleep,
  waitForChromeDebugPort,
  type PlatformCandidates,
} from 'baoyu-chrome-cdp';

export { CdpConnection, gracefulKillChrome, killChrome, openPageSession, sleep, waitForChromeDebugPort };
export type { PlatformCandidates } from 'baoyu-chrome-cdp';

const X_SESSION_URLS = ['https://x.com/', 'https://twitter.com/'] as const;
const REQUIRED_X_SESSION_COOKIES = ['auth_token', 'ct0'] as const;

interface CookieLike {
  name?: string;
  value?: string | null;
}

interface NetworkGetCookiesResult {
  cookies?: CookieLike[];
}

export const CHROME_CANDIDATES_BASIC: PlatformCandidates = {
  darwin: [
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    '/Applications/Google Chrome Canary.app/Contents/MacOS/Google Chrome Canary',
    '/Applications/Chromium.app/Contents/MacOS/Chromium',
  ],
  win32: [
    'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
    'C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe',
  ],
  default: [
    '/usr/bin/google-chrome',
    '/usr/bin/chromium',
    '/usr/bin/chromium-browser',
  ],
};

export const CHROME_CANDIDATES_FULL: PlatformCandidates = {
  darwin: [
    '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome',
    '/Applications/Google Chrome Canary.app/Contents/MacOS/Google Chrome Canary',
    '/Applications/Google Chrome Beta.app/Contents/MacOS/Google Chrome Beta',
    '/Applications/Chromium.app/Contents/MacOS/Chromium',
    '/Applications/Microsoft Edge.app/Contents/MacOS/Microsoft Edge',
  ],
  win32: [
    'C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe',
    'C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe',
    'C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe',
    'C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe',
  ],
  default: [
    '/usr/bin/google-chrome',
    '/usr/bin/google-chrome-stable',
    '/usr/bin/chromium',
    '/usr/bin/chromium-browser',
    '/snap/bin/chromium',
    '/usr/bin/microsoft-edge',
  ],
};

export function findChromeExecutable(candidates: PlatformCandidates): string | undefined {
  return findChromeExecutableBase({
    candidates,
    envNames: ['X_BROWSER_CHROME_PATH'],
  });
}

let _wslHome: string | null | undefined;
function getWslWindowsHome(): string | null {
  if (_wslHome !== undefined) return _wslHome;
  if (!process.env.WSL_DISTRO_NAME) { _wslHome = null; return null; }
  try {
    const raw = execSync('cmd.exe /C "echo %USERPROFILE%"', { encoding: 'utf-8', timeout: 5000 }).trim().replace(/\r/g, '');
    _wslHome = execSync(`wslpath -u "${raw}"`, { encoding: 'utf-8', timeout: 5000 }).trim() || null;
  } catch { _wslHome = null; }
  return _wslHome;
}

export function getDefaultProfileDir(): string {
  return resolveSharedChromeProfileDir({
    envNames: ['BAOYU_CHROME_PROFILE_DIR', 'X_BROWSER_PROFILE_DIR'],
    wslWindowsHome: getWslWindowsHome(),
  });
}

export async function getFreePort(): Promise<number> {
  return await getFreePortBase('X_BROWSER_DEBUG_PORT');
}

export async function findExistingChromeDebugPort(profileDir: string): Promise<number | null> {
  return await findExistingChromeDebugPortBase({ profileDir });
}

const CHROME_LOCK_FILES = ['SingletonLock', 'SingletonSocket', 'SingletonCookie', 'chrome.pid'] as const;

export function hasChromeLockArtifacts(entries: readonly string[]): boolean {
  return CHROME_LOCK_FILES.some((name) => entries.includes(name));
}

export function shouldRetryChromeLaunch(options: {
  lockArtifactsPresent: boolean;
  hasLiveOwner: boolean;
}): boolean {
  return options.lockArtifactsPresent && !options.hasLiveOwner;
}

export function buildXSessionCookieMap(cookies: readonly CookieLike[]): Record<string, string> {
  const cookieMap: Record<string, string> = {};
  for (const cookie of cookies) {
    const name = cookie.name?.trim();
    const value = cookie.value?.trim();
    if (!name || !value) {
      continue;
    }
    cookieMap[name] = value;
  }
  return cookieMap;
}

export function hasRequiredXSessionCookies(cookieMap: Record<string, string>): boolean {
  return REQUIRED_X_SESSION_COOKIES.every((name) => Boolean(cookieMap[name]));
}

export async function readXSessionCookieMap(
  cdp: CdpConnection,
  sessionId?: string,
): Promise<Record<string, string>> {
  const { cookies } = await cdp.send<NetworkGetCookiesResult>(
    'Network.getCookies',
    { urls: [...X_SESSION_URLS] },
    {
      sessionId,
      timeoutMs: 5_000,
    },
  );
  return buildXSessionCookieMap(cookies ?? []);
}

export async function waitForXSessionPersistence(options: {
  cdp: CdpConnection;
  sessionId?: string;
  timeoutMs?: number;
  pollIntervalMs?: number;
}): Promise<boolean> {
  const timeoutMs = options.timeoutMs ?? 15_000;
  const pollIntervalMs = options.pollIntervalMs ?? 1_000;
  const start = Date.now();

  while (Date.now() - start < timeoutMs) {
    const cookieMap = await readXSessionCookieMap(options.cdp, options.sessionId).catch(() => ({}));
    if (hasRequiredXSessionCookies(cookieMap)) {
      return true;
    }
    await sleep(pollIntervalMs);
  }

  return false;
}

function cleanStaleLockFiles(profileDir: string): void {
  for (const name of CHROME_LOCK_FILES) {
    try { fs.unlinkSync(path.join(profileDir, name)); } catch {}
  }
}

function hasLiveChromeOwner(profileDir: string): boolean {
  if (process.platform === 'win32') return false;
  try {
    const result = spawnSync('ps', ['aux'], {
      encoding: 'utf8',
      timeout: 5000,
    });
    if (result.status !== 0 || !result.stdout) return false;
    return result.stdout.split('\n').some((line) => line.includes(`--user-data-dir=${profileDir}`));
  } catch {
    return false;
  }
}

async function listProfileDirEntries(profileDir: string): Promise<string[]> {
  try {
    return await fs.promises.readdir(profileDir);
  } catch {
    return [];
  }
}

async function launchChromeOnce(
  url: string,
  profileDir: string,
  chromePath: string,
): Promise<{ chrome: Awaited<ReturnType<typeof launchChromeBase>>; port: number }> {
  const port = await getFreePort();
  const chrome = await launchChromeBase({
    chromePath,
    profileDir,
    port,
    url,
    extraArgs: ['--start-maximized'],
  });

  try {
    await waitForChromeDebugPort(port, 30_000, { includeLastError: true });
    chrome.unref();
    return { chrome, port };
  } catch (error) {
    killChrome(chrome);
    throw error;
  }
}

export async function launchChrome(
  url: string,
  profileDir: string,
  candidates: PlatformCandidates,
  chromePathOverride?: string,
): Promise<{ chrome: Awaited<ReturnType<typeof launchChromeBase>>; port: number }> {
  const chromePath = chromePathOverride?.trim() || findChromeExecutable(candidates);
  if (!chromePath) throw new Error('Chrome not found. Set X_BROWSER_CHROME_PATH env var.');

  try {
    return await launchChromeOnce(url, profileDir, chromePath);
  } catch (error) {
    const entries = await listProfileDirEntries(profileDir);
    const shouldRetry = shouldRetryChromeLaunch({
      lockArtifactsPresent: hasChromeLockArtifacts(entries),
      hasLiveOwner: hasLiveChromeOwner(profileDir),
    });
    if (!shouldRetry) throw error;

    cleanStaleLockFiles(profileDir);
    return await launchChromeOnce(url, profileDir, chromePath);
  }
}

export function getScriptDir(): string {
  return path.dirname(fileURLToPath(import.meta.url));
}

function runBunScript(scriptPath: string, args: string[]): boolean {
  const result = spawnSync('npx', ['-y', 'bun', scriptPath, ...args], { stdio: 'inherit' });
  return result.status === 0;
}

export function copyImageToClipboard(imagePath: string): boolean {
  const copyScript = path.join(getScriptDir(), 'copy-to-clipboard.ts');
  return runBunScript(copyScript, ['image', imagePath]);
}

export function copyHtmlToClipboard(htmlPath: string): boolean {
  const copyScript = path.join(getScriptDir(), 'copy-to-clipboard.ts');
  return runBunScript(copyScript, ['html', '--file', htmlPath]);
}

export function pasteFromClipboard(targetApp?: string, retries = 3, delayMs = 500): boolean {
  const pasteScript = path.join(getScriptDir(), 'paste-from-clipboard.ts');
  const args = ['--retries', String(retries), '--delay', String(delayMs)];
  if (targetApp) args.push('--app', targetApp);
  return runBunScript(pasteScript, args);
}
