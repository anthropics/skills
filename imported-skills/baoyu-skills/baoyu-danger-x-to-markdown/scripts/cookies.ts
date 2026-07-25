import {
  CdpConnection,
  findChromeExecutable as findChromeExecutableBase,
  findExistingChromeDebugPort,
  gracefulKillChrome,
  getFreePort,
  launchChrome as launchChromeBase,
  openPageSession,
  sleep,
  waitForChromeDebugPort,
  type PlatformCandidates,
} from "baoyu-chrome-cdp";

import process from "node:process";

import { read_cookie_file, write_cookie_file } from "./cookie-file.js";
import { resolveXToMarkdownCookiePath } from "./paths.js";
import { X_COOKIE_NAMES, X_REQUIRED_COOKIES, X_LOGIN_URL, X_USER_DATA_DIR } from "./constants.js";
import type { CookieLike } from "./types.js";

const CHROME_CANDIDATES_FULL: PlatformCandidates = {
  darwin: [
    "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    "/Applications/Google Chrome Canary.app/Contents/MacOS/Google Chrome Canary",
    "/Applications/Google Chrome Beta.app/Contents/MacOS/Google Chrome Beta",
    "/Applications/Chromium.app/Contents/MacOS/Chromium",
    "/Applications/Microsoft Edge.app/Contents/MacOS/Microsoft Edge",
  ],
  win32: [
    "C:\\Program Files\\Google\\Chrome\\Application\\chrome.exe",
    "C:\\Program Files (x86)\\Google\\Chrome\\Application\\chrome.exe",
    "C:\\Program Files\\Microsoft\\Edge\\Application\\msedge.exe",
    "C:\\Program Files (x86)\\Microsoft\\Edge\\Application\\msedge.exe",
  ],
  default: [
    "/usr/bin/google-chrome",
    "/usr/bin/google-chrome-stable",
    "/usr/bin/chromium",
    "/usr/bin/chromium-browser",
    "/snap/bin/chromium",
    "/usr/bin/microsoft-edge",
  ],
};

function findChromeExecutable(): string | null {
  return findChromeExecutableBase({
    candidates: CHROME_CANDIDATES_FULL,
    envNames: ["X_CHROME_PATH"],
  }) ?? null;
}

async function launchChrome(profileDir: string, port: number) {
  const chromePath = findChromeExecutable();
  if (!chromePath) throw new Error("Chrome executable not found.");
  return await launchChromeBase({
    chromePath,
    profileDir,
    port,
    url: X_LOGIN_URL,
    extraArgs: ["--disable-popup-blocking"],
  });
}

async function fetchXCookiesViaCdp(
  profileDir: string,
  timeoutMs: number,
  verbose: boolean,
  log?: (message: string) => void
): Promise<Record<string, string>> {
  const existingPort = await findExistingChromeDebugPort({ profileDir });
  const reusing = existingPort !== null;
  const port = existingPort ?? await getFreePort("X_DEBUG_PORT");
  const chrome = reusing ? null : await launchChrome(profileDir, port);

  let cdp: CdpConnection | null = null;
  let targetId: string | null = null;
  try {
    const wsUrl = await waitForChromeDebugPort(port, 30_000, { includeLastError: true });
    cdp = await CdpConnection.connect(wsUrl, 15_000);

    const page = await openPageSession({
      cdp,
      reusing,
      url: X_LOGIN_URL,
      matchTarget: (target) => target.type === "page" && (
        target.url.includes("x.com") || target.url.includes("twitter.com")
      ),
      enableNetwork: true,
    });
    const { sessionId } = page;
    targetId = page.targetId;

    if (verbose) {
      log?.(reusing
        ? `[x-cookies] Reusing existing Chrome on port ${port}. Waiting for cookies...`
        : "[x-cookies] Chrome opened. If needed, complete X login in the window. Waiting for cookies...");
    }

    const start = Date.now();
    let last: Record<string, string> = {};

    while (Date.now() - start < timeoutMs) {
      const { cookies } = await cdp.send<{ cookies: CookieLike[] }>(
        "Network.getCookies",
        { urls: ["https://x.com/", "https://twitter.com/"] },
        { sessionId, timeoutMs: 10_000 }
      );

      const m = buildXCookieMap((cookies ?? []).filter(Boolean));
      last = m;
      if (hasRequiredXCookies(m)) {
        return m;
      }

      await sleep(1000);
    }

    throw new Error(`Timed out waiting for X cookies. Last keys: ${Object.keys(last).join(", ")}`);
  } finally {
    if (cdp) {
      if (reusing && targetId) {
        try {
          await cdp.send("Target.closeTarget", { targetId }, { timeoutMs: 5_000 });
        } catch {}
      }
      cdp.close();
    }

    if (chrome) await gracefulKillChrome(chrome, port);
  }
}

function resolveCookieDomain(cookie: CookieLike): string | null {
  const rawDomain = cookie.domain?.trim();
  if (rawDomain) {
    return rawDomain.startsWith(".") ? rawDomain.slice(1) : rawDomain;
  }
  const rawUrl = cookie.url?.trim();
  if (rawUrl) {
    try {
      return new URL(rawUrl).hostname;
    } catch {
      return null;
    }
  }
  return null;
}

function pickCookieValue<T extends CookieLike>(cookies: T[], name: string): string | undefined {
  const matches = cookies.filter((cookie) => cookie.name === name && typeof cookie.value === "string");
  if (matches.length === 0) return undefined;

  const preferred = matches.find((cookie) => {
    const domain = resolveCookieDomain(cookie);
    return domain === "x.com" && (cookie.path ?? "/") === "/";
  });
  const xDomain = matches.find((cookie) => (resolveCookieDomain(cookie) ?? "").endsWith("x.com"));
  const twitterDomain = matches.find((cookie) => (resolveCookieDomain(cookie) ?? "").endsWith("twitter.com"));
  return (preferred ?? xDomain ?? twitterDomain ?? matches[0])?.value;
}

function buildXCookieMap<T extends CookieLike>(cookies: T[]): Record<string, string> {
  const cookieMap: Record<string, string> = {};
  for (const name of X_COOKIE_NAMES) {
    const value = pickCookieValue(cookies, name);
    if (value) cookieMap[name] = value;
  }
  return cookieMap;
}

export function hasRequiredXCookies(cookieMap: Record<string, string>): boolean {
  return X_REQUIRED_COOKIES.every((name) => Boolean(cookieMap[name]));
}

function filterXCookieMap(cookieMap: Record<string, string>): Record<string, string> {
  const filtered: Record<string, string> = {};
  for (const name of X_COOKIE_NAMES) {
    const value = cookieMap[name];
    if (value) filtered[name] = value;
  }
  return filtered;
}

function buildInlineCookiesFromEnv(): CookieLike[] {
  const cookies: CookieLike[] = [];
  const authToken = process.env.X_AUTH_TOKEN?.trim();
  const ct0 = process.env.X_CT0?.trim();
  const gt = process.env.X_GUEST_TOKEN?.trim();
  const twid = process.env.X_TWID?.trim();

  if (authToken) {
    cookies.push({ name: "auth_token", value: authToken, domain: "x.com", path: "/" });
  }
  if (ct0) {
    cookies.push({ name: "ct0", value: ct0, domain: "x.com", path: "/" });
  }
  if (gt) {
    cookies.push({ name: "gt", value: gt, domain: "x.com", path: "/" });
  }
  if (twid) {
    cookies.push({ name: "twid", value: twid, domain: "x.com", path: "/" });
  }

  return cookies;
}

async function loadXCookiesFromInline(log?: (message: string) => void): Promise<Record<string, string>> {
  const inline = buildInlineCookiesFromEnv();
  if (inline.length === 0) return {};

  const cookieMap = buildXCookieMap(
    inline.filter((cookie): cookie is CookieLike => Boolean(cookie?.name && typeof cookie.value === "string"))
  );

  if (Object.keys(cookieMap).length > 0) {
    log?.(`[x-cookies] Loaded X cookies from env: ${Object.keys(cookieMap).length} cookie(s).`);
  } else {
    log?.("[x-cookies] Env cookies provided but no X cookies matched.");
  }

  return cookieMap;
}

async function loadXCookiesFromFile(log?: (message: string) => void): Promise<Record<string, string>> {
  const cookiePath = resolveXToMarkdownCookiePath();
  const fileMap = filterXCookieMap((await read_cookie_file(cookiePath)) ?? {});
  if (Object.keys(fileMap).length > 0) {
    log?.(`[x-cookies] Loaded X cookies from file: ${cookiePath} (${Object.keys(fileMap).length} cookie(s))`);
  }
  return fileMap;
}

async function loadXCookiesFromCdp(log?: (message: string) => void): Promise<Record<string, string>> {
  try {
    const cookieMap = await fetchXCookiesViaCdp(X_USER_DATA_DIR, 5 * 60 * 1000, true, log);
    if (!hasRequiredXCookies(cookieMap)) return cookieMap;

    const cookiePath = resolveXToMarkdownCookiePath();
    try {
      await write_cookie_file(cookieMap, cookiePath, "cdp");
      log?.(`[x-cookies] Cookies saved to ${cookiePath}`);
    } catch (error) {
      log?.(
        `[x-cookies] Failed to write cookie file (${cookiePath}): ${
          error instanceof Error ? error.message : String(error ?? "")
        }`
      );
    }
    if (cookieMap.auth_token) log?.(`[x-cookies] auth_token: ${cookieMap.auth_token.slice(0, 20)}...`);
    if (cookieMap.ct0) log?.(`[x-cookies] ct0: ${cookieMap.ct0.slice(0, 20)}...`);
    return cookieMap;
  } catch (error) {
    log?.(
      `[x-cookies] Failed to load cookies via Chrome DevTools Protocol: ${
        error instanceof Error ? error.message : String(error ?? "")
      }`
    );
    return {};
  }
}

export async function loadXCookies(log?: (message: string) => void): Promise<Record<string, string>> {
  const inlineMap = await loadXCookiesFromInline(log);
  const fileMap = await loadXCookiesFromFile(log);
  const combined = { ...fileMap, ...inlineMap };

  if (hasRequiredXCookies(combined)) return combined;

  const cdpMap = await loadXCookiesFromCdp(log);
  return { ...fileMap, ...cdpMap, ...inlineMap };
}

export async function refreshXCookies(log?: (message: string) => void): Promise<Record<string, string>> {
  return loadXCookiesFromCdp(log);
}

export function buildCookieHeader(cookieMap: Record<string, string>): string | undefined {
  const entries = Object.entries(cookieMap).filter(([, value]) => value);
  if (entries.length === 0) return undefined;
  return entries.map(([key, value]) => `${key}=${value}`).join("; ");
}
