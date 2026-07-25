import process from 'node:process';

import {
  CdpConnection,
  discoverRunningChromeDebugPort,
  findChromeExecutable as findChromeExecutableBase,
  findExistingChromeDebugPort,
  gracefulKillChrome,
  getFreePort,
  launchChrome as launchChromeBase,
  openPageSession,
  sleep,
  waitForChromeDebugPort,
  type PlatformCandidates,
} from 'baoyu-chrome-cdp';

import { Endpoint, Headers } from '../constants.js';
import { logger } from './logger.js';
import { cookie_header, fetch_with_timeout } from './http.js';
import { read_cookie_file, type CookieMap, write_cookie_file } from './cookie-file.js';
import { resolveGeminiWebChromeProfileDir, resolveGeminiWebCookiePath } from './paths.js';

const GEMINI_APP_URL = 'https://gemini.google.com/app';

const CHROME_CANDIDATES_FULL: PlatformCandidates = {
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

async function get_free_port(): Promise<number> {
  return await getFreePort('GEMINI_WEB_DEBUG_PORT');
}

function find_chrome_executable(): string | null {
  return findChromeExecutableBase({
    candidates: CHROME_CANDIDATES_FULL,
    envNames: ['GEMINI_WEB_CHROME_PATH'],
  }) ?? null;
}

async function find_existing_chrome_debug_port(profileDir: string): Promise<number | null> {
  return await findExistingChromeDebugPort({ profileDir });
}

async function launch_chrome(profileDir: string, port: number) {
  const chromePath = find_chrome_executable();
  if (!chromePath) throw new Error('Chrome executable not found.');

  return await launchChromeBase({
    chromePath,
    profileDir,
    port,
    url: GEMINI_APP_URL,
    extraArgs: ['--disable-popup-blocking'],
  });
}

async function is_gemini_session_ready(cookies: CookieMap, verbose: boolean): Promise<boolean> {
  if (!cookies['__Secure-1PSID']) return false;

  try {
    const res = await fetch_with_timeout(Endpoint.INIT, {
      method: 'GET',
      headers: { ...Headers.GEMINI, Cookie: cookie_header(cookies) },
      redirect: 'follow',
      timeout_ms: 30_000,
    });

    if (!res.ok) {
      if (verbose) logger.debug(`Gemini init check failed: ${res.status} ${res.statusText}`);
      return false;
    }

    const text = await res.text();
    return /\"SNlM0e\":\"(.*?)\"/.test(text);
  } catch (e) {
    if (verbose) logger.debug(`Gemini init check error: ${e instanceof Error ? e.message : String(e)}`);
    return false;
  }
}

async function fetch_cookies_from_existing_chrome(
  timeoutMs: number,
  verbose: boolean,
): Promise<CookieMap | null> {
  const discovered = await discoverRunningChromeDebugPort();
  if (discovered === null) return null;

  if (verbose) logger.info(`Found reusable Chrome debugging session on port ${discovered.port}. Connecting via WebSocket...`);

  let cdp: CdpConnection | null = null;
  let targetId: string | null = null;
  let createdTarget = false;
  try {
    const connectStart = Date.now();
    const connectTimeout = 30_000;
    let lastConnErr: unknown = null;
    while (Date.now() - connectStart < connectTimeout) {
      try {
        cdp = await CdpConnection.connect(discovered.wsUrl, 5_000);
        break;
      } catch (e) {
        lastConnErr = e;
        if (verbose) logger.debug(`WebSocket connect attempt failed: ${e instanceof Error ? e.message : String(e)}, retrying...`);
        await sleep(1000);
      }
    }
    if (!cdp) {
      if (verbose) logger.debug(`Could not connect to Chrome after ${connectTimeout / 1000}s: ${lastConnErr instanceof Error ? lastConnErr.message : String(lastConnErr)}`);
      return null;
    }

    const page = await openPageSession({
      cdp,
      reusing: false,
      url: GEMINI_APP_URL,
      matchTarget: (target) => target.type === 'page' && target.url.includes('gemini.google.com'),
      enableNetwork: true,
      activateTarget: false,
    });
    const { sessionId } = page;
    targetId = page.targetId;
    createdTarget = page.createdTarget;

    if (verbose) logger.debug(createdTarget ? 'No Gemini tab found, creating new tab...' : 'Found existing Gemini tab, attaching...');

    const start = Date.now();
    let last: CookieMap = {};

    while (Date.now() - start < timeoutMs) {
      const { cookies } = await cdp.send<{ cookies: Array<{ name: string; value: string }> }>(
        'Network.getCookies',
        { urls: ['https://gemini.google.com/', 'https://accounts.google.com/', 'https://www.google.com/'] },
        { sessionId, timeoutMs: 10_000 },
      );

      const cookieMap: CookieMap = {};
      for (const cookie of cookies) {
        if (cookie?.name && typeof cookie.value === 'string') cookieMap[cookie.name] = cookie.value;
      }

      last = cookieMap;
      if (await is_gemini_session_ready(cookieMap, verbose)) return cookieMap;

      await sleep(1000);
    }

    if (verbose) logger.debug(`Existing Chrome did not yield valid cookies. Last keys: ${Object.keys(last).join(', ')}`);
    return null;
  } catch (e) {
    if (verbose) logger.debug(`Failed to connect to existing Chrome debugging session: ${e instanceof Error ? e.message : String(e)}`);
    return null;
  } finally {
    if (cdp) {
      if (createdTarget && targetId) {
        try { await cdp.send('Target.closeTarget', { targetId }, { timeoutMs: 5_000 }); } catch {}
      }
      cdp.close();
    }
  }
}

async function fetch_google_cookies_via_cdp(
  profileDir: string,
  timeoutMs: number,
  verbose: boolean,
): Promise<CookieMap> {
  const existingPort = await find_existing_chrome_debug_port(profileDir);
  const reusing = existingPort !== null;
  const port = existingPort ?? await get_free_port();
  const chrome = reusing ? null : await launch_chrome(profileDir, port);

  let cdp: CdpConnection | null = null;
  let targetId: string | null = null;
  try {
    const wsUrl = await waitForChromeDebugPort(port, 30_000, { includeLastError: true });
    cdp = await CdpConnection.connect(wsUrl, 15_000);

    if (verbose) {
      logger.info(reusing
        ? `Reusing existing Chrome on port ${port}. Waiting for a valid Gemini session...`
        : 'Chrome opened. If needed, complete Google login in the window. Waiting for a valid Gemini session...');
    }

    const page = await openPageSession({
      cdp,
      reusing,
      url: GEMINI_APP_URL,
      matchTarget: (target) => target.type === 'page' && target.url.includes('gemini.google.com'),
      enableNetwork: true,
    });
    const { sessionId } = page;
    targetId = page.targetId;

    const start = Date.now();
    let last: CookieMap = {};

    while (Date.now() - start < timeoutMs) {
      const { cookies } = await cdp.send<{ cookies: Array<{ name: string; value: string }> }>(
        'Network.getCookies',
        { urls: ['https://gemini.google.com/', 'https://accounts.google.com/', 'https://www.google.com/'] },
        { sessionId, timeoutMs: 10_000 },
      );

      const cookieMap: CookieMap = {};
      for (const cookie of cookies) {
        if (cookie?.name && typeof cookie.value === 'string') cookieMap[cookie.name] = cookie.value;
      }

      last = cookieMap;
      if (await is_gemini_session_ready(cookieMap, verbose)) {
        return cookieMap;
      }

      await sleep(1000);
    }

    throw new Error(`Timed out waiting for a valid Gemini session. Last keys: ${Object.keys(last).join(', ')}`);
  } finally {
    if (cdp) {
      if (reusing && targetId) {
        try {
          await cdp.send('Target.closeTarget', { targetId }, { timeoutMs: 5_000 });
        } catch {}
      }
      cdp.close();
    }

    if (chrome) await gracefulKillChrome(chrome, port);
  }
}

export async function load_browser_cookies(domain_name: string = '', verbose: boolean = true): Promise<Record<string, CookieMap>> {
  const force = process.env.GEMINI_WEB_LOGIN?.trim() || process.env.GEMINI_WEB_FORCE_LOGIN?.trim();
  if (!force) {
    const cached = await read_cookie_file();
    if (cached) return { chrome: cached };
  }

  const hasExplicitProfile = !!(process.env.GEMINI_WEB_CHROME_PROFILE_DIR?.trim() || process.env.BAOYU_CHROME_PROFILE_DIR?.trim());
  const existingCookies = hasExplicitProfile ? null : await fetch_cookies_from_existing_chrome(30_000, verbose);
  if (existingCookies) {
    const filtered: CookieMap = {};
    for (const [key, value] of Object.entries(existingCookies)) {
      if (typeof value === 'string' && value.length > 0) filtered[key] = value;
    }

    await write_cookie_file(filtered, resolveGeminiWebCookiePath(), 'cdp-existing');
    void domain_name;
    return { chrome: filtered };
  }

  const profileDir = process.env.GEMINI_WEB_CHROME_PROFILE_DIR?.trim() || resolveGeminiWebChromeProfileDir();
  const cookies = await fetch_google_cookies_via_cdp(profileDir, 120_000, verbose);

  const filtered: CookieMap = {};
  for (const [key, value] of Object.entries(cookies)) {
    if (typeof value === 'string' && value.length > 0) filtered[key] = value;
  }

  await write_cookie_file(filtered, resolveGeminiWebCookiePath(), 'cdp');
  void domain_name;
  return { chrome: filtered };
}

export const loadBrowserCookies = load_browser_cookies;
