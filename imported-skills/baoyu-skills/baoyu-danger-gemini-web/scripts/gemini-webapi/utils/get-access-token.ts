import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';

import { Endpoint, Headers } from '../constants.js';
import { AuthError } from '../exceptions.js';
import { cookie_header, extract_set_cookie_value, fetch_with_timeout } from './http.js';
import { logger } from './logger.js';
import { read_cookie_file, write_cookie_file } from './cookie-file.js';
import { resolveGeminiWebDataDir, resolveGeminiWebCookiePath } from './paths.js';
import { load_browser_cookies } from './load-browser-cookies.js';

async function send_request(cookies: Record<string, string>, verbose: boolean): Promise<[string, Record<string, string>]> {
  const res = await fetch_with_timeout(Endpoint.INIT, {
    method: 'GET',
    headers: { ...Headers.GEMINI, Cookie: cookie_header(cookies) },
    redirect: 'follow',
    timeout_ms: 30_000,
  });

  if (!res.ok) throw new Error(`Init failed: ${res.status} ${res.statusText}`);
  const text = await res.text();
  const m = text.match(/\"SNlM0e\":\"(.*?)\"/);
  if (!m) throw new Error('Missing SNlM0e in response');
  if (verbose) logger.debug('Init succeeded. Initializing client...');
  return [m[1]!, cookies];
}

function merge_cookie_maps(...maps: Array<Record<string, string> | null | undefined>): Record<string, string> {
  const out: Record<string, string> = {};
  for (const m of maps) {
    if (!m) continue;
    for (const [k, v] of Object.entries(m)) {
      if (typeof v === 'string' && v.length > 0) out[k] = v;
    }
  }
  return out;
}

function read_cached_1psidts_file(dir: string, sid: string): string | null {
  try {
    const p = path.join(dir, `.cached_1psidts_${sid}.txt`);
    if (!fs.existsSync(p) || !fs.statSync(p).isFile()) return null;
    const v = fs.readFileSync(p, 'utf8').trim();
    return v || null;
  } catch {
    return null;
  }
}

function list_cached_1psidts(dir: string): Array<{ sid: string; sidts: string }> {
  const out: Array<{ sid: string; sidts: string }> = [];
  try {
    if (!fs.existsSync(dir) || !fs.statSync(dir).isDirectory()) return out;
    for (const f of fs.readdirSync(dir)) {
      if (!f.startsWith('.cached_1psidts_') || !f.endsWith('.txt')) continue;
      const sid = f.slice('.cached_1psidts_'.length, -'.txt'.length);
      if (!sid) continue;
      const sidts = read_cached_1psidts_file(dir, sid);
      if (sidts) out.push({ sid, sidts });
    }
  } catch {}
  return out;
}

async function fetch_google_extra_cookies(proxy: string | null, verbose: boolean): Promise<Record<string, string>> {
  void proxy;
  try {
    const res = await fetch_with_timeout(Endpoint.GOOGLE, { timeout_ms: 15_000 });
    const setCookie = res.headers.get('set-cookie');
    const nid = extract_set_cookie_value(setCookie, 'NID');
    if (nid) return { NID: nid };
  } catch (e) {
    if (verbose) logger.debug(`Skipping google.com preflight: ${e instanceof Error ? e.message : String(e)}`);
  }
  return {};
}

export async function get_access_token(
  base_cookies: Record<string, string>,
  proxy: string | null = null,
  verbose: boolean = false,
): Promise<[string, Record<string, string>]> {
  const extra = await fetch_google_extra_cookies(proxy, verbose);

  const cacheDir = resolveGeminiWebDataDir();
  const candidates: Record<string, string>[] = [];

  const cookieFilePath = resolveGeminiWebCookiePath();
  const cachedFile = await read_cookie_file(cookieFilePath);
  const forceLogin = !!(process.env.GEMINI_WEB_LOGIN?.trim() || process.env.GEMINI_WEB_FORCE_LOGIN?.trim());
  const shouldUseChromeFirst = forceLogin || (!cachedFile && !base_cookies['__Secure-1PSID'] && !base_cookies['__Secure-1PSIDTS']);

  if (shouldUseChromeFirst) {
    try {
      const browser = await load_browser_cookies('google.com', verbose);
      for (const cookies of Object.values(browser)) {
        candidates.push(merge_cookie_maps(extra, cookies));
      }
    } catch (e) {
      if (verbose) logger.warning(`Failed to load cookies via Chrome CDP: ${e instanceof Error ? e.message : String(e)}`);
    }
  }

  if (base_cookies['__Secure-1PSID'] && base_cookies['__Secure-1PSIDTS']) {
    candidates.push(merge_cookie_maps(extra, base_cookies));
  } else if (verbose) {
    logger.debug('Skipping loading base cookies. Either __Secure-1PSID or __Secure-1PSIDTS is not provided.');
  }

  if (cachedFile) {
    candidates.push(merge_cookie_maps(extra, cachedFile));
  }

  if (base_cookies['__Secure-1PSID'] && !base_cookies['__Secure-1PSIDTS']) {
    const sid = base_cookies['__Secure-1PSID'];
    const sidts = read_cached_1psidts_file(cacheDir, sid);
    if (sidts) {
      candidates.push(merge_cookie_maps(extra, base_cookies, { '__Secure-1PSIDTS': sidts }));
    } else if (verbose) {
      logger.debug('Skipping loading cached cookies. Cache file not found or empty.');
    }
  } else if (!base_cookies['__Secure-1PSID']) {
    const caches = list_cached_1psidts(cacheDir);
    for (const c of caches) {
      candidates.push(merge_cookie_maps(extra, { '__Secure-1PSID': c.sid, '__Secure-1PSIDTS': c.sidts }));
    }
    if (caches.length === 0 && verbose) {
      logger.debug('Skipping loading cached cookies. Cookies will be cached after successful initialization.');
    }
  }

  const unique: Record<string, string>[] = [];
  const seen = new Set<string>();
  for (const c of candidates) {
    const key = `${c['__Secure-1PSID'] ?? ''}:${c['__Secure-1PSIDTS'] ?? ''}:${c.NID ?? ''}`;
    if (seen.has(key)) continue;
    seen.add(key);
    unique.push(c);
  }

  const try_candidates = async (): Promise<[string, Record<string, string>]> => {
    if (unique.length === 0) throw new Error('no candidates');
    const attempts = unique.map(async (c, i) => {
      try {
        if (verbose) logger.debug(`Init attempt (${i + 1}/${unique.length})...`);
        return await send_request(c, verbose);
      } catch (e) {
        if (verbose) logger.debug(`Init attempt (${i + 1}/${unique.length}) failed: ${e instanceof Error ? e.message : String(e)}`);
        throw e;
      }
    });
    return (await Promise.any(attempts)) as [string, Record<string, string>];
  };

  try {
    const [token, cookies] = await try_candidates();
    await write_cookie_file(cookies, resolveGeminiWebCookiePath(), 'init').catch(() => {});
    return [token, cookies];
  } catch {
    if (verbose) logger.debug('Cookie attempts failed. Falling back to Chrome CDP cookie load...');
  }

  const browser = await load_browser_cookies('google.com', verbose);
  let valid = 0;
  for (const cookies of Object.values(browser)) {
    if (cookies['__Secure-1PSID']) valid++;
    if (base_cookies['__Secure-1PSID'] && cookies['__Secure-1PSID'] && cookies['__Secure-1PSID'] !== base_cookies['__Secure-1PSID']) {
      if (verbose) logger.debug('Skipping loaded browser cookies: __Secure-1PSID does not match the one provided.');
      continue;
    }
    unique.push(merge_cookie_maps(extra, cookies));
  }

  if (valid === 0) {
    throw new AuthError(
      'No valid cookies available for initialization. Please pass __Secure-1PSID and __Secure-1PSIDTS manually.',
    );
  }

  try {
    const [token, cookies] = await try_candidates();
    await write_cookie_file(cookies, resolveGeminiWebCookiePath(), 'init').catch(() => {});
    return [token, cookies];
  } catch {
    throw new AuthError(
      `Failed to initialize client. SECURE_1PSIDTS could get expired frequently, please make sure cookie values are up to date. (Failed initialization attempts: ${unique.length})`,
    );
  }
}

export const getAccessToken = get_access_token;
