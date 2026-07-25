import fs from 'node:fs';
import path from 'node:path';
import { mkdir, writeFile } from 'node:fs/promises';

import { Endpoint, Headers } from '../constants.js';
import { AuthError } from '../exceptions.js';
import { cookie_header, extract_set_cookie_value, fetch_with_timeout } from './http.js';
import { resolveGeminiWebDataDir } from './paths.js';

export async function rotate_1psidts(cookies: Record<string, string>, _proxy?: string | null): Promise<string | null> {
  const p = resolveGeminiWebDataDir();
  await mkdir(p, { recursive: true });

  const sid = cookies['__Secure-1PSID'];
  if (!sid) throw new Error('Missing __Secure-1PSID cookie.');

  const cachePath = path.join(p, `.cached_1psidts_${sid}.txt`);

  try {
    const st = fs.statSync(cachePath);
    if (Date.now() - st.mtimeMs <= 60_000) return null;
  } catch {}

  const res = await fetch_with_timeout(Endpoint.ROTATE_COOKIES, {
    method: 'POST',
    headers: { ...Headers.ROTATE_COOKIES, Cookie: cookie_header(cookies) },
    body: '[000,"-0000000000000000000"]',
    redirect: 'follow',
    timeout_ms: 30_000,
  });

  if (res.status === 401) throw new AuthError('Failed to refresh cookies (401).');
  if (!res.ok) throw new Error(`RotateCookies failed: ${res.status} ${res.statusText}`);

  const setCookie = res.headers.get('set-cookie');
  const v = extract_set_cookie_value(setCookie, '__Secure-1PSIDTS');
  if (v) {
    await writeFile(cachePath, v, 'utf8');
    return v;
  }

  return null;
}

export const rotate1psidts = rotate_1psidts;

