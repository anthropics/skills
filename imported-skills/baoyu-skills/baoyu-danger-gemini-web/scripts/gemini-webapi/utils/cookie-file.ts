import fs from 'node:fs';
import path from 'node:path';
import { mkdir, readFile, writeFile } from 'node:fs/promises';

import { resolveGeminiWebCookiePath } from './paths.js';

export type CookieMap = Record<string, string>;

export type CookieFileData =
  | {
      cookies: CookieMap;
      updated_at: number;
      source?: string;
    }
  | {
      version: number;
      updatedAt: string;
      cookieMap: CookieMap;
      source?: string;
    };

export async function read_cookie_file(p: string = resolveGeminiWebCookiePath()): Promise<CookieMap | null> {
  try {
    if (!fs.existsSync(p) || !fs.statSync(p).isFile()) return null;
    const raw = await readFile(p, 'utf8');
    const data = JSON.parse(raw) as unknown;

    if (data && typeof data === 'object' && 'cookies' in (data as any)) {
      const cookies = (data as any).cookies as unknown;
      if (cookies && typeof cookies === 'object') {
        const out: CookieMap = {};
        for (const [k, v] of Object.entries(cookies as Record<string, unknown>)) {
          if (typeof v === 'string') out[k] = v;
        }
        return out;
      }
    }

    if (data && typeof data === 'object' && 'cookieMap' in (data as any)) {
      const cookies = (data as any).cookieMap as unknown;
      if (cookies && typeof cookies === 'object') {
        const out: CookieMap = {};
        for (const [k, v] of Object.entries(cookies as Record<string, unknown>)) {
          if (typeof v === 'string') out[k] = v;
        }
        return Object.keys(out).length > 0 ? out : null;
      }
    }

    if (data && typeof data === 'object') {
      const out: CookieMap = {};
      for (const [k, v] of Object.entries(data as Record<string, unknown>)) {
        if (typeof v === 'string') out[k] = v;
      }
      return Object.keys(out).length > 0 ? out : null;
    }

    return null;
  } catch {
    return null;
  }
}

export async function write_cookie_file(
  cookies: CookieMap,
  p: string = resolveGeminiWebCookiePath(),
  source?: string,
): Promise<void> {
  const dir = path.dirname(p);
  await mkdir(dir, { recursive: true });

  const payload: CookieFileData = {
    version: 1,
    updatedAt: new Date().toISOString(),
    cookieMap: cookies,
    source,
  };
  await writeFile(p, JSON.stringify(payload, null, 2), 'utf8');
}

export const readCookieFile = read_cookie_file;
export const writeCookieFile = write_cookie_file;
