export function sleep(ms: number, signal?: AbortSignal): Promise<void> {
  return new Promise((resolve) => {
    const t = setTimeout(() => {
      if (signal) signal.removeEventListener('abort', onAbort);
      resolve();
    }, ms);

    const onAbort = () => {
      clearTimeout(t);
      if (signal) signal.removeEventListener('abort', onAbort);
      resolve();
    };

    if (signal) {
      if (signal.aborted) {
        onAbort();
      } else {
        signal.addEventListener('abort', onAbort, { once: true });
      }
    }
  });
}

export function cookie_header(cookies: Record<string, string>): string {
  return Object.entries(cookies)
    .filter(([, v]) => typeof v === 'string' && v.length > 0)
    .map(([k, v]) => `${k}=${v}`)
    .join('; ');
}

export const cookieHeader = cookie_header;

export function extract_set_cookie_value(setCookie: string | null, name: string): string | null {
  if (!setCookie) return null;
  const re = new RegExp(`(?:^|[;,\\s])${name.replace(/[.*+?^${}()|[\\]\\\\]/g, '\\\\$&')}=([^;]+)`, 'i');
  const m = setCookie.match(re);
  if (!m) return null;
  return m[1] ?? null;
}

export async function fetch_with_timeout(
  url: string,
  init: RequestInit & { timeout_ms?: number } = {},
): Promise<Response> {
  const { timeout_ms, ...rest } = init;
  if (!timeout_ms || timeout_ms <= 0) return fetch(url, rest);

  const ctl = new AbortController();
  const t = setTimeout(() => ctl.abort(), timeout_ms);
  try {
    return await fetch(url, { ...rest, signal: ctl.signal });
  } finally {
    clearTimeout(t);
  }
}

export const fetchWithTimeout = fetch_with_timeout;
