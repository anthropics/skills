import type { AdapterContext } from "../types";

const X_SESSION_URLS = ["https://x.com/", "https://twitter.com/"] as const;
const REQUIRED_X_SESSION_COOKIES = ["auth_token", "ct0"] as const;

interface CookieLike {
  name?: string;
  value?: string | null;
}

interface NetworkGetCookiesResult {
  cookies?: CookieLike[];
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
  context: Pick<AdapterContext, "browser">,
): Promise<Record<string, string>> {
  const { cookies } = await context.browser.targetSession.send<NetworkGetCookiesResult>(
    "Network.getCookies",
    { urls: [...X_SESSION_URLS] },
  );
  return buildXSessionCookieMap(cookies ?? []);
}

export async function isXSessionReady(
  context: Pick<AdapterContext, "browser">,
): Promise<boolean> {
  const cookieMap = await readXSessionCookieMap(context);
  return hasRequiredXSessionCookies(cookieMap);
}
