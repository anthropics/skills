import { readFile, writeFile, mkdir } from "node:fs/promises";
import { dirname, join } from "node:path";
import { resolveChromeProfileDir } from "./profile";
import type { TargetSession } from "./cdp-client";

export interface CdpCookie {
  name: string;
  value: string;
  domain: string;
  path: string;
  expires: number;
  size: number;
  httpOnly: boolean;
  secure: boolean;
  session: boolean;
  sameSite?: string;
  priority?: string;
  sameParty?: boolean;
  sourceScheme?: string;
  sourcePort?: number;
  partitionKey?: string;
}

interface SidecarData {
  savedAt: string;
  cookies: CdpCookie[];
}

export interface CookieSidecarConfig {
  urls: readonly string[];
  filename: string;
  requiredCookieNames: readonly string[];
  filterCookie?: (cookie: CdpCookie) => boolean;
}

function sidecarPath(filename: string, profileDir?: string): string {
  return join(resolveChromeProfileDir(profileDir), filename);
}

function hasRequired(cookies: CdpCookie[], names: readonly string[]): boolean {
  return names.every((name) =>
    cookies.some((c) => c.name === name && Boolean(c.value)),
  );
}

async function getCookies(session: TargetSession, urls: readonly string[]): Promise<CdpCookie[]> {
  const { cookies } = await session.send<{ cookies: CdpCookie[] }>(
    "Network.getCookies",
    { urls: [...urls] },
  );
  return cookies ?? [];
}

export async function exportCookies(
  session: TargetSession,
  config: CookieSidecarConfig,
  profileDir?: string,
): Promise<boolean> {
  const all = await getCookies(session, config.urls);
  const filtered = config.filterCookie ? all.filter(config.filterCookie) : all;
  if (!hasRequired(filtered, config.requiredCookieNames)) return false;

  const filePath = sidecarPath(config.filename, profileDir);
  await mkdir(dirname(filePath), { recursive: true });
  const data: SidecarData = { savedAt: new Date().toISOString(), cookies: filtered };
  await writeFile(filePath, JSON.stringify(data, null, 2));
  return true;
}

export async function restoreCookies(
  session: TargetSession,
  config: CookieSidecarConfig,
  profileDir?: string,
): Promise<boolean> {
  const live = await getCookies(session, config.urls);
  if (hasRequired(live, config.requiredCookieNames)) return false;

  const filePath = sidecarPath(config.filename, profileDir);
  const raw = await readFile(filePath, "utf8");
  const data = JSON.parse(raw) as SidecarData;
  if (!data.cookies?.length) return false;

  const now = Date.now() / 1000;
  const valid = data.cookies.filter((c) => c.session || !c.expires || c.expires > now);
  if (!hasRequired(valid, config.requiredCookieNames)) return false;

  await session.send("Network.setCookies", {
    cookies: valid.map((c) => ({
      name: c.name,
      value: c.value,
      domain: c.domain,
      path: c.path,
      httpOnly: c.httpOnly,
      secure: c.secure,
      sameSite: c.sameSite,
      expires: c.expires,
    })),
  });
  return true;
}
