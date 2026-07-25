import { buildCookieHeader } from "./cookies.js";

let cachedHomeHtml: { userAgent: string; html: string } | null = null;

export async function fetchText(url: string, init?: RequestInit): Promise<string> {
  const response = await fetch(url, init);
  const text = await response.text();
  if (!response.ok) {
    throw new Error(`Request failed (${response.status}) for ${url}: ${text.slice(0, 200)}`);
  }
  return text;
}

export async function fetchHomeHtml(userAgent: string): Promise<string> {
  if (cachedHomeHtml?.userAgent === userAgent) {
    return cachedHomeHtml.html;
  }
  const html = await fetchText("https://x.com", {
    headers: {
      "user-agent": userAgent,
    },
  });
  cachedHomeHtml = { userAgent, html };
  return html;
}

export function parseStringList(raw: string | undefined): string[] {
  if (!raw) return [];
  return raw
    .split(",")
    .map((item) => item.trim())
    .filter(Boolean)
    .map((item) => item.replace(/^\"|\"$/g, ""));
}

export function resolveFeatureValue(html: string, key: string): boolean | undefined {
  const keyPattern = key.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const unescaped = new RegExp(`"${keyPattern}"\\s*:\\s*\\{"value"\\s*:\\s*(true|false)`);
  const escaped = new RegExp(`\\\\"${keyPattern}\\\\"\\s*:\\s*\\\\{\\\\"value\\\\"\\s*:\\s*(true|false)`);
  const match = html.match(unescaped) ?? html.match(escaped);
  if (!match) return undefined;
  return match[1] === "true";
}

export function buildFeatureMap(
  html: string,
  keys: string[],
  defaults?: Record<string, boolean>
): Record<string, boolean> {
  const features: Record<string, boolean> = {};
  for (const key of keys) {
    const value = resolveFeatureValue(html, key);
    if (value !== undefined) {
      features[key] = value;
    } else if (defaults && Object.prototype.hasOwnProperty.call(defaults, key)) {
      features[key] = defaults[key] ?? true;
    } else {
      features[key] = true;
    }
  }
  if (!Object.prototype.hasOwnProperty.call(features, "responsive_web_graphql_exclude_directive_enabled")) {
    features.responsive_web_graphql_exclude_directive_enabled = true;
  }
  return features;
}

export function buildFieldToggleMap(keys: string[]): Record<string, boolean> {
  const toggles: Record<string, boolean> = {};
  for (const key of keys) {
    toggles[key] = true;
  }
  return toggles;
}

export function buildTweetFieldToggleMap(keys: string[]): Record<string, boolean> {
  const toggles: Record<string, boolean> = {};
  for (const key of keys) {
    if (key === "withGrokAnalyze" || key === "withDisallowedReplyControls") {
      toggles[key] = false;
    } else {
      toggles[key] = true;
    }
  }
  return toggles;
}

export function buildRequestHeaders(
  cookieMap: Record<string, string>,
  userAgent: string,
  bearerToken: string
): Record<string, string> {
  const headers: Record<string, string> = {
    authorization: bearerToken,
    "user-agent": userAgent,
    accept: "application/json",
    "x-twitter-active-user": "yes",
    "x-twitter-client-language": "en",
    "accept-language": "en",
  };

  if (cookieMap.auth_token) {
    headers["x-twitter-auth-type"] = "OAuth2Session";
  }

  const cookieHeader = buildCookieHeader(cookieMap);
  if (cookieHeader) {
    headers.cookie = cookieHeader;
  }
  if (cookieMap.ct0) {
    headers["x-csrf-token"] = cookieMap.ct0;
  }
  if (process.env.X_CLIENT_TRANSACTION_ID?.trim()) {
    headers["x-client-transaction-id"] = process.env.X_CLIENT_TRANSACTION_ID.trim();
  }

  return headers;
}
