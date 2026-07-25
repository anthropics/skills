import fs from "node:fs";
import path from "node:path";
import os from "node:os";

export type StrictHostKeyChecking = "yes" | "no" | "accept-new";

export interface WechatAccount {
  name: string;
  alias: string;
  default?: boolean;
  default_publish_method?: string;
  default_author?: string;
  need_open_comment?: number;
  only_fans_can_comment?: number;
  app_id?: string;
  app_secret?: string;
  chrome_profile_path?: string;
  remote_publish_host?: string;
  remote_publish_user?: string;
  remote_publish_port?: number;
  remote_publish_identity_file?: string;
  remote_publish_known_hosts_file?: string;
  remote_publish_strict_host_key_checking?: StrictHostKeyChecking;
  remote_publish_connect_timeout?: number;
  remote_publish_proxy_jump?: string;
}

export interface WechatExtendConfig {
  default_theme?: string;
  default_color?: string;
  default_publish_method?: string;
  default_author?: string;
  need_open_comment?: number;
  only_fans_can_comment?: number;
  chrome_profile_path?: string;
  remote_publish_host?: string;
  remote_publish_user?: string;
  remote_publish_port?: number;
  remote_publish_identity_file?: string;
  remote_publish_known_hosts_file?: string;
  remote_publish_strict_host_key_checking?: StrictHostKeyChecking;
  remote_publish_connect_timeout?: number;
  remote_publish_proxy_jump?: string;
  accounts?: WechatAccount[];
}

export interface ResolvedAccount {
  name?: string;
  alias?: string;
  default_publish_method?: string;
  default_author?: string;
  need_open_comment: number;
  only_fans_can_comment: number;
  app_id?: string;
  app_secret?: string;
  chrome_profile_path?: string;
  remote_publish_host?: string;
  remote_publish_user?: string;
  remote_publish_port?: number;
  remote_publish_identity_file?: string;
  remote_publish_known_hosts_file?: string;
  remote_publish_strict_host_key_checking?: StrictHostKeyChecking;
  remote_publish_connect_timeout?: number;
  remote_publish_proxy_jump?: string;
}

function stripQuotes(s: string): string {
  return s.replace(/^['"]|['"]$/g, "");
}

function toBool01(v: string): number {
  return v === "1" || v === "true" ? 1 : 0;
}

function homeDir(): string {
  return process.env.HOME || process.env.USERPROFILE || os.homedir();
}

function parsePort(key: string, v: string): number {
  const n = Number.parseInt(v, 10);
  if (!Number.isFinite(n) || String(n) !== v.trim() || n < 1 || n > 65535) {
    throw new Error(`Invalid ${key}: ${v} (expected integer 1-65535)`);
  }
  return n;
}

function parsePositiveInt(key: string, v: string): number {
  const n = Number.parseInt(v, 10);
  if (!Number.isFinite(n) || String(n) !== v.trim() || n <= 0) {
    throw new Error(`Invalid ${key}: ${v} (expected positive integer)`);
  }
  return n;
}

function parseStrictHostKeyChecking(key: string, v: string): StrictHostKeyChecking {
  const lower = v.toLowerCase();
  if (lower === "yes" || lower === "no" || lower === "accept-new") {
    return lower;
  }
  throw new Error(`Invalid ${key}: ${v} (expected yes|no|accept-new)`);
}

function parseWechatExtend(content: string): WechatExtendConfig {
  const config: WechatExtendConfig = {};
  const lines = content.split("\n");
  let inAccounts = false;
  let current: Record<string, string> | null = null;
  const rawAccounts: Record<string, string>[] = [];

  for (const raw of lines) {
    const trimmed = raw.trim();
    if (!trimmed || trimmed.startsWith("#")) continue;

    if (trimmed === "accounts:") {
      inAccounts = true;
      continue;
    }

    if (inAccounts) {
      const listMatch = raw.match(/^\s+-\s+(.+)$/);
      if (listMatch) {
        if (current) rawAccounts.push(current);
        current = {};
        const kv = listMatch[1]!;
        const ci = kv.indexOf(":");
        if (ci > 0) {
          current[kv.slice(0, ci).trim()] = stripQuotes(kv.slice(ci + 1).trim());
        }
        continue;
      }

      if (current && /^\s{2,}/.test(raw) && !trimmed.startsWith("-")) {
        const ci = trimmed.indexOf(":");
        if (ci > 0) {
          current[trimmed.slice(0, ci).trim()] = stripQuotes(trimmed.slice(ci + 1).trim());
        }
        continue;
      }

      if (!/^\s/.test(raw)) {
        if (current) rawAccounts.push(current);
        current = null;
        inAccounts = false;
      } else {
        continue;
      }
    }

    const ci = trimmed.indexOf(":");
    if (ci < 0) continue;
    const key = trimmed.slice(0, ci).trim();
    const val = stripQuotes(trimmed.slice(ci + 1).trim());
    if (val === "null" || val === "") continue;

    switch (key) {
      case "default_theme": config.default_theme = val; break;
      case "default_color": config.default_color = val; break;
      case "default_publish_method": config.default_publish_method = val; break;
      case "default_author": config.default_author = val; break;
      case "need_open_comment": config.need_open_comment = toBool01(val); break;
      case "only_fans_can_comment": config.only_fans_can_comment = toBool01(val); break;
      case "chrome_profile_path": config.chrome_profile_path = val; break;
      case "remote_publish_host": config.remote_publish_host = val; break;
      case "remote_publish_user": config.remote_publish_user = val; break;
      case "remote_publish_port": config.remote_publish_port = parsePort("remote_publish_port", val); break;
      case "remote_publish_identity_file": config.remote_publish_identity_file = val; break;
      case "remote_publish_known_hosts_file": config.remote_publish_known_hosts_file = val; break;
      case "remote_publish_strict_host_key_checking": config.remote_publish_strict_host_key_checking = parseStrictHostKeyChecking("remote_publish_strict_host_key_checking", val); break;
      case "remote_publish_connect_timeout": config.remote_publish_connect_timeout = parsePositiveInt("remote_publish_connect_timeout", val); break;
      case "remote_publish_proxy_jump": config.remote_publish_proxy_jump = val; break;
    }
  }

  if (current) rawAccounts.push(current);

  if (rawAccounts.length > 0) {
    config.accounts = rawAccounts.map(a => ({
      name: a.name || "",
      alias: a.alias || "",
      default: a.default === "true" || a.default === "1",
      default_publish_method: a.default_publish_method || undefined,
      default_author: a.default_author || undefined,
      need_open_comment: a.need_open_comment ? toBool01(a.need_open_comment) : undefined,
      only_fans_can_comment: a.only_fans_can_comment ? toBool01(a.only_fans_can_comment) : undefined,
      app_id: a.app_id || undefined,
      app_secret: a.app_secret || undefined,
      chrome_profile_path: a.chrome_profile_path || undefined,
      remote_publish_host: a.remote_publish_host || undefined,
      remote_publish_user: a.remote_publish_user || undefined,
      remote_publish_port: a.remote_publish_port ? parsePort("remote_publish_port", a.remote_publish_port) : undefined,
      remote_publish_identity_file: a.remote_publish_identity_file || undefined,
      remote_publish_known_hosts_file: a.remote_publish_known_hosts_file || undefined,
      remote_publish_strict_host_key_checking: a.remote_publish_strict_host_key_checking
        ? parseStrictHostKeyChecking("remote_publish_strict_host_key_checking", a.remote_publish_strict_host_key_checking)
        : undefined,
      remote_publish_connect_timeout: a.remote_publish_connect_timeout
        ? parsePositiveInt("remote_publish_connect_timeout", a.remote_publish_connect_timeout)
        : undefined,
      remote_publish_proxy_jump: a.remote_publish_proxy_jump || undefined,
    }));
  }

  return config;
}

export function loadWechatExtendConfig(): WechatExtendConfig {
  const paths = [
    path.join(process.cwd(), ".baoyu-skills", "baoyu-post-to-wechat", "EXTEND.md"),
    path.join(
      process.env.XDG_CONFIG_HOME || path.join(homeDir(), ".config"),
      "baoyu-skills", "baoyu-post-to-wechat", "EXTEND.md"
    ),
    path.join(homeDir(), ".baoyu-skills", "baoyu-post-to-wechat", "EXTEND.md"),
  ];
  for (const p of paths) {
    let content: string;
    try {
      content = fs.readFileSync(p, "utf-8");
    } catch {
      continue;
    }
    return parseWechatExtend(content);
  }
  return {};
}

function selectAccount(config: WechatExtendConfig, alias?: string): WechatAccount | undefined {
  if (!config.accounts || config.accounts.length === 0) return undefined;
  if (alias) return config.accounts.find(a => a.alias === alias);
  if (config.accounts.length === 1) return config.accounts[0];
  return config.accounts.find(a => a.default);
}

export function resolveAccount(config: WechatExtendConfig, alias?: string): ResolvedAccount {
  const acct = selectAccount(config, alias);
  return {
    name: acct?.name,
    alias: acct?.alias,
    default_publish_method: acct?.default_publish_method ?? config.default_publish_method,
    default_author: acct?.default_author ?? config.default_author,
    need_open_comment: acct?.need_open_comment ?? config.need_open_comment ?? 1,
    only_fans_can_comment: acct?.only_fans_can_comment ?? config.only_fans_can_comment ?? 0,
    app_id: acct?.app_id,
    app_secret: acct?.app_secret,
    chrome_profile_path: acct?.chrome_profile_path ?? config.chrome_profile_path,
    remote_publish_host: acct?.remote_publish_host ?? config.remote_publish_host,
    remote_publish_user: acct?.remote_publish_user ?? config.remote_publish_user,
    remote_publish_port: acct?.remote_publish_port ?? config.remote_publish_port,
    remote_publish_identity_file: acct?.remote_publish_identity_file ?? config.remote_publish_identity_file,
    remote_publish_known_hosts_file: acct?.remote_publish_known_hosts_file ?? config.remote_publish_known_hosts_file,
    remote_publish_strict_host_key_checking:
      acct?.remote_publish_strict_host_key_checking ?? config.remote_publish_strict_host_key_checking,
    remote_publish_connect_timeout: acct?.remote_publish_connect_timeout ?? config.remote_publish_connect_timeout,
    remote_publish_proxy_jump: acct?.remote_publish_proxy_jump ?? config.remote_publish_proxy_jump,
  };
}

function loadEnvFile(envPath: string): Record<string, string> {
  const env: Record<string, string> = {};
  if (!fs.existsSync(envPath)) return env;
  const content = fs.readFileSync(envPath, "utf-8");
  for (const line of content.split("\n")) {
    const trimmed = line.trim();
    if (!trimmed || trimmed.startsWith("#")) continue;
    const eqIdx = trimmed.indexOf("=");
    if (eqIdx > 0) {
      const key = trimmed.slice(0, eqIdx).trim();
      let value = trimmed.slice(eqIdx + 1).trim();
      if ((value.startsWith('"') && value.endsWith('"')) ||
          (value.startsWith("'") && value.endsWith("'"))) {
        value = value.slice(1, -1);
      }
      env[key] = value;
    }
  }
  return env;
}

function aliasToEnvKey(alias: string): string {
  return alias.toUpperCase().replace(/-/g, "_");
}

interface CredentialSource {
  name: string;
  appIdKey: string;
  appSecretKey: string;
  appId?: string;
  appSecret?: string;
}

export interface LoadedCredentials {
  appId: string;
  appSecret: string;
  source: string;
  skippedSources: string[];
}

function normalizeCredentialValue(value?: string): string | undefined {
  const trimmed = value?.trim();
  return trimmed ? trimmed : undefined;
}

function describeMissingKeys(source: CredentialSource): string {
  const missingKeys: string[] = [];
  if (!source.appId) missingKeys.push(source.appIdKey);
  if (!source.appSecret) missingKeys.push(source.appSecretKey);
  return `${source.name} missing ${missingKeys.join(" and ")}`;
}

function buildCredentialSource(
  name: string,
  values: Record<string, string | undefined>,
  appIdKey: string,
  appSecretKey: string,
): CredentialSource {
  return {
    name,
    appIdKey,
    appSecretKey,
    appId: normalizeCredentialValue(values[appIdKey]),
    appSecret: normalizeCredentialValue(values[appSecretKey]),
  };
}

function resolveCredentialSource(
  sources: CredentialSource[],
  account?: ResolvedAccount,
): LoadedCredentials {
  const skippedSources: string[] = [];

  for (const source of sources) {
    if (source.appId && source.appSecret) {
      return {
        appId: source.appId,
        appSecret: source.appSecret,
        source: source.name,
        skippedSources,
      };
    }

    if (source.appId || source.appSecret) {
      skippedSources.push(describeMissingKeys(source));
    }
  }

  const hint = account?.alias ? ` (account: ${account.alias})` : "";
  const partialHint = skippedSources.length > 0
    ? `\nIncomplete credential sources skipped:\n- ${skippedSources.join("\n- ")}`
    : "";

  throw new Error(
    `Missing WECHAT_APP_ID or WECHAT_APP_SECRET${hint}.\n` +
    "Set via EXTEND.md account config, environment variables, or .baoyu-skills/.env file." +
    partialHint
  );
}

export function loadCredentials(account?: ResolvedAccount): LoadedCredentials {
  const cwdEnvPath = path.join(process.cwd(), ".baoyu-skills", ".env");
  const homeEnvPath = path.join(homeDir(), ".baoyu-skills", ".env");
  const cwdEnv = loadEnvFile(cwdEnvPath);
  const homeEnv = loadEnvFile(homeEnvPath);

  const sources: CredentialSource[] = [];

  if (account?.app_id || account?.app_secret) {
    sources.push({
      name: account.alias ? `EXTEND.md account "${account.alias}"` : "EXTEND.md account config",
      appIdKey: "app_id",
      appSecretKey: "app_secret",
      appId: normalizeCredentialValue(account.app_id),
      appSecret: normalizeCredentialValue(account.app_secret),
    });
  }

  const prefix = account?.alias ? `WECHAT_${aliasToEnvKey(account.alias)}_` : "";
  if (prefix) {
    const prefixedKeyLabel = `${prefix}APP_ID/${prefix}APP_SECRET`;
    sources.push(
      buildCredentialSource(`process.env (${prefixedKeyLabel})`, process.env, `${prefix}APP_ID`, `${prefix}APP_SECRET`),
      buildCredentialSource(`<cwd>/.baoyu-skills/.env (${prefixedKeyLabel})`, cwdEnv, `${prefix}APP_ID`, `${prefix}APP_SECRET`),
      buildCredentialSource(`~/.baoyu-skills/.env (${prefixedKeyLabel})`, homeEnv, `${prefix}APP_ID`, `${prefix}APP_SECRET`),
    );
  }

  sources.push(
    buildCredentialSource("process.env", process.env, "WECHAT_APP_ID", "WECHAT_APP_SECRET"),
    buildCredentialSource("<cwd>/.baoyu-skills/.env", cwdEnv, "WECHAT_APP_ID", "WECHAT_APP_SECRET"),
    buildCredentialSource("~/.baoyu-skills/.env", homeEnv, "WECHAT_APP_ID", "WECHAT_APP_SECRET"),
  );

  return resolveCredentialSource(sources, account);
}

export function listAccounts(config: WechatExtendConfig): string[] {
  return (config.accounts || []).map(a => a.alias);
}
