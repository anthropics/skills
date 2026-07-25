import { execSync } from "node:child_process";
import os from "node:os";
import path from "node:path";
import process from "node:process";

const APP_DATA_DIR = "baoyu-skills";
const X_TO_MARKDOWN_DATA_DIR = "x-to-markdown";
const COOKIE_FILE_NAME = "cookies.json";
const PROFILE_DIR_NAME = "chrome-profile";
const CONSENT_FILE_NAME = "consent.json";

export function resolveUserDataRoot(): string {
  if (process.platform === "win32") {
    return process.env.APPDATA ?? path.join(os.homedir(), "AppData", "Roaming");
  }
  if (process.platform === "darwin") {
    return path.join(os.homedir(), "Library", "Application Support");
  }
  return process.env.XDG_DATA_HOME ?? path.join(os.homedir(), ".local", "share");
}

export function resolveXToMarkdownDataDir(): string {
  const override = process.env.X_DATA_DIR?.trim();
  if (override) return path.resolve(override);
  return path.join(resolveUserDataRoot(), APP_DATA_DIR, X_TO_MARKDOWN_DATA_DIR);
}

export function resolveXToMarkdownCookiePath(): string {
  const override = process.env.X_COOKIE_PATH?.trim();
  if (override) return path.resolve(override);
  return path.join(resolveXToMarkdownDataDir(), COOKIE_FILE_NAME);
}

let _wslHome: string | null | undefined;
function getWslWindowsHome(): string | null {
  if (_wslHome !== undefined) return _wslHome;
  if (!process.env.WSL_DISTRO_NAME) { _wslHome = null; return null; }
  try {
    const raw = execSync('cmd.exe /C "echo %USERPROFILE%"', { encoding: 'utf-8', timeout: 5000 }).trim().replace(/\r/g, '');
    _wslHome = execSync(`wslpath -u "${raw}"`, { encoding: 'utf-8', timeout: 5000 }).trim() || null;
  } catch { _wslHome = null; }
  return _wslHome;
}

export function resolveXToMarkdownChromeProfileDir(): string {
  const override = process.env.BAOYU_CHROME_PROFILE_DIR?.trim() || process.env.X_CHROME_PROFILE_DIR?.trim();
  if (override) return path.resolve(override);
  const wslHome = getWslWindowsHome();
  if (wslHome) return path.join(wslHome, ".local", "share", APP_DATA_DIR, PROFILE_DIR_NAME);
  return path.join(resolveUserDataRoot(), APP_DATA_DIR, PROFILE_DIR_NAME);
}

export function resolveXToMarkdownConsentPath(): string {
  return path.join(resolveXToMarkdownDataDir(), CONSENT_FILE_NAME);
}
