import { launch, type LaunchedChrome } from "chrome-launcher";
import WebSocket from "ws";
import type { Logger } from "../utils/logger";
import {
  cleanChromeLockArtifacts,
  ensureChromeProfileDir,
  findChromeProcessUsingProfile,
  findExistingChromeDebugPort,
  hasChromeLockArtifacts,
  listChromeProfileEntries,
  resolveChromeProfileDir,
  shouldRetryChromeLaunchRecovery,
} from "./profile";

interface ChromeVersionResponse {
  webSocketDebuggerUrl: string;
}

export interface ChromeConnectOptions {
  cdpUrl?: string;
  browserPath?: string;
  headless?: boolean;
  logger?: Logger;
  profileDir?: string;
}

export interface ChromeConnection {
  browserWsUrl: string;
  origin?: string;
  port?: number;
  profileDir?: string;
  launched: boolean;
  close(): Promise<void>;
}

async function fetchJson<T>(url: string): Promise<T> {
  const response = await fetch(url);
  if (!response.ok) {
    throw new Error(`Failed to fetch ${url}: HTTP ${response.status}`);
  }
  return (await response.json()) as T;
}

async function connectToHttpEndpoint(origin: string): Promise<ChromeConnection> {
  const normalizedOrigin = origin.replace(/\/$/, "");
  const version = await fetchJson<ChromeVersionResponse>(`${normalizedOrigin}/json/version`);
  return {
    browserWsUrl: version.webSocketDebuggerUrl,
    origin: normalizedOrigin,
    port: Number(new URL(normalizedOrigin).port || 80),
    launched: false,
    async close() {
      // Reused external Chrome, nothing to close here.
    },
  };
}

async function tryReuseChrome(profileDir: string, logger?: Logger): Promise<ChromeConnection | null> {
  const port = await findExistingChromeDebugPort({ profileDir });
  if (!port) {
    return null;
  }

  const origin = `http://127.0.0.1:${port}`;
  try {
    const connection = await connectToHttpEndpoint(origin);
    logger?.info(`Reusing Chrome debugger at ${origin} for profile ${profileDir}`);
    return {
      ...connection,
      profileDir,
    };
  } catch {
    // Debugger disappeared between detection and connect.
  }
  return null;
}

async function launchFreshChrome(
  profileDir: string,
  options: Pick<ChromeConnectOptions, "browserPath" | "headless">,
): Promise<ChromeConnection> {
  let launchedChrome: LaunchedChrome | null = null;
  try {
    launchedChrome = await launch({
      chromePath: options.browserPath,
      userDataDir: profileDir,
      chromeFlags: [
        "--disable-background-networking",
        "--disable-default-apps",
        "--disable-popup-blocking",
        "--disable-sync",
        "--no-first-run",
        "--no-default-browser-check",
        "--remote-allow-origins=*",
        ...(!options.headless ? ["--no-startup-window"] : []),
        ...(options.headless ? ["--headless=new"] : []),
      ],
    });

    const origin = `http://127.0.0.1:${launchedChrome.port}`;
    const version = await fetchJson<ChromeVersionResponse>(`${origin}/json/version`);

    const chrome = launchedChrome;
    return {
      browserWsUrl: version.webSocketDebuggerUrl,
      origin,
      port: launchedChrome.port,
      profileDir,
      launched: true,
      async close() {
        if (!chrome) return;
        await gracefulCloseChrome(chrome, origin);
      },
    };
  } catch (error) {
    launchedChrome?.kill();
    throw error;
  }
}

async function gracefulCloseChrome(chrome: LaunchedChrome, origin: string): Promise<void> {
  try {
    const resp = await fetch(`${origin}/json/version`);
    const { webSocketDebuggerUrl } = (await resp.json()) as ChromeVersionResponse;
    if (webSocketDebuggerUrl) {
      const ws = await new Promise<WebSocket>((resolve, reject) => {
        const socket = new WebSocket(webSocketDebuggerUrl);
        socket.once("open", () => resolve(socket));
        socket.once("error", reject);
      });
      const id = 1;
      ws.send(JSON.stringify({ id, method: "Browser.close" }));
      await new Promise<void>((resolve) => {
        const timer = setTimeout(() => { ws.close(); resolve(); }, 5_000);
        ws.once("close", () => { clearTimeout(timer); resolve(); });
      });
      const exited = await new Promise<boolean>((resolve) => {
        if (chrome.pid && !isProcessAlive(chrome.pid)) { resolve(true); return; }
        const timer = setTimeout(() => resolve(false), 3_000);
        chrome.process.once("exit", () => { clearTimeout(timer); resolve(true); });
      });
      if (exited) return;
    }
  } catch {}
  chrome.kill();
}

function isProcessAlive(pid: number): boolean {
  try { process.kill(pid, 0); return true; } catch { return false; }
}

export async function connectChrome(options: ChromeConnectOptions): Promise<ChromeConnection> {
  if (options.cdpUrl) {
    if (options.cdpUrl.startsWith("ws://") || options.cdpUrl.startsWith("wss://")) {
      return {
        browserWsUrl: options.cdpUrl,
        launched: false,
        async close() {},
      };
    }
    return connectToHttpEndpoint(options.cdpUrl);
  }

  const profileDir = ensureChromeProfileDir(resolveChromeProfileDir(options.profileDir));
  const reused = await tryReuseChrome(profileDir, options.logger);
  if (reused) {
    return reused;
  }

  options.logger?.warn(`No running Chrome debugger found for profile ${profileDir}. Launching Chrome with that profile.`);
  try {
    return await launchFreshChrome(profileDir, options);
  } catch (error) {
    const entries = await listChromeProfileEntries(profileDir);
    const shouldRetry = shouldRetryChromeLaunchRecovery({
      hasLockArtifacts: hasChromeLockArtifacts(entries),
      hasLiveOwner: findChromeProcessUsingProfile(profileDir),
    });
    if (!shouldRetry) {
      throw error;
    }

    options.logger?.warn(`Chrome launch failed with stale profile locks. Cleaning ${profileDir} and retrying once.`);
    cleanChromeLockArtifacts(profileDir);
    return await launchFreshChrome(profileDir, options);
  }
}
