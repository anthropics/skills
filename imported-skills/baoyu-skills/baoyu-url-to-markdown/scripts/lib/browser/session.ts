import { execFile } from "node:child_process";
import { promisify } from "node:util";
import { CdpClient, TargetSession, evaluateRuntime } from "./cdp-client";

interface NavigationResult {
  errorText?: string;
}

const execFileAsync = promisify(execFile);
const MACOS_BROWSER_APP_IDS = [
  "com.google.Chrome",
  "org.chromium.Chromium",
  "com.brave.Browser",
  "com.microsoft.edgemac",
];

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

async function activateBrowserApp(): Promise<void> {
  if (process.platform !== "darwin") {
    return;
  }

  for (const appId of MACOS_BROWSER_APP_IDS) {
    try {
      await execFileAsync("osascript", ["-e", `tell application id "${appId}" to activate`]);
      return;
    } catch {
      // Try the next installed browser bundle id.
    }
  }
}

export class BrowserSession {
  private constructor(
    private readonly cdp: CdpClient,
    public readonly targetSession: TargetSession,
    public readonly interactive: boolean,
  ) {}

  static async open(
    cdp: CdpClient,
    options: {
      initialUrl?: string;
      interactive?: boolean;
    } = {},
  ): Promise<BrowserSession> {
    const targetSession = await cdp.createPageSession({
      initialUrl: options.initialUrl,
      visible: options.interactive,
    });
    const browser = new BrowserSession(cdp, targetSession, Boolean(options.interactive));
    if (browser.interactive) {
      await browser.bringToFront().catch(() => {});
    }
    return browser;
  }

  async goto(url: string, timeoutMs = 30_000): Promise<void> {
    const loadPromise = this.targetSession.waitForEvent("Page.loadEventFired", undefined, timeoutMs).catch(() => null);
    const result = await this.targetSession.send<NavigationResult>("Page.navigate", { url });
    if (result.errorText) {
      throw new Error(`Navigation failed: ${result.errorText}`);
    }
    await loadPromise;
    await this.waitForReadyState(timeoutMs);
  }

  async waitForReadyState(timeoutMs = 30_000): Promise<void> {
    const startedAt = Date.now();
    while (Date.now() - startedAt < timeoutMs) {
      const state = await this.evaluate<string>("document.readyState");
      if (state === "interactive" || state === "complete") {
        return;
      }
      await sleep(150);
    }
    throw new Error("Timed out waiting for document.readyState");
  }

  async evaluate<T>(expression: string): Promise<T> {
    return evaluateRuntime<T>(this.targetSession, expression);
  }

  async getHTML(): Promise<string> {
    return this.evaluate<string>("document.documentElement.outerHTML");
  }

  async getTitle(): Promise<string> {
    return this.evaluate<string>("document.title");
  }

  async getURL(): Promise<string> {
    return this.evaluate<string>("window.location.href");
  }

  async bringToFront(): Promise<void> {
    await this.targetSession.send("Page.bringToFront").catch(async () => {
      await this.cdp.sendBrowserCommand("Target.activateTarget", {
        targetId: this.targetSession.targetId,
      });
    });
    if (this.interactive) {
      await activateBrowserApp().catch(() => {});
    }
  }

  async click(selector: string): Promise<void> {
    const result = await this.evaluate<{ ok: boolean; error?: string }>(`
      (() => {
        const element = document.querySelector(${JSON.stringify(selector)});
        if (!element) {
          return { ok: false, error: "Element not found" };
        }
        element.scrollIntoView({ block: "center", inline: "center" });
        if (element instanceof HTMLElement) {
          element.click();
          return { ok: true };
        }
        return { ok: false, error: "Element is not clickable" };
      })()
    `);

    if (!result.ok) {
      throw new Error(result.error ?? `Failed to click ${selector}`);
    }
  }

  async scrollToEnd(options: { stepPx?: number; delayMs?: number; maxSteps?: number } = {}): Promise<void> {
    const stepPx = options.stepPx ?? 1_400;
    const delayMs = options.delayMs ?? 250;
    const maxSteps = options.maxSteps ?? 6;

    for (let step = 0; step < maxSteps; step += 1) {
      const done = await this.evaluate<boolean>(`
        (() => {
          const before = window.scrollY;
          window.scrollBy(0, ${stepPx});
          const atBottom = window.innerHeight + window.scrollY >= document.body.scrollHeight - 4;
          return atBottom || window.scrollY === before;
        })()
      `);
      if (done) {
        break;
      }
      await sleep(delayMs);
    }
  }

  async close(): Promise<void> {
    await this.cdp.closeTarget(this.targetSession.targetId);
  }
}
