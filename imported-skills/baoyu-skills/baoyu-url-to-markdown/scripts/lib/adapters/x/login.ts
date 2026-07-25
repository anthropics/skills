import type { AdapterContext, AdapterLoginInfo, AdapterProcessResult } from "../types";

interface XLoginSnapshot {
  currentUrl: string;
  hasAccountMenu: boolean;
  hasLoginInputs: boolean;
  bodyText: string;
}

export async function detectXLogin(context: AdapterContext): Promise<AdapterLoginInfo> {
  const snapshot = await context.browser.evaluate<XLoginSnapshot>(`
    (() => {
      const bodyText = (document.body?.innerText ?? "").slice(0, 2500);
      return {
        currentUrl: window.location.href,
        hasAccountMenu: Boolean(
          document.querySelector(
            '[data-testid="SideNav_AccountSwitcher_Button"], [data-testid="AppTabBar_Profile_Link"], [aria-label="Account menu"]'
          )
        ),
        hasLoginInputs: Boolean(
          document.querySelector(
            'input[name="text"], input[name="password"], input[autocomplete="username"], input[autocomplete="current-password"]'
          )
        ),
        bodyText,
      };
    })()
  `).catch(async () => ({
    currentUrl: await context.browser.getURL().catch(() => context.input.url.toString()),
    hasAccountMenu: false,
    hasLoginInputs: false,
    bodyText: "",
  }));

  if (
    /\/i\/flow\/login|\/login/i.test(snapshot.currentUrl) ||
    snapshot.hasLoginInputs ||
    /sign in to x|join x today|登录 x|注册 x|登录到 x/i.test(snapshot.bodyText)
  ) {
    return {
      provider: "x",
      state: "logged_out",
      required: true,
      reason: "X login page detected",
    };
  }

  if (snapshot.hasAccountMenu) {
    return {
      provider: "x",
      state: "logged_in",
    };
  }

  return {
    provider: "x",
    state: "unknown",
  };
}

export function buildNeedsLoginResult(login: AdapterLoginInfo): AdapterProcessResult {
  return {
    status: "needs_interaction",
    login: {
      ...login,
      provider: "x",
      state: login.state === "logged_in" ? "unknown" : login.state,
      required: true,
    },
    interaction: {
      type: "wait_for_interaction",
      kind: "login",
      provider: "x",
      reason: login.reason,
      prompt: "Please sign in to X in the opened Chrome window. Extraction will continue automatically once login is detected.",
      requiresVisibleBrowser: true,
    },
  };
}
