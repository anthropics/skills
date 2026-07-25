import type { Adapter, AdapterLoginInfo } from "../types";
import { exportCookies, restoreCookies, type CookieSidecarConfig } from "../../browser/cookie-sidecar";
import { detectInteractionGate } from "../../browser/interaction-gates";
import type { ExtractedDocument } from "../../extract/document";
import { collectMediaFromDocument } from "../../media/markdown-media";
import { extractArticleDocumentFromPayload } from "./article";
import { buildNeedsLoginResult, detectXLogin } from "./login";
import { extractStatusId, isXHost } from "./match";
import { collectXJsonPayloads, waitForInitialXPayload } from "./payloads";
import { extractSingleTweetDocumentFromPayload } from "./single";
import { extractThreadDocumentFromPayloads } from "./thread";
import { loadFullXThread } from "./thread-loader";

const cookieConfig: CookieSidecarConfig = {
  urls: ["https://x.com/", "https://twitter.com/"],
  filename: "x-session-cookies.json",
  requiredCookieNames: ["auth_token", "ct0"],
  filterCookie: (c) => {
    const d = c.domain ?? "";
    return d.endsWith("x.com") || d.endsWith("twitter.com");
  },
};

function extractDocumentFromPayloads(
  payloads: unknown[],
  statusId: string,
  pageUrl: string,
): ExtractedDocument | null {
  for (const payload of payloads) {
    const articleDocument = extractArticleDocumentFromPayload(payload, statusId, pageUrl, payloads);
    if (articleDocument) {
      return articleDocument;
    }
  }

  const threadDocument = extractThreadDocumentFromPayloads(payloads, statusId, pageUrl);
  if (threadDocument) {
    return threadDocument;
  }

  for (const payload of payloads) {
    const singleDocument = extractSingleTweetDocumentFromPayload(payload, statusId, pageUrl);
    if (singleDocument) {
      return singleDocument;
    }
  }

  return null;
}

async function ensureXLoginState(context: Parameters<Adapter["process"]>[0]): Promise<AdapterLoginInfo> {
  return detectXLogin(context);
}

export const xAdapter: Adapter = {
  name: "x",
  match(input) {
    return isXHost(input.url.hostname);
  },
  async checkLogin(context) {
    return detectXLogin(context);
  },
  async exportCookies(context, profileDir) {
    return exportCookies(context.browser.targetSession, cookieConfig, profileDir);
  },
  async restoreCookies(context, profileDir) {
    return restoreCookies(context.browser.targetSession, cookieConfig, profileDir);
  },
  async process(context) {
    const statusId = extractStatusId(context.input.url);
    if (!statusId) {
      return {
        status: "no_document",
      };
    }

    context.log.info(`Loading ${context.input.url.toString()} with x adapter`);
    await context.browser.goto(context.input.url.toString(), context.timeoutMs);

    const interaction = await detectInteractionGate(context.browser);
    if (interaction) {
      return {
        status: "needs_interaction",
        interaction,
      };
    }

    let login = await ensureXLoginState(context);
    if (login.state === "logged_out") {
      return buildNeedsLoginResult(login);
    }

    await waitForInitialXPayload(context);
    await loadFullXThread(context, statusId);

    const pageUrl = await context.browser.getURL();
    const postLoadInteraction = await detectInteractionGate(context.browser);
    if (postLoadInteraction) {
      return {
        status: "needs_interaction",
        interaction: postLoadInteraction,
        login,
      };
    }

    login = await ensureXLoginState(context).catch(() => login);
    if (login.state === "logged_out") {
      return buildNeedsLoginResult(login);
    }

    const payloads = await collectXJsonPayloads(context);
    if (payloads.length === 0) {
      return {
        status: "no_document",
        login,
      };
    }

    const document = extractDocumentFromPayloads(payloads, statusId, pageUrl);
    if (document) {
      return {
        status: "ok",
        document,
        media: collectMediaFromDocument(document),
        login,
      };
    }

    return {
      status: "no_document",
      login,
    };
  },
};
