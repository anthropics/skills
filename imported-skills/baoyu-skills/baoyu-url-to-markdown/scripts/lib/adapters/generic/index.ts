import type { Adapter } from "../types";
import { detectInteractionGate } from "../../browser/interaction-gates";
import { captureNormalizedPageSnapshot } from "../../browser/page-snapshot";
import { convertHtmlToMarkdown } from "../../extract/html-to-markdown";

export const genericAdapter: Adapter = {
  name: "generic",
  match() {
    return true;
  },
  async process(context) {
    context.log.info(`Loading ${context.input.url.toString()} with generic adapter`);
    await context.browser.goto(context.input.url.toString(), context.timeoutMs);

    try {
      await context.network.waitForIdle({
        idleMs: 1_200,
        timeoutMs: Math.min(context.timeoutMs, 15_000),
      });
    } catch {
      context.log.debug("Network idle timed out on initial load; continuing.");
    }

    await context.browser.scrollToEnd({ maxSteps: 4, delayMs: 300 });

    try {
      await context.network.waitForIdle({
        idleMs: 900,
        timeoutMs: Math.min(context.timeoutMs, 10_000),
      });
    } catch {
      context.log.debug("Network idle timed out after scrolling; continuing.");
    }

    const interaction = await detectInteractionGate(context.browser);
    if (interaction) {
      return {
        status: "needs_interaction",
        interaction,
      };
    }

    const snapshot = await captureNormalizedPageSnapshot(context.browser);
    const converted = await convertHtmlToMarkdown(snapshot.html, snapshot.finalUrl, {
      enableRemoteMarkdownFallback: context.outputFormat === "markdown",
      preserveBase64Images: context.downloadMedia,
    });
    const document = {
      url: snapshot.finalUrl,
      canonicalUrl: converted.metadata.canonicalUrl,
      title: converted.metadata.title,
      author: converted.metadata.author,
      siteName: converted.metadata.siteName,
      publishedAt: converted.metadata.publishedAt,
      summary: converted.metadata.summary,
      adapter: "generic",
      metadata: {
        coverImage: converted.metadata.coverImage,
        language: converted.metadata.language,
        capturedAt: converted.metadata.capturedAt,
        conversionMethod: converted.conversionMethod,
        fallbackReason: converted.fallbackReason,
        kind: "generic/article",
      },
      content: converted.markdown ? [{ type: "markdown" as const, markdown: converted.markdown }] : [],
    };

    return {
      status: "ok",
      document,
      media: converted.media,
    };
  },
};
