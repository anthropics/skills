import { mkdir, writeFile } from "node:fs/promises";
import { join } from "node:path";
import { createInterface } from "node:readline";
import { connectChrome, type ChromeConnection } from "../browser/chrome-launcher";
import { CdpClient } from "../browser/cdp-client";
import { detectInteractionGate } from "../browser/interaction-gates";
import { NetworkJournal } from "../browser/network-journal";
import { BrowserSession } from "../browser/session";
import { genericAdapter, resolveAdapter } from "../adapters";
import { isXSessionReady } from "../adapters/x/session";
import type { ExtractedDocument } from "../extract/document";
import { renderMarkdown } from "../extract/markdown-renderer";
import { downloadMediaAssets } from "../media/default-downloader";
import { rewriteMarkdownMediaLinks } from "../media/markdown-media";
import { createLogger } from "../utils/logger";
import { normalizeUrl } from "../utils/url";
import type {
  Adapter,
  AdapterContext,
  AdapterLoginInfo,
  LoginState,
  MediaAsset,
  WaitForInteractionRequest,
} from "../adapters/types";

export type WaitMode = "none" | "interaction" | "force";
export type OutputFormat = "markdown" | "json";

export interface ConvertCommandOptions {
  url?: string;
  output?: string;
  format: OutputFormat;
  adapter?: string;
  debugDir?: string;
  cdpUrl?: string;
  browserPath?: string;
  chromeProfileDir?: string;
  headless: boolean;
  downloadMedia: boolean;
  mediaDir?: string;
  waitMode: WaitMode;
  interactionTimeoutMs: number;
  interactionPollIntervalMs: number;
  timeoutMs: number;
}

interface RuntimeResources {
  chrome: ChromeConnection;
  cdp: CdpClient;
  browser: BrowserSession;
  network: NetworkJournal;
  interactive: boolean;
}

interface ForceWaitSnapshot {
  url: string;
  hasGate: boolean;
  loginState: LoginState | "unavailable";
  sessionReady: boolean;
}

interface SuccessfulConvertOutput {
  adapter: string;
  status: "ok";
  login?: AdapterLoginInfo;
  media: MediaAsset[];
  downloads: Awaited<ReturnType<typeof downloadMediaAssets>> | null;
  document: ExtractedDocument;
  markdown: string;
}

interface InteractionRequiredOutput {
  adapter: string;
  status: "needs_interaction";
  login?: AdapterLoginInfo;
  interaction: WaitForInteractionRequest;
}

function sleep(ms: number): Promise<void> {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

function isForceWaitSessionReady(snapshot: ForceWaitSnapshot): boolean {
  return snapshot.sessionReady;
}

export function shouldKeepBrowserOpenAfterInteraction(options: {
  launched: boolean;
  interaction: Pick<WaitForInteractionRequest, "kind" | "provider">;
}): boolean {
  return options.launched && options.interaction.kind === "login" && options.interaction.provider === "x";
}

export function shouldAutoContinueForceWait(
  initial: ForceWaitSnapshot,
  current: ForceWaitSnapshot,
): boolean {
  if (initial.hasGate && !current.hasGate) {
    return true;
  }

  if (initial.loginState === "logged_out" && current.loginState !== "logged_out" && isForceWaitSessionReady(current)) {
    return true;
  }

  if (initial.loginState !== "logged_in" && current.loginState === "logged_in" && isForceWaitSessionReady(current)) {
    return true;
  }

  if (
    current.url !== initial.url &&
    !current.hasGate &&
    current.loginState !== "logged_out" &&
    isForceWaitSessionReady(current)
  ) {
    return true;
  }

  return false;
}

async function writeOutput(path: string, content: string): Promise<void> {
  const directory = path.includes("/") ? path.slice(0, path.lastIndexOf("/")) : "";
  if (directory) {
    await mkdir(directory, { recursive: true });
  }
  await writeFile(path, content, "utf8");
}

async function writeDebugArtifacts(
  debugDir: string,
  document: ExtractedDocument,
  markdown: string,
  browser: BrowserSession,
  network: NetworkJournal,
): Promise<void> {
  await mkdir(debugDir, { recursive: true });

  const html = await browser.getHTML().catch(() => "");
  const networkDump = await network.toJSON({ includeBodies: true });

  await Promise.all([
    writeFile(join(debugDir, "document.json"), JSON.stringify(document, null, 2), "utf8"),
    writeFile(join(debugDir, "markdown.md"), markdown, "utf8"),
    writeFile(join(debugDir, "page.html"), html, "utf8"),
    writeFile(join(debugDir, "network.json"), JSON.stringify(networkDump, null, 2), "utf8"),
  ]);
}

async function openRuntime(
  options: ConvertCommandOptions,
  interactive: boolean,
  debugEnabled: boolean,
): Promise<RuntimeResources> {
  const logger = createLogger(debugEnabled);
  if (interactive) {
    logger.info("Opening Chrome in interactive mode.");
  }
  const chrome = await connectChrome({
    cdpUrl: options.cdpUrl,
    browserPath: options.browserPath,
    profileDir: options.chromeProfileDir,
    headless: interactive ? false : options.headless,
    logger,
  });

  const cdp = await CdpClient.connect(chrome.browserWsUrl);
  const browser = await BrowserSession.open(cdp, { interactive });
  if (interactive) {
    await browser.bringToFront().catch(() => {});
  }
  const network = new NetworkJournal(browser.targetSession, logger);
  await network.start();

  return {
    chrome,
    cdp,
    browser,
    network,
    interactive,
  };
}

async function closeRuntime(runtime: RuntimeResources | null | undefined): Promise<void> {
  if (!runtime) {
    return;
  }
  runtime.network.stop();
  await runtime.browser.close().catch(() => {});
  await runtime.cdp.close().catch(() => {});
  await runtime.chrome.close().catch(() => {});
}

async function isInteractionSessionReady(
  context: AdapterContext,
  interaction: WaitForInteractionRequest,
): Promise<boolean> {
  if (interaction.provider !== "x") {
    return true;
  }
  return await isXSessionReady(context).catch(() => false);
}

async function reopenInteractiveRuntime(
  runtime: RuntimeResources,
  options: ConvertCommandOptions,
  debugEnabled: boolean,
): Promise<RuntimeResources> {
  if (runtime.interactive) {
    return runtime;
  }

  await closeRuntime(runtime);
  return openRuntime(options, true, debugEnabled);
}

async function captureForceWaitSnapshot(
  adapter: Adapter,
  context: AdapterContext,
): Promise<ForceWaitSnapshot> {
  const [gate, url, login] = await Promise.all([
    detectInteractionGate(context.browser).catch(() => null),
    context.browser.getURL().catch(() => context.input.url.toString()),
    adapter.checkLogin?.(context).catch(() => ({
      provider: adapter.name,
      state: "unknown" as const,
    })),
  ]);

  return {
    url,
    hasGate: Boolean(gate),
    loginState: login?.state ?? "unavailable",
    sessionReady: adapter.name === "x" ? await isXSessionReady(context).catch(() => false) : true,
  };
}

async function waitForForceResume(
  adapter: Adapter,
  context: AdapterContext,
  options: ConvertCommandOptions,
): Promise<void> {
  if (context.interactive) {
    await context.browser.bringToFront().catch(() => {});
  }

  const prompt =
    "Chrome is ready. Complete any manual login or verification. Extraction will continue automatically after it detects progress, or press Enter to continue immediately.";
  context.log.info(prompt);

  const rl = createInterface({
    input: process.stdin,
    output: process.stderr,
  });

  let manualContinue = false;
  let closed = false;
  const closeReadline = (): void => {
    if (!closed) {
      closed = true;
      rl.close();
    }
  };

  rl.once("line", () => {
    manualContinue = true;
    closeReadline();
  });

  const initial = await captureForceWaitSnapshot(adapter, context);
  const startedAt = Date.now();

  try {
    while (Date.now() - startedAt < options.interactionTimeoutMs) {
      if (manualContinue) {
        return;
      }

      const current = await captureForceWaitSnapshot(adapter, context);
      if (shouldAutoContinueForceWait(initial, current)) {
        return;
      }

      await sleep(options.interactionPollIntervalMs);
    }
  } finally {
    closeReadline();
  }

  throw new Error("Timed out waiting for force-mode interaction to complete");
}

async function waitForInteraction(
  adapter: Adapter,
  context: AdapterContext,
  interaction: WaitForInteractionRequest,
  options: ConvertCommandOptions,
): Promise<AdapterLoginInfo> {
  const timeoutMs = interaction.timeoutMs ?? options.interactionTimeoutMs;
  const pollIntervalMs = interaction.pollIntervalMs ?? options.interactionPollIntervalMs;
  if (context.interactive) {
    await context.browser.bringToFront().catch(() => {});
  }
  context.log.info(interaction.prompt);

  const startedAt = Date.now();
  let lastLogin: AdapterLoginInfo | null = null;

  while (Date.now() - startedAt < timeoutMs) {
    if (interaction.kind === "login" && adapter.checkLogin) {
      lastLogin = await adapter.checkLogin(context);
      if (lastLogin.state === "logged_in" && await isInteractionSessionReady(context, interaction)) {
        return lastLogin;
      }
    }

    const gate = await detectInteractionGate(context.browser);
    if (!gate) {
      if (interaction.kind !== "login") {
        return lastLogin ?? {
          provider: interaction.provider,
          state: "unknown",
          reason: `${interaction.provider} challenge cleared`,
        };
      }

      if (!adapter.checkLogin) {
        return {
          provider: interaction.provider,
          state: "unknown",
        };
      }

      lastLogin = await adapter.checkLogin(context);
      if (lastLogin.state !== "logged_out" && await isInteractionSessionReady(context, interaction)) {
        return lastLogin;
      }
    }
    await sleep(pollIntervalMs);
  }

  const reason = lastLogin?.reason ? ` (${lastLogin.reason})` : "";
  throw new Error(`Timed out waiting for ${interaction.provider} interaction${reason}`);
}

export function formatOutputContent(
  format: OutputFormat,
  payload: SuccessfulConvertOutput | InteractionRequiredOutput,
): string {
  if (format === "json") {
    return JSON.stringify(payload, null, 2);
  }

  if (payload.status !== "ok") {
    throw new Error("Markdown output is only available for successful extraction results");
  }

  return payload.markdown;
}

function printOutput(content: string): void {
  process.stdout.write(content);
  if (!content.endsWith("\n")) {
    process.stdout.write("\n");
  }
}

export async function runConvertCommand(options: ConvertCommandOptions): Promise<void> {
  if (!options.url) {
    throw new Error("URL is required");
  }
  if (options.downloadMedia && !options.output) {
    throw new Error("--download-media requires --output so media paths can be rewritten relative to the saved output file");
  }

  const url = normalizeUrl(options.url);
  let runtime = await openRuntime(options, options.waitMode !== "none", Boolean(options.debugDir));
  const logger = createLogger(Boolean(options.debugDir));
  let didLogin = false;
  let adapter: Adapter | null = null;
  let context: AdapterContext | null = null;

  try {
    adapter = resolveAdapter({ url }, options.adapter);
    context = {
      input: { url },
      browser: runtime.browser,
      network: runtime.network,
      cdp: runtime.cdp,
      log: logger,
      outputFormat: options.format,
      timeoutMs: options.timeoutMs,
      interactive: runtime.interactive,
      downloadMedia: options.downloadMedia,
    };

    if (adapter.restoreCookies) {
      const restored = await adapter.restoreCookies(context, runtime.chrome.profileDir).catch(() => false);
      if (restored) logger.info(`Restored ${adapter.name} session cookies from sidecar.`);
    }

    if (options.waitMode === "interaction" && adapter.checkLogin) {
      await context.browser.goto(url.toString(), options.timeoutMs).catch(() => {});
      const preLogin = await adapter.checkLogin(context);
      if (preLogin.state !== "logged_in") {
        didLogin = true;
        await waitForInteraction(adapter, context, {
          type: "wait_for_interaction",
          kind: "login",
          provider: preLogin.provider ?? adapter.name,
          prompt: `Please sign in to ${adapter.name === "x" ? "X" : adapter.name} in the opened Chrome window. Extraction will continue automatically once login is detected.`,
          reason: preLogin.reason ?? `Not logged in to ${adapter.name}`,
          requiresVisibleBrowser: true,
        }, options);
      }
    }

    if (options.waitMode === "force") {
      await context.browser.goto(url.toString(), options.timeoutMs).catch(() => {});
      await waitForForceResume(adapter, context, options);
    }

    let result = await adapter.process(context);

    if (result.status === "no_document") {
      const interaction = await detectInteractionGate(context.browser);
      if (interaction) {
        result = {
          status: "needs_interaction",
          interaction,
          login: result.login,
        };
      }
    }

    while (result.status === "needs_interaction") {
      if (options.waitMode === "none") {
        if (options.format === "json") {
          printOutput(
            formatOutputContent(options.format, {
            adapter: adapter.name,
            status: result.status,
            login: result.login,
            interaction: result.interaction,
            }),
          );
          return;
        }

        throw new Error(`${adapter.name} requires manual interaction. Re-run with --wait-for interaction to continue after completing it.`);
      }

      if (result.interaction.requiresVisibleBrowser !== false) {
        runtime = await reopenInteractiveRuntime(runtime, options, Boolean(options.debugDir));
      }

      context = {
        input: { url },
        browser: runtime.browser,
        network: runtime.network,
        cdp: runtime.cdp,
        log: logger,
        outputFormat: options.format,
        timeoutMs: options.timeoutMs,
        interactive: runtime.interactive,
        downloadMedia: options.downloadMedia,
      };

      await context.browser.goto(url.toString(), options.timeoutMs).catch(() => {});
      if (result.interaction.kind === "login") {
        didLogin = true;
      }
      await waitForInteraction(adapter, context, result.interaction, options);
      result = await adapter.process(context);

      if (result.status === "no_document") {
        const interaction = await detectInteractionGate(context.browser);
        if (interaction) {
          result = {
            status: "needs_interaction",
            interaction,
            login: result.login,
          };
        }
      }
    }

    let document: ExtractedDocument | null = result.status === "ok" ? result.document : null;
    let media: MediaAsset[] = result.status === "ok" ? (result.media ?? []) : [];
    let login = result.login;
    let mediaAdapter = adapter;

    if (!document && adapter.name !== genericAdapter.name && result.status === "no_document") {
      logger.info(`Adapter ${adapter.name} returned no structured document; falling back to generic extraction`);
      const fallback = await genericAdapter.process(context);
      if (fallback.status === "ok") {
        document = fallback.document;
        media = fallback.media ?? [];
        mediaAdapter = genericAdapter;
      }
    }

    if (!document) {
      throw new Error("Failed to extract a document from the target URL");
    }

    document.requestedUrl ??= url.toString();

    let markdown = renderMarkdown(document);
    let downloadResult:
      | Awaited<ReturnType<typeof downloadMediaAssets>>
      | null = null;

    if (options.downloadMedia && options.output) {
      downloadResult = mediaAdapter.downloadMedia
        ? await mediaAdapter.downloadMedia({
            media,
            outputPath: options.output,
            mediaDir: options.mediaDir,
            log: logger,
          })
        : await downloadMediaAssets({
            media,
            outputPath: options.output,
            mediaDir: options.mediaDir,
            log: logger,
          });

      markdown = rewriteMarkdownMediaLinks(markdown, downloadResult.replacements);
      if (downloadResult.downloadedImages > 0 || downloadResult.downloadedVideos > 0) {
        logger.info(
          `Downloaded ${downloadResult.downloadedImages} images and ${downloadResult.downloadedVideos} videos`,
        );
      }
    }

    if (options.output) {
      await writeOutput(
        options.output,
        formatOutputContent(options.format, {
          adapter: document.adapter ?? adapter.name,
          status: "ok",
          login,
          media,
          downloads: downloadResult,
          document,
          markdown,
        }),
      );
      logger.info(`Saved ${options.format} to ${options.output}`);
    }

    if (options.debugDir) {
      await writeDebugArtifacts(options.debugDir, document, markdown, runtime.browser, runtime.network);
      logger.info(`Wrote debug artifacts to ${options.debugDir}`);
    }

    if (options.format === "json") {
      printOutput(
        formatOutputContent(options.format, {
        adapter: document.adapter ?? adapter.name,
        status: "ok",
        login,
        media,
        downloads: downloadResult,
        document,
        markdown,
        }),
      );
      return;
    }

    printOutput(markdown);
  } finally {
    if (adapter?.exportCookies && context) {
      await adapter.exportCookies(context, runtime.chrome.profileDir).catch(() => {});
    }
    await closeRuntime(runtime);
  }
}
