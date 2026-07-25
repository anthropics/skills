import { Readability } from "@mozilla/readability";
import { Defuddle } from "defuddle/node";
import { JSDOM, VirtualConsole } from "jsdom";
import TurndownService from "turndown";
import { gfm } from "turndown-plugin-gfm";
import { collectMediaFromMarkdown } from "../media/markdown-media";
import type { MediaAsset } from "../media/types";
import { cleanHtml } from "./html-cleaner";

export interface HtmlConversionMetadata {
  url: string;
  canonicalUrl?: string;
  siteName?: string;
  title?: string;
  summary?: string;
  author?: string;
  publishedAt?: string;
  coverImage?: string;
  language?: string;
  capturedAt: string;
}

export interface ConvertHtmlToMarkdownOptions {
  enableRemoteMarkdownFallback?: boolean;
  preserveBase64Images?: boolean;
}

export interface HtmlToMarkdownResult {
  metadata: HtmlConversionMetadata;
  markdown: string;
  rawHtml: string;
  cleanedHtml: string;
  media: MediaAsset[];
  conversionMethod: string;
  fallbackReason?: string;
}

type JsonObject = Record<string, unknown>;

const MIN_CONTENT_LENGTH = 120;
const DEFUDDLE_API_ORIGIN = "https://defuddle.md";
const LOCAL_FALLBACK_SCORE_DELTA = 120;
const REMOTE_FALLBACK_SCORE_DELTA = 20;
const LOW_QUALITY_MARKERS = [
  /Join The Conversation/i,
  /One Community\. Many Voices/i,
  /Read our community guidelines/i,
  /Create a free account to share your thoughts/i,
  /Become a Forbes Member/i,
  /Subscribe to trusted journalism/i,
  /\bComments\b/i,
];

const ARTICLE_TYPES = new Set([
  "Article",
  "NewsArticle",
  "BlogPosting",
  "WebPage",
  "ReportageNewsArticle",
]);

const turndown = new TurndownService({
  headingStyle: "atx",
  bulletListMarker: "-",
  codeBlockStyle: "fenced",
}) as TurndownService & {
  remove(selectors: string[]): void;
  addRule(
    key: string,
    rule: {
      filter: string | ((node: Node) => boolean);
      replacement: (content: string) => string;
    },
  ): void;
};

turndown.use(gfm);
turndown.remove(["script", "style", "iframe", "noscript", "template", "svg", "path"]);
turndown.addRule("collapseFigure", {
  filter: "figure",
  replacement(content: string) {
    return `\n\n${content.trim()}\n\n`;
  },
});
turndown.addRule("dropInvisibleAnchors", {
  filter(node: Node) {
    return (
      node.nodeName === "A" &&
      !(node as Element).textContent?.trim() &&
      !(node as Element).querySelector("img, video, picture, source")
    );
  },
  replacement() {
    return "";
  },
});

function pickString(...values: unknown[]): string | undefined {
  for (const value of values) {
    if (typeof value !== "string") {
      continue;
    }
    const trimmed = value.trim();
    if (trimmed) {
      return trimmed;
    }
  }
  return undefined;
}

function normalizeMarkdown(markdown: string): string {
  return markdown
    .replace(/\r\n/g, "\n")
    .replace(/[ \t]+\n/g, "\n")
    .replace(/\n{3,}/g, "\n\n")
    .trim();
}

function stripWrappingQuotes(value: string): string {
  const trimmed = value.trim();
  if (
    (trimmed.startsWith('"') && trimmed.endsWith('"')) ||
    (trimmed.startsWith("'") && trimmed.endsWith("'"))
  ) {
    return trimmed.slice(1, -1).trim();
  }
  return trimmed;
}

function stripMarkdownFrontmatter(markdown: string): string {
  return markdown.replace(/^\uFEFF?---\n[\s\S]*?\n---(?:\n|$)/, "").trim();
}

function cleanMarkdownTitle(value: string): string | undefined {
  const cleaned = stripWrappingQuotes(
    value
      .replace(/\s+#+\s*$/, "")
      .replace(/!\[[^\]]*\]\([^)]+\)/g, "")
      .replace(/\[([^\]]+)\]\([^)]+\)/g, "$1")
      .replace(/[*_`~]/g, "")
      .trim(),
  );

  return cleaned || undefined;
}

export function extractTitleFromMarkdownDocument(markdown: string): string | undefined {
  const normalized = markdown.replace(/\r\n/g, "\n").trim();
  if (!normalized) {
    return undefined;
  }

  const frontmatterMatch = normalized.match(/^\uFEFF?---\n([\s\S]*?)\n---(?:\n|$)/);
  if (frontmatterMatch) {
    for (const line of frontmatterMatch[1].split("\n")) {
      const match = line.match(/^title:\s*(.+?)\s*$/i);
      if (!match) {
        continue;
      }

      const title = cleanMarkdownTitle(match[1]);
      if (title) {
        return title;
      }
    }
  }

  const body = stripMarkdownFrontmatter(normalized);
  const headingMatch = body.match(/^#{1,6}\s+(.+)$/m);
  if (!headingMatch) {
    return undefined;
  }

  return cleanMarkdownTitle(headingMatch[1]);
}

function trimKnownBoilerplate(markdown: string): string {
  const normalized = normalizeMarkdown(markdown);
  const lines = normalized.split("\n");

  while (lines.length > 0) {
    const lastLine = lines[lines.length - 1]?.trim();
    if (!lastLine) {
      lines.pop();
      continue;
    }

    if (/^继续滑动看下一个$/.test(lastLine) || /^轻触阅读原文$/.test(lastLine)) {
      lines.pop();
      continue;
    }

    break;
  }

  return normalizeMarkdown(lines.join("\n"));
}

function buildDefuddleApiUrl(targetUrl: string): string {
  return `${DEFUDDLE_API_ORIGIN}/${encodeURIComponent(targetUrl)}`;
}

async function fetchDefuddleApiMarkdown(
  targetUrl: string,
): Promise<{ markdown: string; title?: string }> {
  const response = await fetch(buildDefuddleApiUrl(targetUrl), {
    headers: {
      accept: "text/markdown,text/plain;q=0.9,*/*;q=0.1",
    },
    redirect: "follow",
  });

  if (!response.ok) {
    throw new Error(`defuddle.md returned ${response.status} ${response.statusText}`);
  }

  const rawMarkdown = (await response.text()).replace(/\r\n/g, "\n").trim();
  if (!rawMarkdown) {
    throw new Error("defuddle.md returned empty markdown");
  }

  const title = extractTitleFromMarkdownDocument(rawMarkdown);
  const markdown = trimKnownBoilerplate(stripMarkdownFrontmatter(rawMarkdown));
  if (!markdown) {
    throw new Error("defuddle.md returned empty markdown");
  }

  return {
    markdown,
    title,
  };
}

function sanitizeHtmlFragment(html: string): string {
  const dom = new JSDOM(`<div id="__root">${html}</div>`);
  const root = dom.window.document.querySelector("#__root");
  if (!root) {
    return html;
  }

  for (const selector of ["script", "style", "iframe", "noscript", "template", "svg", "path"]) {
    root.querySelectorAll(selector).forEach((element) => element.remove());
  }

  return root.innerHTML;
}

function extractTextFromHtml(html: string): string {
  const dom = new JSDOM(`<!doctype html><html><body>${html}</body></html>`);
  const { document } = dom.window;
  for (const selector of ["script", "style", "noscript", "template", "iframe", "svg", "path"]) {
    document.querySelectorAll(selector).forEach((element) => element.remove());
  }
  return document.body?.textContent?.replace(/\s+/g, " ").trim() ?? "";
}

function getMetaContent(document: Document, names: string[]): string | undefined {
  for (const name of names) {
    const element =
      document.querySelector(`meta[name="${name}"]`) ??
      document.querySelector(`meta[property="${name}"]`);
    const content = element?.getAttribute("content")?.trim();
    if (content) {
      return content;
    }
  }
  return undefined;
}

function normalizeLanguageTag(value: string | null | undefined): string | undefined {
  if (!value) {
    return undefined;
  }

  const trimmed = value.trim();
  if (!trimmed) {
    return undefined;
  }

  const primary = trimmed.split(/[,\s;]/, 1)[0]?.trim();
  if (!primary) {
    return undefined;
  }

  return primary.replace(/_/g, "-");
}

function flattenJsonLdItems(data: unknown): JsonObject[] {
  if (!data || typeof data !== "object") {
    return [];
  }

  if (Array.isArray(data)) {
    return data.flatMap(flattenJsonLdItems);
  }

  const item = data as JsonObject;
  if (Array.isArray(item["@graph"])) {
    return (item["@graph"] as unknown[]).flatMap(flattenJsonLdItems);
  }

  return [item];
}

function parseJsonLdScripts(document: Document): JsonObject[] {
  const results: JsonObject[] = [];
  document.querySelectorAll("script[type='application/ld+json']").forEach((script) => {
    try {
      const data = JSON.parse(script.textContent ?? "");
      results.push(...flattenJsonLdItems(data));
    } catch {
      // Ignore malformed json-ld blocks.
    }
  });
  return results;
}

function extractAuthorFromJsonLd(authorData: unknown): string | undefined {
  if (typeof authorData === "string") {
    return authorData.trim() || undefined;
  }

  if (!authorData || typeof authorData !== "object") {
    return undefined;
  }

  if (Array.isArray(authorData)) {
    return authorData
      .map((author) => extractAuthorFromJsonLd(author))
      .filter((value): value is string => Boolean(value))
      .join(", ") || undefined;
  }

  const author = authorData as JsonObject;
  return pickString(author.name);
}

function extractPrimaryJsonLdMeta(document: Document): Partial<HtmlConversionMetadata> {
  for (const item of parseJsonLdScripts(document)) {
    const type = Array.isArray(item["@type"]) ? item["@type"][0] : item["@type"];
    if (typeof type !== "string" || !ARTICLE_TYPES.has(type)) {
      continue;
    }

    return {
      title: pickString(item.headline, item.name),
      summary: pickString(item.description),
      author: extractAuthorFromJsonLd(item.author),
      publishedAt: pickString(item.datePublished, item.dateCreated),
      coverImage: pickString(
        item.image,
        (item.image as JsonObject | undefined)?.url,
        Array.isArray(item.image) ? item.image[0] : undefined,
      ),
    };
  }

  return {};
}

function extractPageMetadata(
  html: string,
  url: string,
  capturedAt: string,
): HtmlConversionMetadata {
  const dom = new JSDOM(html, { url });
  const { document } = dom.window;
  const jsonLd = extractPrimaryJsonLdMeta(document);

  return {
    url,
    canonicalUrl:
      document.querySelector('link[rel="canonical"]')?.getAttribute("href")?.trim() ??
      getMetaContent(document, ["og:url"]),
    siteName: pickString(
      getMetaContent(document, ["og:site_name"]),
      document.querySelector('meta[name="application-name"]')?.getAttribute("content"),
    ),
    title: pickString(
      getMetaContent(document, ["og:title", "twitter:title"]),
      jsonLd.title,
      document.querySelector("h1")?.textContent,
      document.title,
    ),
    summary: pickString(
      getMetaContent(document, ["description", "og:description", "twitter:description"]),
      jsonLd.summary,
    ),
    author: pickString(
      getMetaContent(document, ["author", "article:author", "twitter:creator"]),
      jsonLd.author,
    ),
    publishedAt: pickString(
      document.querySelector("time[datetime]")?.getAttribute("datetime"),
      getMetaContent(document, ["article:published_time", "datePublished", "publishdate", "date"]),
      jsonLd.publishedAt,
    ),
    coverImage: pickString(
      getMetaContent(document, ["og:image", "twitter:image", "twitter:image:src"]),
      jsonLd.coverImage,
    ),
    language: pickString(
      normalizeLanguageTag(document.documentElement.getAttribute("lang")),
      normalizeLanguageTag(
        pickString(
          getMetaContent(document, ["language", "content-language", "og:locale"]),
          document.querySelector("meta[http-equiv='content-language']")?.getAttribute("content"),
        ),
      ),
    ),
    capturedAt,
  };
}

function isMarkdownUsable(markdown: string, html: string): boolean {
  const normalized = normalizeMarkdown(markdown);
  if (!normalized) {
    return false;
  }

  const htmlTextLength = extractTextFromHtml(html).length;
  if (htmlTextLength < MIN_CONTENT_LENGTH) {
    return true;
  }

  if (normalized.length >= 80) {
    return true;
  }

  return normalized.length >= Math.min(200, Math.floor(htmlTextLength * 0.2));
}

function countMarkerHits(markdown: string, markers: RegExp[]): number {
  let hits = 0;
  for (const marker of markers) {
    if (marker.test(markdown)) {
      hits += 1;
    }
  }
  return hits;
}

function countUsefulParagraphs(markdown: string): number {
  const paragraphs = normalizeMarkdown(markdown).split(/\n{2,}/);
  let count = 0;

  for (const paragraph of paragraphs) {
    const trimmed = paragraph.trim();
    if (!trimmed) {
      continue;
    }
    if (/^!?\[[^\]]*\]\([^)]+\)$/.test(trimmed)) {
      continue;
    }
    if (/^#{1,6}\s+/.test(trimmed)) {
      continue;
    }
    if ((trimmed.match(/\b[\p{L}\p{N}']+\b/gu) || []).length < 8) {
      continue;
    }
    count += 1;
  }

  return count;
}

function scoreMarkdownQuality(markdown: string): number {
  const normalized = normalizeMarkdown(markdown);
  const wordCount = (normalized.match(/\b[\p{L}\p{N}']+\b/gu) || []).length;
  const usefulParagraphs = countUsefulParagraphs(normalized);
  const headingCount = (normalized.match(/^#{1,6}\s+/gm) || []).length;
  const markerHits = countMarkerHits(normalized, LOW_QUALITY_MARKERS);
  return Math.min(wordCount, 4000) + usefulParagraphs * 40 + headingCount * 10 - markerHits * 180;
}

function shouldCompareWithFallback(markdown: string): boolean {
  const normalized = normalizeMarkdown(markdown);
  return countMarkerHits(normalized, LOW_QUALITY_MARKERS) > 0 || countUsefulParagraphs(normalized) < 6;
}

function hasMeaningfulMarkdownStructure(markdown: string): boolean {
  const normalized = normalizeMarkdown(markdown);
  if (!normalized) {
    return false;
  }

  return (
    countUsefulParagraphs(normalized) > 0 ||
    /^#{1,6}\s+/m.test(normalized) ||
    /^[-*]\s+/m.test(normalized) ||
    /^\d+\.\s+/m.test(normalized) ||
    /!\[[^\]]*\]\([^)]+\)/.test(normalized)
  );
}

function shouldTryRemoteMarkdownFallback(
  markdown: string,
  html: string,
  options: ConvertHtmlToMarkdownOptions,
): boolean {
  if (!options.enableRemoteMarkdownFallback) {
    return false;
  }

  return !isMarkdownUsable(markdown, html) || shouldCompareWithFallback(markdown);
}

function shouldPreferRemoteMarkdown(
  current: HtmlToMarkdownResult,
  remote: HtmlToMarkdownResult,
  html: string,
): boolean {
  if (!isMarkdownUsable(current.markdown, html)) {
    return true;
  }

  if (!hasMeaningfulMarkdownStructure(current.markdown) && hasMeaningfulMarkdownStructure(remote.markdown)) {
    return true;
  }

  return scoreMarkdownQuality(remote.markdown) > scoreMarkdownQuality(current.markdown) + REMOTE_FALLBACK_SCORE_DELTA;
}

function buildRemoteFallbackReason(current: HtmlToMarkdownResult, html: string): string {
  if (!isMarkdownUsable(current.markdown, html)) {
    return current.fallbackReason
      ? `Used defuddle.md markdown fallback after local extraction failed: ${current.fallbackReason}`
      : "Used defuddle.md markdown fallback after local extraction returned empty or incomplete markdown";
  }

  return "defuddle.md produced higher-quality markdown than local extraction";
}

async function tryDefuddleConversion(
  html: string,
  url: string,
  baseMetadata: HtmlConversionMetadata,
): Promise<{ ok: true; result: HtmlToMarkdownResult } | { ok: false; reason: string }> {
  try {
    const virtualConsole = new VirtualConsole();
    virtualConsole.on("jsdomError", (error: Error & { type?: string }) => {
      if (error.type === "css parsing" || /Could not parse CSS stylesheet/i.test(error.message)) {
        return;
      }
    });

    const dom = new JSDOM(html, { url, virtualConsole });
    const result = await Defuddle(dom, url, { markdown: true });
    const markdown = trimKnownBoilerplate(result.content || "");

    if (!isMarkdownUsable(markdown, html)) {
      return { ok: false, reason: "Defuddle returned empty or incomplete markdown" };
    }

    const metadata: HtmlConversionMetadata = {
      ...baseMetadata,
      title: pickString(result.title, baseMetadata.title),
      summary: pickString(result.description, baseMetadata.summary),
      author: pickString(result.author, baseMetadata.author),
      publishedAt: pickString(result.published, baseMetadata.publishedAt),
      coverImage: pickString(result.image, baseMetadata.coverImage),
      language: pickString(result.language, baseMetadata.language),
    };

    return {
      ok: true,
      result: {
        metadata,
        markdown,
        rawHtml: html,
        cleanedHtml: html,
        media: collectMediaFromMarkdown(markdown).concat(
          metadata.coverImage
            ? [{ url: metadata.coverImage, kind: "image", role: "cover" as const }]
            : [],
        ),
        conversionMethod: "defuddle",
      },
    };
  } catch (error) {
    return {
      ok: false,
      reason: error instanceof Error ? error.message : String(error),
    };
  }
}

async function tryDefuddleApiConversion(
  html: string,
  url: string,
  baseMetadata: HtmlConversionMetadata,
): Promise<{ ok: true; result: HtmlToMarkdownResult } | { ok: false; reason: string }> {
  try {
    const result = await fetchDefuddleApiMarkdown(url);
    const markdown = result.markdown;

    if (!isMarkdownUsable(markdown, html) && scoreMarkdownQuality(markdown) < 80) {
      return { ok: false, reason: "defuddle.md returned empty or incomplete markdown" };
    }

    const metadata: HtmlConversionMetadata = {
      ...baseMetadata,
      title: pickString(result.title, baseMetadata.title),
    };

    return {
      ok: true,
      result: {
        metadata,
        markdown,
        rawHtml: html,
        cleanedHtml: html,
        media: collectMediaFromMarkdown(markdown).concat(
          metadata.coverImage
            ? [{ url: metadata.coverImage, kind: "image", role: "cover" as const }]
            : [],
        ),
        conversionMethod: "defuddle-api",
      },
    };
  } catch (error) {
    return {
      ok: false,
      reason: error instanceof Error ? error.message : String(error),
    };
  }
}

function convertHtmlFragmentToMarkdown(html: string): string {
  if (!html.trim()) {
    return "";
  }

  try {
    return turndown.turndown(sanitizeHtmlFragment(html));
  } catch {
    return "";
  }
}

function fallbackPlainText(html: string): string {
  return trimKnownBoilerplate(extractTextFromHtml(html));
}

function convertWithReadability(
  rawHtml: string,
  cleanedHtml: string,
  url: string,
  baseMetadata: HtmlConversionMetadata,
): HtmlToMarkdownResult {
  const dom = new JSDOM(cleanedHtml, { url });
  const document = dom.window.document;
  const article = new Readability(document).parse();

  const contentHtml =
    article?.content?.trim() ??
    document.querySelector("main")?.innerHTML?.trim() ??
    document.body?.innerHTML?.trim() ??
    "";

  let markdown = contentHtml ? convertHtmlFragmentToMarkdown(contentHtml) : "";
  if (!markdown) {
    markdown = fallbackPlainText(cleanedHtml);
  }

  const metadata: HtmlConversionMetadata = {
    ...baseMetadata,
    title: pickString(article?.title, baseMetadata.title),
    summary: pickString(article?.excerpt, baseMetadata.summary),
    author: pickString(article?.byline, baseMetadata.author),
  };

  const media = collectMediaFromMarkdown(markdown);
  if (metadata.coverImage) {
    media.unshift({
      url: metadata.coverImage,
      kind: "image",
      role: "cover",
    });
  }

  return {
    metadata,
    markdown: trimKnownBoilerplate(markdown),
    rawHtml,
    cleanedHtml,
    media,
    conversionMethod: article?.content ? "legacy:readability" : "legacy:body",
  };
}

export async function convertHtmlToMarkdown(
  html: string,
  url: string,
  options: ConvertHtmlToMarkdownOptions = {},
): Promise<HtmlToMarkdownResult> {
  const capturedAt = new Date().toISOString();
  const baseMetadata = extractPageMetadata(html, url, capturedAt);

  let cleanedHtml = html;
  try {
    cleanedHtml = cleanHtml(html, url, {
      removeBase64Images: !options.preserveBase64Images,
    });
  } catch {
    cleanedHtml = html;
  }

  let selectedResult: HtmlToMarkdownResult;
  const defuddleResult = await tryDefuddleConversion(cleanedHtml, url, baseMetadata);
  if (defuddleResult.ok) {
    if (shouldCompareWithFallback(defuddleResult.result.markdown)) {
      const fallbackResult = convertWithReadability(html, cleanedHtml, url, baseMetadata);
      if (
        scoreMarkdownQuality(fallbackResult.markdown) >
        scoreMarkdownQuality(defuddleResult.result.markdown) + LOCAL_FALLBACK_SCORE_DELTA
      ) {
        selectedResult = {
          ...fallbackResult,
          fallbackReason: "Readability/Turndown produced higher-quality markdown than Defuddle",
        };
      } else {
        selectedResult = {
          ...defuddleResult.result,
          rawHtml: html,
          cleanedHtml,
        };
      }
    } else {
      selectedResult = {
        ...defuddleResult.result,
        rawHtml: html,
        cleanedHtml,
      };
    }
  } else {
    selectedResult = {
      ...convertWithReadability(html, cleanedHtml, url, baseMetadata),
      fallbackReason: defuddleResult.reason,
    };
  }

  if (!shouldTryRemoteMarkdownFallback(selectedResult.markdown, cleanedHtml, options)) {
    return selectedResult;
  }

  const remoteDefuddleResult = await tryDefuddleApiConversion(cleanedHtml, url, baseMetadata);
  if (!remoteDefuddleResult.ok || !shouldPreferRemoteMarkdown(selectedResult, remoteDefuddleResult.result, cleanedHtml)) {
    return selectedResult;
  }

  return {
    ...remoteDefuddleResult.result,
    rawHtml: html,
    cleanedHtml,
    fallbackReason: buildRemoteFallbackReason(selectedResult, cleanedHtml),
  };
}
