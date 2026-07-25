import { Readability } from "@mozilla/readability";
import { JSDOM } from "jsdom";
import type { ExtractedDocument } from "./document";

function getMetaContent(document: Document, selectors: string[]): string | undefined {
  for (const selector of selectors) {
    const value = document.querySelector(selector)?.getAttribute("content")?.trim();
    if (value) {
      return value;
    }
  }
  return undefined;
}

export function extractDocumentFromHtml(input: {
  url: string;
  html: string;
  adapter?: string;
}): ExtractedDocument {
  const dom = new JSDOM(input.html, { url: input.url });
  const document = dom.window.document;

  const canonicalUrl =
    document.querySelector('link[rel="canonical"]')?.getAttribute("href")?.trim() ??
    getMetaContent(document, ['meta[property="og:url"]']);

  const siteName = getMetaContent(document, [
    'meta[property="og:site_name"]',
    'meta[name="application-name"]',
  ]);

  const metadataAuthor = getMetaContent(document, [
    'meta[name="author"]',
    'meta[property="article:author"]',
    'meta[name="twitter:creator"]',
  ]);

  const publishedAt = getMetaContent(document, [
    'meta[property="article:published_time"]',
    'meta[name="pubdate"]',
    'meta[name="date"]',
    'meta[itemprop="datePublished"]',
  ]);

  const article = new Readability(document).parse();
  const title =
    article?.title?.trim() ||
    getMetaContent(document, ['meta[property="og:title"]']) ||
    document.title.trim() ||
    undefined;

  const summary =
    article?.excerpt?.trim() ||
    getMetaContent(document, [
      'meta[name="description"]',
      'meta[property="og:description"]',
      'meta[name="twitter:description"]',
    ]);

  const contentHtml =
    article?.content?.trim() ||
    document.querySelector("main")?.innerHTML?.trim() ||
    document.body?.innerHTML?.trim() ||
    "";

  const author = article?.byline?.trim() || metadataAuthor;

  return {
    url: input.url,
    canonicalUrl,
    title,
    author,
    siteName,
    publishedAt,
    summary,
    adapter: input.adapter ?? "generic",
    metadata: {
      language: document.documentElement.lang || undefined,
    },
    content: contentHtml ? [{ type: "html", html: contentHtml }] : [],
  };
}

