import { JSDOM } from "jsdom";
import TurndownService from "turndown";
import { gfm } from "turndown-plugin-gfm";
import type { Adapter } from "../types";
import type { ExtractedDocument } from "../../extract/document";
import { collectMediaFromDocument } from "../../media/markdown-media";

const HN_BASE_URL = "https://news.ycombinator.com";

const turndown = new TurndownService({
  headingStyle: "atx",
  bulletListMarker: "-",
  codeBlockStyle: "fenced",
});

turndown.use(gfm);

export interface HnItem {
  id: number;
  type: "story" | "comment" | "job" | "poll" | "pollopt" | string;
  by?: string;
  time?: number;
  text?: string;
  title?: string;
  url?: string;
  score?: number;
  descendants?: number;
  kids?: number[];
  parent?: number;
  deleted?: boolean;
  dead?: boolean;
}

export interface HnCommentNode {
  item: HnItem;
  children: HnCommentNode[];
}

interface ParsedHnThread {
  story: HnItem;
  comments: HnCommentNode[];
}

function decodeHtmlText(value: string | undefined): string | undefined {
  if (!value) {
    return undefined;
  }

  const dom = new JSDOM(`<!doctype html><html><body>${value}</body></html>`);
  return dom.window.document.body.textContent?.trim() || undefined;
}

function normalizeMarkdown(markdown: string): string {
  return markdown
    .replace(/\r\n/g, "\n")
    .replace(/[ \t]+\n/g, "\n")
    .replace(/\n{3,}/g, "\n\n")
    .trim();
}

function convertHnHtmlToMarkdown(html: string | undefined, baseUrl: string): string {
  if (!html?.trim()) {
    return "";
  }

  const dom = new JSDOM(`<div id="__root">${html}</div>`, { url: baseUrl });
  const root = dom.window.document.querySelector("#__root");
  if (!root) {
    return "";
  }

  root.querySelectorAll("a[href]").forEach((element) => {
    const href = element.getAttribute("href");
    if (!href) {
      return;
    }

    try {
      element.setAttribute("href", new URL(href, baseUrl).toString());
    } catch {
      // Ignore malformed URLs and keep the original href.
    }
  });

  return normalizeMarkdown(turndown.turndown(root.innerHTML));
}

function formatIsoTimestamp(unixSeconds: number | undefined): string | undefined {
  if (!unixSeconds || !Number.isFinite(unixSeconds)) {
    return undefined;
  }

  return new Date(unixSeconds * 1_000).toISOString();
}

function formatDisplayTimestamp(unixSeconds: number | undefined): string {
  const iso = formatIsoTimestamp(unixSeconds);
  if (!iso) {
    return "unknown time";
  }

  return iso.replace("T", " ").replace(".000Z", " UTC");
}

function indentMarkdown(markdown: string, spaces: number): string {
  const prefix = " ".repeat(spaces);
  return markdown
    .split("\n")
    .map((line) => (line ? `${prefix}${line}` : prefix))
    .join("\n");
}

function renderCommentHeader(item: HnItem, pageUrl: string): string {
  const author = item.by ?? "[deleted]";
  const time = item.id
    ? `[${formatDisplayTimestamp(item.time)}](${pageUrl}#${item.id})`
    : formatDisplayTimestamp(item.time);
  return `${author} · ${time}`;
}

function renderCommentNode(node: HnCommentNode, pageUrl: string, depth = 0): string {
  const baseIndent = " ".repeat(depth * 4);
  const lines = [`${baseIndent}- ${renderCommentHeader(node.item, pageUrl)}`];
  const body = convertHnHtmlToMarkdown(node.item.text, pageUrl);

  if (body) {
    lines.push("");
    lines.push(indentMarkdown(body, depth * 4 + 4));
  } else if (node.item.deleted || node.item.dead) {
    lines.push("");
    lines.push(`${baseIndent}    [comment unavailable]`);
  }

  for (const child of node.children) {
    lines.push("");
    lines.push(renderCommentNode(child, pageUrl, depth + 1));
  }

  return lines.join("\n");
}

export function buildHnThreadMarkdown(
  story: HnItem,
  comments: HnCommentNode[],
  pageUrl: string,
): string {
  const lines: string[] = [];
  const storyUrl = story.url ? new URL(story.url, pageUrl).toString() : undefined;
  const storyText = convertHnHtmlToMarkdown(story.text, pageUrl);

  if (storyUrl && storyUrl !== pageUrl) {
    lines.push(`Source: [${storyUrl}](${storyUrl})`);
  }
  lines.push(`HN Item: [${story.id}](${pageUrl})`);

  const submittedBy = story.by ? ` by ${story.by}` : "";
  const submittedAt = formatDisplayTimestamp(story.time);
  lines.push(`Submitted${submittedBy} at ${submittedAt}`);

  const stats: string[] = [];
  if (typeof story.score === "number") {
    stats.push(`${story.score} points`);
  }
  if (typeof story.descendants === "number") {
    stats.push(`${story.descendants} comments`);
  }
  if (stats.length > 0) {
    lines.push(stats.join(" | "));
  }

  if (storyText) {
    lines.push("");
    lines.push("## Post");
    lines.push("");
    lines.push(storyText);
  }

  lines.push("");
  lines.push("## Comments");
  lines.push("");

  if (comments.length === 0) {
    lines.push("No comments.");
  } else {
    lines.push(comments.map((comment) => renderCommentNode(comment, pageUrl)).join("\n\n"));
  }

  return normalizeMarkdown(lines.join("\n"));
}

export function buildHnDocument(
  story: HnItem,
  comments: HnCommentNode[],
  pageUrl: string,
): ExtractedDocument {
  const decodedTitle = decodeHtmlText(story.title) ?? `HN Item ${story.id}`;

  return {
    url: pageUrl,
    canonicalUrl: pageUrl,
    title: decodedTitle,
    author: story.by,
    siteName: "Hacker News",
    publishedAt: formatIsoTimestamp(story.time),
    adapter: "hn",
    metadata: {
      kind: "hn/story",
      storyId: story.id,
      storyUrl: story.url ? new URL(story.url, pageUrl).toString() : undefined,
      points: story.score,
      commentCount: story.descendants,
    },
    content: [
      {
        type: "markdown",
        markdown: buildHnThreadMarkdown(story, comments, pageUrl),
      },
    ],
  };
}

export function parseHnItemId(url: URL): number | null {
  if (url.hostname !== "news.ycombinator.com") {
    return null;
  }

  if (url.pathname !== "/item") {
    return null;
  }

  const value = url.searchParams.get("id");
  if (!value || !/^\d+$/.test(value)) {
    return null;
  }

  return Number(value);
}

function extractUnixSecondsFromAge(element: Element | null): number | undefined {
  const title = element?.getAttribute("title")?.trim();
  if (!title) {
    return undefined;
  }

  const match = title.match(/(\d{9,})$/);
  return match ? Number(match[1]) : undefined;
}

function extractScore(text: string | null | undefined): number | undefined {
  if (!text) {
    return undefined;
  }

  const match = text.match(/(\d+)/);
  return match ? Number(match[1]) : undefined;
}

function extractCommentCount(container: ParentNode): number | undefined {
  const anchors = Array.from(container.querySelectorAll("a"));
  for (const anchor of anchors) {
    const match = anchor.textContent?.trim().match(/(\d+)\s+comments?/i);
    if (match) {
      return Number(match[1]);
    }
  }
  return undefined;
}

function normalizeStoryUrl(storyId: number, href: string | null | undefined, pageUrl: string): string | undefined {
  if (!href) {
    return undefined;
  }

  try {
    const resolved = new URL(href, pageUrl).toString();
    if (resolved === pageUrl || resolved === `${HN_BASE_URL}/item?id=${storyId}`) {
      return undefined;
    }
    return resolved;
  } catch {
    return undefined;
  }
}

export function extractHnThreadFromHtml(html: string, pageUrl: string): ParsedHnThread | null {
  const dom = new JSDOM(html, { url: pageUrl });
  const { document } = dom.window;
  const storyRow = document.querySelector("table.fatitem tr.athing.submission");
  if (!storyRow) {
    return null;
  }

  const storyId = Number(storyRow.getAttribute("id"));
  if (!Number.isFinite(storyId)) {
    return null;
  }

  const titleLink = storyRow.querySelector(".titleline > a");
  const subline = document.querySelector("table.fatitem .subline");
  const topText = document.querySelector("table.fatitem .toptext");

  const story: HnItem = {
    id: storyId,
    type: "story",
    by: subline?.querySelector(".hnuser")?.textContent?.trim() || undefined,
    time: extractUnixSecondsFromAge(subline?.querySelector(".age") ?? null),
    title: titleLink?.innerHTML?.trim() || undefined,
    url: normalizeStoryUrl(storyId, titleLink?.getAttribute("href"), pageUrl),
    text: topText?.innerHTML?.trim() || undefined,
    score: extractScore(subline?.querySelector(".score")?.textContent),
    descendants: extractCommentCount(subline ?? document),
  };

  const roots: HnCommentNode[] = [];
  const stack: HnCommentNode[] = [];

  document.querySelectorAll("tr.athing.comtr").forEach((row) => {
    const commentId = Number(row.getAttribute("id"));
    if (!Number.isFinite(commentId)) {
      return;
    }

    const indentRaw = row.querySelector("td.ind")?.getAttribute("indent");
    const depth = indentRaw && /^\d+$/.test(indentRaw) ? Number(indentRaw) : 0;
    const comhead = row.querySelector(".comhead");
    const item: HnItem = {
      id: commentId,
      type: "comment",
      by: comhead?.querySelector(".hnuser")?.textContent?.trim() || undefined,
      time: extractUnixSecondsFromAge(comhead?.querySelector(".age") ?? null),
      text: row.querySelector(".comment > .commtext")?.innerHTML?.trim() || undefined,
      deleted: row.querySelector(".comment > .commtext") === null,
    };

    const node: HnCommentNode = {
      item,
      children: [],
    };

    while (stack.length > depth) {
      stack.pop();
    }

    const parent = stack[stack.length - 1];
    if (parent) {
      parent.children.push(node);
    } else {
      roots.push(node);
    }

    stack.push(node);
  });

  return {
    story,
    comments: roots,
  };
}

export const hnAdapter: Adapter = {
  name: "hn",
  match(input) {
    return parseHnItemId(input.url) !== null;
  },
  async process(context) {
    const itemId = parseHnItemId(context.input.url);
    if (!itemId) {
      return {
        status: "no_document",
      };
    }

    const pageUrl = context.input.url.toString();
    context.log.info(`Loading ${pageUrl} with hn adapter`);
    await context.browser.goto(pageUrl, context.timeoutMs);
    const html = await context.browser.getHTML();
    const thread = extractHnThreadFromHtml(html, pageUrl);
    if (!thread) {
      return {
        status: "no_document",
      };
    }

    const document = buildHnDocument(thread.story, thread.comments, pageUrl);
    return {
      status: "ok",
      document,
      media: collectMediaFromDocument(document),
    };
  },
};
