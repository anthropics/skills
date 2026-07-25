import TurndownService from "turndown";
import { gfm } from "turndown-plugin-gfm";
import { normalizeMarkdownMediaLinks } from "../media/markdown-media";
import type { ContentBlock, ExtractedDocument } from "./document";

const turndownService = new TurndownService({
  codeBlockStyle: "fenced",
  headingStyle: "atx",
  bulletListMarker: "-",
});

turndownService.use(gfm);

function renderBlock(block: ContentBlock): string {
  switch (block.type) {
    case "paragraph":
      return block.text.trim();
    case "heading":
      return `${"#".repeat(Math.min(Math.max(block.depth, 1), 6))} ${block.text.trim()}`;
    case "list":
      return block.items
        .map((item, index) => (block.ordered ? `${index + 1}. ${item.trim()}` : `- ${item.trim()}`))
        .join("\n");
    case "quote":
      return block.text
        .split("\n")
        .map((line) => `> ${line}`)
        .join("\n");
    case "code":
      return `\`\`\`${block.language ?? ""}\n${block.code.trimEnd()}\n\`\`\``;
    case "image":
      return `![${block.alt ?? ""}](${block.url})`;
    case "html":
      return turndownService.turndown(block.html).trim();
    case "markdown":
      return block.markdown.trim();
  }
}

function isDefinedValue(value: unknown): boolean {
  return value !== undefined && value !== null && value !== "";
}

function renderFrontmatterValue(value: unknown): string {
  if (typeof value === "string") {
    if (value.includes("\n")) {
      return `|-\n${value
        .replace(/\r\n/g, "\n")
        .split("\n")
        .map((line) => `  ${line}`)
        .join("\n")}`;
    }
    return JSON.stringify(value);
  }
  if (typeof value === "number" || typeof value === "boolean") {
    return String(value);
  }
  return JSON.stringify(value);
}

function renderFrontmatter(document: ExtractedDocument): string {
  const fields = new Map<string, unknown>();
  const preferredOrder = [
    "title",
    "url",
    "requestedUrl",
    "author",
    "authorName",
    "authorUsername",
    "authorUrl",
    "coverImage",
    "siteName",
    "publishedAt",
    "summary",
    "adapter",
  ];

  fields.set("title", document.title);
  fields.set("url", document.canonicalUrl ?? document.url);
  fields.set("requestedUrl", document.requestedUrl ?? document.url);
  fields.set("author", document.author);
  fields.set("siteName", document.siteName);
  fields.set("publishedAt", document.publishedAt);
  fields.set("summary", document.summary);
  fields.set("adapter", document.adapter);

  for (const [key, value] of Object.entries(document.metadata ?? {})) {
    if (!fields.has(key)) {
      fields.set(key, value);
    }
  }

  const orderedKeys = [
    ...preferredOrder.filter((key) => fields.has(key)),
    ...Array.from(fields.keys()).filter((key) => !preferredOrder.includes(key)).sort(),
  ];

  const lines = orderedKeys
    .map((key) => [key, fields.get(key)] as const)
    .filter(([, value]) => isDefinedValue(value))
    .map(([key, value]) => `${key}: ${renderFrontmatterValue(value)}`);

  if (lines.length === 0) {
    return "";
  }

  return `---\n${lines.join("\n")}\n---`;
}

function cleanMarkdown(markdown: string): string {
  return normalizeMarkdownMediaLinks(markdown.replace(/\n{3,}/g, "\n\n").trim());
}

function normalizeComparableTitle(value: string): string {
  return value
    .trim()
    .toLowerCase()
    .replace(/^>\s*/, "")
    .replace(/^#+\s+/, "")
    .replace(/(?:\.{3}|…)\s*$/, "");
}

function bodyStartsWithTitle(body: string, title: string): boolean {
  const firstMeaningfulLine = body
    .replace(/\r\n/g, "\n")
    .split("\n")
    .map((line) => line.trim())
    .find((line) => line && !/^!?\[[^\]]*\]\([^)]+\)$/.test(line));

  if (!firstMeaningfulLine) {
    return false;
  }

  const comparableTitle = normalizeComparableTitle(title);
  const comparableFirstLine = normalizeComparableTitle(firstMeaningfulLine);
  if (!comparableTitle || !comparableFirstLine) {
    return false;
  }

  return (
    comparableFirstLine === comparableTitle ||
    comparableFirstLine.startsWith(comparableTitle) ||
    comparableTitle.startsWith(comparableFirstLine)
  );
}

export function renderMarkdown(document: ExtractedDocument): string {
  const sections: string[] = [];
  const frontmatter = renderFrontmatter(document);

  if (frontmatter) {
    sections.push(frontmatter);
  }

  const body = document.content
    .map((block) => renderBlock(block))
    .filter(Boolean)
    .join("\n\n");

  if (document.title && !bodyStartsWithTitle(body, document.title)) {
    sections.push(`# ${document.title}`);
  }

  if (body) {
    sections.push(body);
  }

  return cleanMarkdown(sections.join("\n\n"));
}
