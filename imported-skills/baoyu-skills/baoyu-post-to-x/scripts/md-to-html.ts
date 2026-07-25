import fs from 'node:fs';
import { mkdir, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { pathToFileURL } from 'node:url';

import frontMatter from 'front-matter';
import hljs from 'highlight.js/lib/common';
import { Lexer, Marked, type RendererObject, type Tokens } from 'marked';
import { unified } from 'unified';
import remarkCjkFriendly from 'remark-cjk-friendly';
import remarkParse from 'remark-parse';
import remarkStringify from 'remark-stringify';

import {
  preprocessMermaidInMarkdown,
  replaceMarkdownImagesWithPlaceholders,
  resolveImagePath,
} from 'baoyu-md';
import { closeRenderer, renderMermaidToPng } from 'baoyu-chrome-cdp/mermaid';

interface ImageInfo {
  placeholder: string;
  localPath: string;
  originalPath: string;
  blockIndex: number;
  alt?: string;
}

interface ParsedMarkdown {
  title: string;
  coverImage: string | null;
  contentImages: ImageInfo[];
  html: string;
  totalBlocks: number;
}

type FrontmatterFields = Record<string, unknown>;

function parseFrontmatter(content: string): { frontmatter: FrontmatterFields; body: string } {
  try {
    const parsed = frontMatter<FrontmatterFields>(content);
    return {
      frontmatter: parsed.attributes ?? {},
      body: parsed.body,
    };
  } catch {
    return { frontmatter: {}, body: content };
  }
}

function stripWrappingQuotes(value: string): string {
  if (!value) return value;
  const doubleQuoted = value.startsWith('"') && value.endsWith('"');
  const singleQuoted = value.startsWith("'") && value.endsWith("'");
  const cjkDoubleQuoted = value.startsWith('\u201c') && value.endsWith('\u201d');
  const cjkSingleQuoted = value.startsWith('\u2018') && value.endsWith('\u2019');
  if (doubleQuoted || singleQuoted || cjkDoubleQuoted || cjkSingleQuoted) {
    return value.slice(1, -1).trim();
  }
  return value.trim();
}

function toFrontmatterString(value: unknown): string | undefined {
  if (typeof value === 'string') {
    return stripWrappingQuotes(value);
  }
  if (typeof value === 'number' || typeof value === 'boolean') {
    return String(value);
  }
  return undefined;
}

function pickFirstString(frontmatter: FrontmatterFields, keys: string[]): string | undefined {
  for (const key of keys) {
    const value = toFrontmatterString(frontmatter[key]);
    if (value) return value;
  }
  return undefined;
}

function findCoverImageNearMarkdown(baseDir: string): string | null {
  const candidateDirs = [baseDir, path.join(baseDir, 'imgs')];
  const coverPattern = /^cover\.(png|jpe?g|webp)$/i;

  for (const dir of candidateDirs) {
    try {
      if (!fs.existsSync(dir) || !fs.statSync(dir).isDirectory()) {
        continue;
      }

      const match = fs.readdirSync(dir).find((entry) => coverPattern.test(entry));
      if (match) {
        return path.join(dir, match);
      }
    } catch {
      continue;
    }
  }

  return null;
}

function extractTitleFromMarkdown(markdown: string): string {
  const tokens = Lexer.lex(markdown, { gfm: true, breaks: true });
  for (const token of tokens) {
    if (token.type === 'heading' && token.depth === 1) {
      return stripWrappingQuotes(token.text);
    }
  }
  return '';
}

function escapeHtml(text: string): string {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;')
    .replace(/'/g, '&#39;');
}

function escapeRegExp(value: string): string {
  return value.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
}

function highlightCode(code: string, lang: string): string {
  try {
    if (lang && hljs.getLanguage(lang)) {
      return hljs.highlight(code, { language: lang, ignoreIllegals: true }).value;
    }
    return hljs.highlightAuto(code).value;
  } catch {
    return escapeHtml(code);
  }
}

// Normalize CJK-adjacent emphasis so `marked` renders it correctly.
//
// `marked`'s emphasis tokenizer treats a closing `**`/`*` directly followed by a
// CJK character as not right-flanking, so it leaves the delimiters literal
// (e.g. `**加粗**这` renders as plain text with the asterisks intact). We round-trip
// the markdown through `remark-cjk-friendly`, whose stringify serializes the
// boundary character as an HTML entity (`&#x8FD9;`); the entity is treated as
// punctuation by `marked`'s flanking rules, so emphasis parses as expected.
//
// We deliberately do NOT decode the entities afterward. They are valid HTML
// character references that render correctly when the article HTML is pasted into
// the X editor, and `marked` only emits them for characters outside the emphasis
// span (the boundary char), never inside it. A blanket decode of the rendered
// HTML would risk turning author-written literal entities (e.g. `&#x3C;b&#x3E;`
// meant to display `<b>` as text) into real tags, so we leave them intact.
function preprocessCjkMarkdown(markdown: string): string {
  try {
    const processor = unified()
      .use(remarkParse)
      .use(remarkCjkFriendly)
      .use(remarkStringify);

    return String(processor.processSync(markdown));
  } catch {
    return markdown;
  }
}

function convertMarkdownToHtml(markdown: string): { html: string; totalBlocks: number } {
  const preprocessedMarkdown = preprocessCjkMarkdown(markdown);
  const blockTokens = Lexer.lex(preprocessedMarkdown, { gfm: true, breaks: true });

  const renderer: RendererObject = {
    heading({ depth, tokens }: Tokens.Heading): string {
      if (depth === 1) {
        return '';
      }
      return `<h2>${this.parser.parseInline(tokens)}</h2>`;
    },

    paragraph({ tokens }: Tokens.Paragraph): string {
      const text = this.parser.parseInline(tokens).trim();
      if (!text) return '';
      return `<p>${text}</p>`;
    },

    blockquote({ tokens }: Tokens.Blockquote): string {
      return `<blockquote>${this.parser.parse(tokens)}</blockquote>`;
    },

    code({ text, lang = '' }: Tokens.Code): string {
      const language = lang.split(/\s+/)[0]!.toLowerCase();
      const source = text.replace(/\n$/, '');
      const highlighted = highlightCode(source, language).replace(/\n/g, '<br>');
      const label = language ? `<strong>[${escapeHtml(language)}]</strong><br>` : '';
      return `<blockquote>${label}${highlighted}</blockquote>`;
    },

    image({ href, text }: Tokens.Image): string {
      if (!href) return '';
      return escapeHtml(text ?? '');
    },

    link({ href, title, tokens, text }: Tokens.Link): string {
      const label = tokens?.length ? this.parser.parseInline(tokens) : escapeHtml(text || href || '');
      if (!href) return label;

      const titleAttr = title ? ` title="${escapeHtml(title)}"` : '';
      return `<a href="${escapeHtml(href)}"${titleAttr} rel="noopener noreferrer nofollow">${label}</a>`;
    },
  };

  const parser = new Marked({
    gfm: true,
    breaks: true,
  });
  parser.use({ renderer });

  const rendered = parser.parse(preprocessedMarkdown);
  if (typeof rendered !== 'string') {
    throw new Error('Unexpected async markdown parse result');
  }

  const totalBlocks = blockTokens.filter((token) => {
    if (token.type === 'space') return false;
    if (token.type === 'heading' && token.depth === 1) return false;
    return true;
  }).length;

  return {
    html: rendered,
    totalBlocks,
  };
}

export async function parseMarkdown(
  markdownPath: string,
  options?: { coverImage?: string; title?: string; tempDir?: string },
): Promise<ParsedMarkdown> {
  const content = fs.readFileSync(markdownPath, 'utf-8');
  const baseDir = path.dirname(markdownPath);
  const tempDir = options?.tempDir ?? path.join(os.tmpdir(), 'x-article-images');

  await mkdir(tempDir, { recursive: true });

  const { frontmatter, body } = parseFrontmatter(content);

  let title = stripWrappingQuotes(options?.title ?? '') || pickFirstString(frontmatter, ['title']) || '';
  if (!title) {
    title = extractTitleFromMarkdown(body);
  }
  if (!title) {
    title = path.basename(markdownPath, path.extname(markdownPath));
  }

  let coverImagePath = stripWrappingQuotes(options?.coverImage ?? '') || pickFirstString(frontmatter, [
    'cover_image',
    'coverImage',
    'cover',
    'image',
    'featureImage',
    'feature_image',
  ]) || null;
  if (!coverImagePath) {
    coverImagePath = findCoverImageNearMarkdown(baseDir);
  }

  const { markdown: mermaidProcessedBody, images: mermaidImages } =
    await preprocessMermaidInMarkdown(body, {
      baseDir,
      renderFn: renderMermaidToPng,
      onError: (error, block) => {
        const message = error instanceof Error ? error.message : String(error);
        console.error(
          `[md-to-html] mermaid render failed (${block.code.slice(0, 40).replace(/\s+/g, ' ')}…): ${message}`,
        );
      },
    });

  if (mermaidImages.length > 0) {
    const fresh = mermaidImages.filter((image) => !image.cached).length;
    console.error(
      `[md-to-html] mermaid: ${mermaidImages.length} block(s), ${fresh} rendered, ${mermaidImages.length - fresh} cached`,
    );
  }

  const { images, markdown: rewrittenBody } = replaceMarkdownImagesWithPlaceholders(
    mermaidProcessedBody,
    'XIMGPH_',
  );
  const { html, totalBlocks } = convertMarkdownToHtml(rewrittenBody);

  const htmlLines = html.split('\n');
  const imageBlockIndexes = new Map<string, number>();
  for (let i = 0; i < images.length; i++) {
    const placeholder = images[i]!.placeholder;
    for (let lineIndex = 0; lineIndex < htmlLines.length; lineIndex++) {
      const regex = new RegExp(`\\b${escapeRegExp(placeholder)}\\b`);
      if (regex.test(htmlLines[lineIndex]!)) {
        imageBlockIndexes.set(placeholder, lineIndex);
        break;
      }
    }
  }

  const contentImages: ImageInfo[] = [];
  let firstImageAsCover: string | null = null;

  for (let i = 0; i < images.length; i++) {
    const img = images[i]!;
    const localPath = await resolveImagePath(img.originalPath, baseDir, tempDir, 'md-to-html');

    if (i === 0 && !coverImagePath) {
      firstImageAsCover = localPath;
    }

    contentImages.push({
      placeholder: img.placeholder,
      localPath,
      originalPath: img.originalPath,
      alt: img.alt,
      blockIndex: imageBlockIndexes.get(img.placeholder) ?? -1,
    });
  }

  const finalHtml = html.replace(/\n{3,}/g, '\n\n').trim();

  let resolvedCoverImage: string | null = null;
  if (coverImagePath) {
    resolvedCoverImage = await resolveImagePath(coverImagePath, baseDir, tempDir, 'md-to-html');
  } else if (firstImageAsCover) {
    resolvedCoverImage = firstImageAsCover;
  }

  return {
    title,
    coverImage: resolvedCoverImage,
    contentImages,
    html: finalHtml,
    totalBlocks,
  };
}

function printUsage(): never {
  console.log(`Convert Markdown to HTML for X Article publishing

Usage:
  npx -y bun md-to-html.ts <markdown_file> [options]

Options:
  --title <title>       Override title from frontmatter
  --cover <image>       Override cover image from frontmatter
  --output <json|html>  Output format (default: json)
  --html-only           Output only the HTML content
  --save-html <path>    Save HTML to file

Frontmatter fields:
  title: Article title (or use first H1)
  cover_image: Cover image path or URL
  cover: Alias for cover_image
  image: Alias for cover_image

Example:
  npx -y bun md-to-html.ts article.md --output json
  npx -y bun md-to-html.ts article.md --html-only > /tmp/article.html
  npx -y bun md-to-html.ts article.md --save-html /tmp/article.html
`);
  process.exit(0);
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes('--help') || args.includes('-h')) {
    printUsage();
  }

  let markdownPath: string | undefined;
  let title: string | undefined;
  let coverImage: string | undefined;
  let outputFormat: 'json' | 'html' = 'json';
  let htmlOnly = false;
  let saveHtmlPath: string | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === '--title' && args[i + 1]) {
      title = args[++i];
    } else if (arg === '--cover' && args[i + 1]) {
      coverImage = args[++i];
    } else if (arg === '--output' && args[i + 1]) {
      outputFormat = args[++i] as 'json' | 'html';
    } else if (arg === '--html-only') {
      htmlOnly = true;
    } else if (arg === '--save-html' && args[i + 1]) {
      saveHtmlPath = args[++i];
    } else if (!arg.startsWith('-')) {
      markdownPath = arg;
    }
  }

  if (!markdownPath) {
    console.error('Error: Markdown file path required');
    process.exit(1);
  }

  if (!fs.existsSync(markdownPath)) {
    console.error(`Error: File not found: ${markdownPath}`);
    process.exit(1);
  }

  const result = await parseMarkdown(markdownPath, { title, coverImage });

  if (saveHtmlPath) {
    await writeFile(saveHtmlPath, result.html, 'utf-8');
    console.error(`[md-to-html] HTML saved to: ${saveHtmlPath}`);
  }

  if (htmlOnly) {
    console.log(result.html);
  } else if (outputFormat === 'html') {
    console.log(result.html);
  } else {
    console.log(JSON.stringify(result, null, 2));
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  try {
    await main();
  } catch (err) {
    console.error(`Error: ${err instanceof Error ? err.message : String(err)}`);
    process.exitCode = 1;
  } finally {
    await closeRenderer();
  }
}
