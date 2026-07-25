import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import process from "node:process";

import {
  COLOR_PRESETS,
  FONT_FAMILY_MAP,
  FONT_SIZE_OPTIONS,
  THEME_NAMES,
  extractSummaryFromBody,
  extractTitleFromMarkdown,
  formatTimestamp,
  parseArgs,
  parseFrontmatter,
  preprocessMermaidInMarkdown,
  renderMarkdownDocument,
  replaceMarkdownImagesWithPlaceholders,
  resolveContentImages,
  serializeFrontmatter,
  stripWrappingQuotes,
} from "baoyu-md";
import type { CliOptions } from "baoyu-md";
import { closeRenderer, renderMermaidToPng } from "baoyu-chrome-cdp/mermaid";

interface ImageInfo {
  placeholder: string;
  localPath: string;
  originalPath: string;
  alt?: string;
}

interface MermaidImageInfo {
  hash: string;
  localPath: string;
  cached: boolean;
}

interface ParsedResult {
  title: string;
  author: string;
  summary: string;
  htmlPath: string;
  backupPath?: string;
  contentImages: ImageInfo[];
  mermaidImages: MermaidImageInfo[];
}

interface MermaidCliOptions {
  enabled?: boolean;
  theme?: string;
  scale?: number;
  background?: string;
  minWidth?: number;
}

type ConvertMarkdownOptions = Partial<Omit<CliOptions, "inputPath">> & {
  title?: string;
  mermaid?: MermaidCliOptions;
};

function escapeHtmlAttribute(value: string): string {
  return value
    .replace(/&/g, "&amp;")
    .replace(/"/g, "&quot;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;");
}

export async function convertMarkdown(
  markdownPath: string,
  options?: ConvertMarkdownOptions,
): Promise<ParsedResult> {
  const baseDir = path.dirname(markdownPath);
  const content = fs.readFileSync(markdownPath, "utf-8");
  const theme = options?.theme;
  const keepTitle = options?.keepTitle ?? false;
  const citeStatus = options?.citeStatus ?? false;

  const { frontmatter, body } = parseFrontmatter(content);

  let title = stripWrappingQuotes(options?.title ?? "")
    || stripWrappingQuotes(frontmatter.title ?? "")
    || extractTitleFromMarkdown(body);
  if (!title) {
    title = path.basename(markdownPath, path.extname(markdownPath));
  }

  const author = stripWrappingQuotes(frontmatter.author ?? "");
  let summary = stripWrappingQuotes(frontmatter.description ?? "")
    || stripWrappingQuotes(frontmatter.summary ?? "");
  if (!summary) {
    summary = extractSummaryFromBody(body, 120);
  }

  const effectiveFrontmatter = options?.title
    ? { ...frontmatter, title }
    : frontmatter;

  const mermaidEnabled = options?.mermaid?.enabled !== false;
  const mermaidMinWidth = options?.mermaid?.minWidth ?? 860;
  const { markdown: mermaidProcessedBody, images: mermaidImages } =
    await preprocessMermaidInMarkdown(body, {
      baseDir,
      renderFn: renderMermaidToPng,
      enabled: mermaidEnabled,
      theme: options?.mermaid?.theme,
      scale: options?.mermaid?.scale,
      background: options?.mermaid?.background,
      minWidth: mermaidMinWidth,
      onError: (error, block) => {
        const message = error instanceof Error ? error.message : String(error);
        console.error(
          `[markdown-to-html] mermaid render failed (${block.code.slice(0, 40).replace(/\s+/g, " ")}…): ${message}`,
        );
      },
    });

  if (mermaidImages.length > 0) {
    const fresh = mermaidImages.filter((image) => !image.cached).length;
    console.error(
      `[markdown-to-html] mermaid: ${mermaidImages.length} block(s), ${fresh} rendered, ${mermaidImages.length - fresh} cached`,
    );
  }

  const { images, markdown: rewrittenBody } = replaceMarkdownImagesWithPlaceholders(
    mermaidProcessedBody,
    "MDTOHTMLIMGPH_",
  );
  const rewrittenMarkdown = `${serializeFrontmatter(effectiveFrontmatter)}${rewrittenBody}`;

  console.error(
    `[markdown-to-html] Rendering with theme: ${theme ?? "default"}, keepTitle: ${keepTitle}, citeStatus: ${citeStatus}`,
  );

  const { html } = await renderMarkdownDocument(rewrittenMarkdown, {
    codeTheme: options?.codeTheme,
    countStatus: options?.countStatus,
    citeStatus,
    defaultTitle: title,
    fontFamily: options?.fontFamily,
    fontSize: options?.fontSize,
    isMacCodeBlock: options?.isMacCodeBlock,
    isShowLineNumber: options?.isShowLineNumber,
    keepTitle,
    legend: options?.legend,
    primaryColor: options?.primaryColor,
    theme,
  });

  const finalHtmlPath = markdownPath.replace(/\.md$/i, ".html");
  let backupPath: string | undefined;

  if (fs.existsSync(finalHtmlPath)) {
    backupPath = `${finalHtmlPath}.bak-${formatTimestamp()}`;
    console.error(`[markdown-to-html] Backing up existing file to: ${backupPath}`);
    fs.renameSync(finalHtmlPath, backupPath);
  }

  fs.writeFileSync(finalHtmlPath, html, "utf-8");

  const hasRemoteImages = images.some((image) =>
    image.originalPath.startsWith("http://") || image.originalPath.startsWith("https://"),
  );
  const tempDir = hasRemoteImages
    ? fs.mkdtempSync(path.join(os.tmpdir(), "markdown-to-html-"))
    : baseDir;
  const contentImages = await resolveContentImages(images, baseDir, tempDir, "markdown-to-html");

  let finalContent = fs.readFileSync(finalHtmlPath, "utf-8");
  for (const image of contentImages) {
    const altAttr = image.alt !== undefined
      ? ` alt="${escapeHtmlAttribute(image.alt)}"`
      : "";
    const imgTag = `<img src="${escapeHtmlAttribute(image.originalPath)}" `
      + `data-local-path="${escapeHtmlAttribute(image.localPath)}"${altAttr} `
      + `style="display: block; width: 100%; margin: 1.5em auto;">`;
    finalContent = finalContent.replace(image.placeholder, imgTag);
  }
  fs.writeFileSync(finalHtmlPath, finalContent, "utf-8");

  console.error(`[markdown-to-html] HTML saved to: ${finalHtmlPath}`);

  return {
    title,
    author,
    summary,
    htmlPath: finalHtmlPath,
    backupPath,
    contentImages,
    mermaidImages: mermaidImages.map((image) => ({
      hash: image.hash,
      localPath: image.localPath,
      cached: image.cached,
    })),
  };
}

function printUsage(exitCode = 0): never {
  const colorNames = Object.keys(COLOR_PRESETS).join(", ");
  const fontFamilyNames = Object.keys(FONT_FAMILY_MAP).join(", ");

  console.log(`Convert Markdown to styled HTML

Usage:
  npx -y bun main.ts <markdown_file> [options]

Options:
  --title <title>         Override title
  --theme <name>          Theme name (${THEME_NAMES.join(", ")}). Default: default
  --color <name|hex>      Primary color: ${colorNames}
  --font-family <name>    Font: ${fontFamilyNames}, or CSS value
  --font-size <N>         Font size: ${FONT_SIZE_OPTIONS.join(", ")} (default: 16px)
  --code-theme <name>     Code highlight theme (default: github)
  --mac-code-block        Show Mac-style code block header
  --no-mac-code-block     Hide Mac-style code block header
  --line-number           Show line numbers in code blocks
  --cite                  Convert ordinary external links to bottom citations. Default: off
  --count                 Show reading time / word count
  --legend <value>        Image caption: title-alt, alt-title, title, alt, none
  --keep-title            Keep the first heading in content. Default: false (removed)
  --mermaid-theme <name>  Mermaid theme: default, forest, dark, neutral. Default: default
  --mermaid-scale <N>     Mermaid render scale: 1, 1.5, 2, 3. Default: 2
  --mermaid-width <N>     Mermaid target display width in CSS px. Default: 860
  --mermaid-bg <value>    Mermaid background: white, transparent, or #hex. Default: white
  --no-mermaid            Skip Mermaid rendering; emit <pre class="mermaid"> fallback
  --help                  Show this help

Output:
  HTML file saved to same directory as input markdown file.
  Example: article.md -> article.html

  If HTML file already exists, it will be backed up first:
  article.html -> article.html.bak-YYYYMMDDHHMMSS

Output JSON format:
{
  "title": "Article Title",
  "htmlPath": "/path/to/article.html",
  "backupPath": "/path/to/article.html.bak-20260128180000",
  "contentImages": [...]
}

Example:
  npx -y bun main.ts article.md
  npx -y bun main.ts article.md --theme grace
  npx -y bun main.ts article.md --theme modern --color red
  npx -y bun main.ts article.md --cite
`);
  process.exit(exitCode);
}

function parseArgValue(argv: string[], i: number, flag: string): string | null {
  const arg = argv[i]!;
  if (arg.includes("=")) {
    return arg.slice(flag.length + 1);
  }
  const next = argv[i + 1];
  return next ?? null;
}

function extractTitleArg(argv: string[]): { renderArgs: string[]; title?: string } {
  let title: string | undefined;
  const renderArgs: string[] = [];

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i]!;
    if (arg === "--title" || arg.startsWith("--title=")) {
      const value = parseArgValue(argv, i, "--title");
      if (!value) {
        console.error("Missing value for --title");
        printUsage(1);
      }
      title = value;
      if (!arg.includes("=")) {
        i += 1;
      }
      continue;
    }
    renderArgs.push(arg);
  }

  return { renderArgs, title };
}

const VALID_MERMAID_THEMES = new Set(["default", "forest", "dark", "neutral", "base"]);

function extractMermaidArgs(argv: string[]): { renderArgs: string[]; mermaid: MermaidCliOptions } {
  const mermaid: MermaidCliOptions = {};
  const renderArgs: string[] = [];

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i]!;
    if (arg === "--no-mermaid") {
      mermaid.enabled = false;
      continue;
    }
    if (arg === "--mermaid-theme" || arg.startsWith("--mermaid-theme=")) {
      const value = parseArgValue(argv, i, "--mermaid-theme");
      if (!value) {
        console.error("Missing value for --mermaid-theme");
        printUsage(1);
      }
      if (!VALID_MERMAID_THEMES.has(value)) {
        console.error(`Invalid --mermaid-theme: ${value} (choose one of ${[...VALID_MERMAID_THEMES].join(", ")})`);
        printUsage(1);
      }
      mermaid.theme = value;
      if (!arg.includes("=")) i += 1;
      continue;
    }
    if (arg === "--mermaid-scale" || arg.startsWith("--mermaid-scale=")) {
      const value = parseArgValue(argv, i, "--mermaid-scale");
      const parsed = Number.parseFloat(value ?? "");
      if (!value || !Number.isFinite(parsed) || parsed <= 0 || parsed > 4) {
        console.error(`Invalid --mermaid-scale: ${value} (expect a positive number ≤ 4)`);
        printUsage(1);
      }
      mermaid.scale = parsed;
      if (!arg.includes("=")) i += 1;
      continue;
    }
    if (arg === "--mermaid-width" || arg.startsWith("--mermaid-width=")) {
      const value = parseArgValue(argv, i, "--mermaid-width");
      const parsed = Number.parseInt(value ?? "", 10);
      if (!value || !Number.isFinite(parsed) || parsed <= 0) {
        console.error(`Invalid --mermaid-width: ${value} (expect a positive integer)`);
        printUsage(1);
      }
      mermaid.minWidth = parsed;
      if (!arg.includes("=")) i += 1;
      continue;
    }
    if (arg === "--mermaid-bg" || arg.startsWith("--mermaid-bg=")) {
      const value = parseArgValue(argv, i, "--mermaid-bg");
      if (!value) {
        console.error("Missing value for --mermaid-bg");
        printUsage(1);
      }
      mermaid.background = value;
      if (!arg.includes("=")) i += 1;
      continue;
    }
    renderArgs.push(arg);
  }

  return { renderArgs, mermaid };
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes("--help") || args.includes("-h")) {
    printUsage(0);
  }

  const { renderArgs: afterTitle, title } = extractTitleArg(args);
  const { renderArgs, mermaid } = extractMermaidArgs(afterTitle);
  const options = parseArgs(renderArgs);
  if (!options) {
    printUsage(1);
  }

  const markdownPath = path.resolve(process.cwd(), options.inputPath);
  if (!markdownPath.toLowerCase().endsWith(".md")) {
    console.error("Input file must end with .md");
    process.exit(1);
  }

  if (!fs.existsSync(markdownPath)) {
    console.error(`Error: File not found: ${markdownPath}`);
    process.exit(1);
  }

  const result = await convertMarkdown(markdownPath, { ...options, title, mermaid });
  console.log(JSON.stringify(result, null, 2));
}

try {
  await main();
} catch (error) {
  console.error(`Error: ${error instanceof Error ? error.message : String(error)}`);
  process.exitCode = 1;
} finally {
  await closeRenderer();
}
