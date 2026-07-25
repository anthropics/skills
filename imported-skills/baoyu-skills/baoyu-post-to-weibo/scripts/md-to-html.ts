import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import process from "node:process";

import {
  extractSummaryFromBody,
  extractTitleFromMarkdown,
  parseFrontmatter,
  pickFirstString,
  preprocessMermaidInMarkdown,
  renderMarkdownDocument,
  replaceMarkdownImagesWithPlaceholders,
  resolveColorToken,
  resolveContentImages,
  resolveImagePath,
  serializeFrontmatter,
  stripWrappingQuotes,
} from "baoyu-md";
import { closeRenderer, renderMermaidToPng } from "baoyu-chrome-cdp/mermaid";

interface ImageInfo {
  placeholder: string;
  localPath: string;
  originalPath: string;
  alt?: string;
}

interface ParsedMarkdown {
  title: string;
  summary: string;
  shortSummary: string;
  coverImage: string | null;
  contentImages: ImageInfo[];
  html: string;
}

export async function parseMarkdown(
  markdownPath: string,
  options?: {
    coverImage?: string;
    title?: string;
    tempDir?: string;
    theme?: string;
    color?: string;
    citeStatus?: boolean;
  },
): Promise<ParsedMarkdown> {
  const content = fs.readFileSync(markdownPath, "utf-8");
  const baseDir = path.dirname(markdownPath);
  const tempDir = options?.tempDir ?? fs.mkdtempSync(path.join(os.tmpdir(), "weibo-article-images-"));

  const { frontmatter, body } = parseFrontmatter(content);

  let title = stripWrappingQuotes(options?.title ?? "")
    || stripWrappingQuotes(frontmatter.title ?? "")
    || extractTitleFromMarkdown(body);
  if (!title) {
    title = path.basename(markdownPath, path.extname(markdownPath));
  }

  let summary = stripWrappingQuotes(frontmatter.summary ?? "")
    || stripWrappingQuotes(frontmatter.description ?? "")
    || stripWrappingQuotes(frontmatter.excerpt ?? "");
  if (!summary) {
    summary = extractSummaryFromBody(body, 44);
  }
  const shortSummary = extractSummaryFromBody(body, 44);

  const coverImagePath = stripWrappingQuotes(options?.coverImage ?? "")
    || pickFirstString(frontmatter, ["featureImage", "cover_image", "coverImage", "cover", "image"])
    || null;

  const { markdown: mermaidProcessedBody, images: mermaidImages } =
    await preprocessMermaidInMarkdown(body, {
      baseDir,
      renderFn: renderMermaidToPng,
      onError: (error, block) => {
        const message = error instanceof Error ? error.message : String(error);
        console.error(
          `[md-to-html] mermaid render failed (${block.code.slice(0, 40).replace(/\s+/g, " ")}…): ${message}`,
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
    "WBIMGPH_",
  );
  const rewrittenMarkdown = `${serializeFrontmatter(frontmatter)}${rewrittenBody}`;

  const { html } = await renderMarkdownDocument(rewrittenMarkdown, {
    citeStatus: options?.citeStatus ?? false,
    defaultTitle: title,
    keepTitle: false,
    primaryColor: resolveColorToken(options?.color),
    theme: options?.theme,
  });

  const contentImages = await resolveContentImages(images, baseDir, tempDir, "md-to-html");

  let resolvedCoverImage: string | null = null;
  if (coverImagePath) {
    resolvedCoverImage = await resolveImagePath(coverImagePath, baseDir, tempDir, "md-to-html");
  }

  return {
    title,
    summary,
    shortSummary,
    coverImage: resolvedCoverImage,
    contentImages,
    html,
  };
}

async function main(): Promise<void> {
  const args = process.argv.slice(2);
  if (args.length === 0 || args.includes("--help") || args.includes("-h")) {
    console.log(`Convert Markdown to HTML for Weibo article publishing

Usage:
  npx -y bun md-to-html.ts <markdown_file> [options]

Options:
  --title <title>       Override title
  --cover <image>       Override cover image
  --output <json|html>  Output format (default: json)
  --html-only           Output only the HTML content
  --save-html <path>    Save HTML to file
  --help                Show this help
`);
    process.exit(0);
  }

  let markdownPath: string | undefined;
  let title: string | undefined;
  let coverImage: string | undefined;
  let outputFormat: "json" | "html" = "json";
  let htmlOnly = false;
  let saveHtmlPath: string | undefined;

  for (let i = 0; i < args.length; i++) {
    const arg = args[i]!;
    if (arg === "--title" && args[i + 1]) {
      title = args[++i];
    } else if (arg === "--cover" && args[i + 1]) {
      coverImage = args[++i];
    } else if (arg === "--output" && args[i + 1]) {
      outputFormat = args[++i] as "json" | "html";
    } else if (arg === "--html-only") {
      htmlOnly = true;
    } else if (arg === "--save-html" && args[i + 1]) {
      saveHtmlPath = args[++i];
    } else if (!arg.startsWith("-")) {
      markdownPath = arg;
    }
  }

  if (!markdownPath || !fs.existsSync(markdownPath)) {
    console.error("Error: Valid markdown file path required");
    process.exit(1);
  }

  const result = await parseMarkdown(markdownPath, { title, coverImage });

  if (saveHtmlPath) {
    fs.writeFileSync(saveHtmlPath, result.html, "utf-8");
    console.error(`[md-to-html] HTML saved to: ${saveHtmlPath}`);
  }

  if (htmlOnly || outputFormat === "html") {
    console.log(result.html);
  } else {
    console.log(JSON.stringify(result, null, 2));
  }
}

if (import.meta.main ?? (process.argv[1] && path.resolve(process.argv[1]) === path.resolve(import.meta.filename ?? ""))) {
  try {
    await main();
  } catch (error) {
    console.error(`Error: ${error instanceof Error ? error.message : String(error)}`);
    process.exitCode = 1;
  } finally {
    await closeRenderer();
  }
}
