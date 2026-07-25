import path from "node:path";
import { mkdir, writeFile } from "node:fs/promises";

type MediaKind = "image" | "video";
type MediaHint = "image" | "unknown";

type MarkdownLinkCandidate = {
  url: string;
  hint: MediaHint;
};

export type LocalizeMarkdownMediaOptions = {
  markdownPath: string;
  log?: (message: string) => void;
};

export type LocalizeMarkdownMediaResult = {
  markdown: string;
  downloadedImages: number;
  downloadedVideos: number;
  imageDir: string | null;
  videoDir: string | null;
};

const MARKDOWN_LINK_RE = /(!?\[[^\]\n]*\])\((<)?(https?:\/\/[^)\s>]+)(>)?\)/g;

const IMAGE_EXTENSIONS = new Set([
  "jpg",
  "jpeg",
  "png",
  "webp",
  "gif",
  "bmp",
  "avif",
  "heic",
  "heif",
  "svg",
]);

const VIDEO_EXTENSIONS = new Set(["mp4", "m4v", "mov", "webm", "mkv"]);

const MIME_EXTENSION_MAP: Record<string, string> = {
  "image/jpeg": "jpg",
  "image/jpg": "jpg",
  "image/png": "png",
  "image/webp": "webp",
  "image/gif": "gif",
  "image/bmp": "bmp",
  "image/avif": "avif",
  "image/heic": "heic",
  "image/heif": "heif",
  "image/svg+xml": "svg",
  "video/mp4": "mp4",
  "video/webm": "webm",
  "video/quicktime": "mov",
  "video/x-m4v": "m4v",
};

const DOWNLOAD_USER_AGENT =
  "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36";

function normalizeContentType(raw: string | null): string {
  return raw?.split(";")[0]?.trim().toLowerCase() ?? "";
}

function normalizeExtension(raw: string | undefined | null): string | undefined {
  if (!raw) return undefined;
  const trimmed = raw.replace(/^\./, "").trim().toLowerCase();
  if (!trimmed) return undefined;
  if (trimmed === "jpeg") return "jpg";
  if (trimmed === "jpg") return "jpg";
  return trimmed;
}

function resolveExtensionFromUrl(rawUrl: string): string | undefined {
  try {
    const parsed = new URL(rawUrl);
    const extFromPath = normalizeExtension(path.posix.extname(parsed.pathname));
    if (extFromPath) return extFromPath;
    const extFromFormat = normalizeExtension(parsed.searchParams.get("format"));
    if (extFromFormat) return extFromFormat;
  } catch {
    return undefined;
  }
  return undefined;
}

function resolveKindFromContentType(contentType: string): MediaKind | undefined {
  if (!contentType) return undefined;
  if (contentType.startsWith("image/")) return "image";
  if (contentType.startsWith("video/")) return "video";
  return undefined;
}

function resolveKindFromExtension(ext: string | undefined): MediaKind | undefined {
  if (!ext) return undefined;
  if (IMAGE_EXTENSIONS.has(ext)) return "image";
  if (VIDEO_EXTENSIONS.has(ext)) return "video";
  return undefined;
}

function resolveKindFromHostname(rawUrl: string): MediaKind | undefined {
  try {
    const hostname = new URL(rawUrl).hostname.toLowerCase();
    if (hostname.includes("video.twimg.com")) return "video";
    if (hostname.includes("pbs.twimg.com")) return "image";
  } catch {
    return undefined;
  }
  return undefined;
}

function resolveMediaKind(
  rawUrl: string,
  contentType: string,
  extension: string | undefined,
  hint: MediaHint
): MediaKind | undefined {
  const kindFromType = resolveKindFromContentType(contentType);
  if (kindFromType) return kindFromType;

  const kindFromExtension = resolveKindFromExtension(extension);
  if (kindFromExtension) return kindFromExtension;

  const kindFromHost = resolveKindFromHostname(rawUrl);
  if (kindFromHost) return kindFromHost;

  if (contentType && contentType !== "application/octet-stream") {
    return undefined;
  }

  return hint === "image" ? "image" : undefined;
}

function resolveOutputExtension(
  contentType: string,
  extension: string | undefined,
  kind: MediaKind
): string {
  const extFromMime = normalizeExtension(MIME_EXTENSION_MAP[contentType]);
  if (extFromMime) return extFromMime;

  const normalizedExt = normalizeExtension(extension);
  if (normalizedExt) return normalizedExt;

  return kind === "video" ? "mp4" : "jpg";
}

function safeDecodeURIComponent(value: string): string {
  try {
    return decodeURIComponent(value);
  } catch {
    return value;
  }
}

function sanitizeFileSegment(input: string): string {
  return input
    .replace(/[^a-zA-Z0-9_-]+/g, "-")
    .replace(/-+/g, "-")
    .replace(/^[-_]+|[-_]+$/g, "")
    .slice(0, 48);
}

function resolveFileStem(rawUrl: string, extension: string): string {
  try {
    const parsed = new URL(rawUrl);
    const base = path.posix.basename(parsed.pathname);
    if (!base) return "";
    const decodedBase = safeDecodeURIComponent(base);
    const normalizedExt = normalizeExtension(extension);
    const stripExt = normalizedExt ? new RegExp(`\\.${normalizedExt}$`, "i") : null;
    const rawStem = stripExt ? decodedBase.replace(stripExt, "") : decodedBase;
    return sanitizeFileSegment(rawStem);
  } catch {
    return "";
  }
}

function buildFileName(kind: MediaKind, index: number, sourceUrl: string, extension: string): string {
  const stem = resolveFileStem(sourceUrl, extension);
  const prefix = kind === "image" ? "img" : "video";
  const serial = String(index).padStart(3, "0");
  const suffix = stem ? `-${stem}` : "";
  return `${prefix}-${serial}${suffix}.${extension}`;
}

const FRONTMATTER_COVER_RE = /^(coverImage:\s*")(https?:\/\/[^"]+)(")/m;

function toHighResUrl(rawUrl: string): string {
  try {
    const parsed = new URL(rawUrl);
    if (parsed.hostname !== "pbs.twimg.com") return rawUrl;
    const ext = path.posix.extname(parsed.pathname).replace(/^\./, "").toLowerCase();
    if (!ext || !IMAGE_EXTENSIONS.has(ext)) return rawUrl;
    parsed.pathname = parsed.pathname.replace(new RegExp(`\\.${ext}$`), "");
    parsed.searchParams.set("format", ext === "jpeg" ? "jpg" : ext);
    parsed.searchParams.set("name", "4096x4096");
    return parsed.toString();
  } catch {
    return rawUrl;
  }
}

function isPlausibleMediaUrl(rawUrl: string): boolean {
  const ext = resolveExtensionFromUrl(rawUrl);
  if (ext && (IMAGE_EXTENSIONS.has(ext) || VIDEO_EXTENSIONS.has(ext))) return true;
  if (resolveKindFromHostname(rawUrl) !== undefined) return true;
  return false;
}

function collectMarkdownLinkCandidates(markdown: string): MarkdownLinkCandidate[] {
  const candidates: MarkdownLinkCandidate[] = [];
  const seen = new Set<string>();

  const fmMatch = markdown.match(/^---\n([\s\S]*?)\n---/);
  if (fmMatch) {
    const coverMatch = fmMatch[1]?.match(FRONTMATTER_COVER_RE);
    if (coverMatch?.[2] && !seen.has(coverMatch[2])) {
      seen.add(coverMatch[2]);
      candidates.push({ url: coverMatch[2], hint: "image" });
    }
  }

  MARKDOWN_LINK_RE.lastIndex = 0;
  let match: RegExpExecArray | null;
  while ((match = MARKDOWN_LINK_RE.exec(markdown))) {
    const label = match[1] ?? "";
    const rawUrl = match[3] ?? "";
    if (!rawUrl || seen.has(rawUrl)) continue;
    const isImage = label.startsWith("![");
    if (!isImage && !isPlausibleMediaUrl(rawUrl)) continue;
    seen.add(rawUrl);
    candidates.push({
      url: rawUrl,
      hint: isImage ? "image" : "unknown",
    });
  }

  return candidates;
}

function rewriteMarkdownMediaLinks(markdown: string, replacements: Map<string, string>): string {
  if (replacements.size === 0) return markdown;
  MARKDOWN_LINK_RE.lastIndex = 0;

  let result = markdown.replace(MARKDOWN_LINK_RE, (full, label, _openAngle, rawUrl) => {
    const localPath = replacements.get(rawUrl);
    if (!localPath) return full;
    return `${label}(${localPath})`;
  });

  result = result.replace(FRONTMATTER_COVER_RE, (full, prefix, rawUrl, suffix) => {
    const localPath = replacements.get(rawUrl);
    if (!localPath) return full;
    return `${prefix}${localPath}${suffix}`;
  });

  return result;
}

export async function localizeMarkdownMedia(
  markdown: string,
  options: LocalizeMarkdownMediaOptions
): Promise<LocalizeMarkdownMediaResult> {
  const log = options.log ?? (() => {});
  const markdownDir = path.dirname(options.markdownPath);
  const candidates = collectMarkdownLinkCandidates(markdown);

  if (candidates.length === 0) {
    return {
      markdown,
      downloadedImages: 0,
      downloadedVideos: 0,
      imageDir: null,
      videoDir: null,
    };
  }

  const replacements = new Map<string, string>();
  let downloadedImages = 0;
  let downloadedVideos = 0;

  for (const candidate of candidates) {
    try {
      const downloadUrl = toHighResUrl(candidate.url);
      const response = await fetch(downloadUrl, {
        method: "GET",
        redirect: "follow",
        headers: {
          "user-agent": DOWNLOAD_USER_AGENT,
        },
      });

      if (!response.ok) {
        log(`[x-to-markdown] Skip media (${response.status}): ${candidate.url}`);
        continue;
      }

      const sourceUrl = response.url || candidate.url;
      const contentType = normalizeContentType(response.headers.get("content-type"));
      const extension = resolveExtensionFromUrl(sourceUrl) ?? resolveExtensionFromUrl(candidate.url);
      const kind = resolveMediaKind(sourceUrl, contentType, extension, candidate.hint);
      if (!kind) {
        continue;
      }

      const outputExtension = resolveOutputExtension(contentType, extension, kind);
      const nextIndex = kind === "image" ? downloadedImages + 1 : downloadedVideos + 1;
      const dirName = kind === "image" ? "imgs" : "videos";
      const targetDir = path.join(markdownDir, dirName);
      await mkdir(targetDir, { recursive: true });

      const fileName = buildFileName(kind, nextIndex, sourceUrl, outputExtension);
      const absolutePath = path.join(targetDir, fileName);
      const relativePath = path.posix.join(dirName, fileName);
      const bytes = Buffer.from(await response.arrayBuffer());
      await writeFile(absolutePath, bytes);
      replacements.set(candidate.url, relativePath);

      if (kind === "image") {
        downloadedImages = nextIndex;
      } else {
        downloadedVideos = nextIndex;
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error ?? "");
      log(`[x-to-markdown] Failed to download media ${candidate.url}: ${message}`);
    }
  }

  return {
    markdown: rewriteMarkdownMediaLinks(markdown, replacements),
    downloadedImages,
    downloadedVideos,
    imageDir: downloadedImages > 0 ? path.join(markdownDir, "imgs") : null,
    videoDir: downloadedVideos > 0 ? path.join(markdownDir, "videos") : null,
  };
}
