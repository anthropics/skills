import path from "node:path";
import type { MediaKind } from "./types";

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

export function normalizeContentType(raw: string | null): string {
  return raw?.split(";")[0]?.trim().toLowerCase() ?? "";
}

export function normalizeExtension(raw: string | undefined | null): string | undefined {
  if (!raw) {
    return undefined;
  }
  const trimmed = raw.replace(/^\./, "").trim().toLowerCase();
  if (!trimmed) {
    return undefined;
  }
  if (trimmed === "jpeg" || trimmed === "jpg") {
    return "jpg";
  }
  return trimmed;
}

export function resolveExtensionFromUrl(rawUrl: string): string | undefined {
  try {
    const parsed = new URL(rawUrl);
    const extFromPath = normalizeExtension(path.posix.extname(parsed.pathname));
    if (extFromPath) {
      return extFromPath;
    }
    const extFromFormat = normalizeExtension(parsed.searchParams.get("format"));
    if (extFromFormat) {
      return extFromFormat;
    }
  } catch {
    return undefined;
  }
  return undefined;
}

export function resolveExtensionFromContentType(contentType: string): string | undefined {
  return normalizeExtension(MIME_EXTENSION_MAP[contentType]);
}

export function resolveKindFromContentType(contentType: string): MediaKind | undefined {
  if (!contentType) {
    return undefined;
  }
  if (contentType.startsWith("image/")) {
    return "image";
  }
  if (contentType.startsWith("video/")) {
    return "video";
  }
  return undefined;
}

export function resolveKindFromExtension(extension: string | undefined): MediaKind | undefined {
  if (!extension) {
    return undefined;
  }
  if (IMAGE_EXTENSIONS.has(extension)) {
    return "image";
  }
  if (VIDEO_EXTENSIONS.has(extension)) {
    return "video";
  }
  return undefined;
}

export function resolveMediaKind(
  rawUrl: string,
  contentType: string,
  extension: string | undefined,
  hint?: MediaKind,
): MediaKind | undefined {
  const kindFromType = resolveKindFromContentType(contentType);
  if (kindFromType) {
    return kindFromType;
  }

  const kindFromExtension = resolveKindFromExtension(extension);
  if (kindFromExtension) {
    return kindFromExtension;
  }

  if (contentType && contentType !== "application/octet-stream") {
    return undefined;
  }

  if (hint) {
    return hint;
  }

  if (rawUrl.startsWith("data:image/")) {
    return "image";
  }

  if (rawUrl.startsWith("data:video/")) {
    return "video";
  }

  return undefined;
}

export function resolveOutputExtension(
  contentType: string,
  extension: string | undefined,
  kind: MediaKind,
): string {
  const fromMime = resolveExtensionFromContentType(contentType);
  if (fromMime) {
    return fromMime;
  }
  const normalized = normalizeExtension(extension);
  if (normalized) {
    return normalized;
  }
  return kind === "video" ? "mp4" : "jpg";
}

export function isDataUri(value: string): boolean {
  return value.startsWith("data:");
}

export function safeDecodeURIComponent(value: string): string {
  try {
    return decodeURIComponent(value);
  } catch {
    return value;
  }
}

function extractEmbeddedUrl(value: string): string | undefined {
  const encodedMatch = value.match(/https?%3A%2F%2F.+$/i)?.[0];
  if (encodedMatch) {
    const decoded = safeDecodeURIComponent(encodedMatch);
    try {
      return new URL(decoded).href;
    } catch {
      return undefined;
    }
  }

  const literalMatch = value.match(/https?:\/\/.+$/i)?.[0];
  if (!literalMatch) {
    return undefined;
  }

  try {
    return new URL(literalMatch).href;
  } catch {
    return undefined;
  }
}

export function normalizeMediaUrl(rawUrl: string): string {
  if (isDataUri(rawUrl)) {
    return rawUrl;
  }

  try {
    const parsed = new URL(rawUrl);
    const hostname = parsed.hostname.toLowerCase();

    if (hostname === "substackcdn.com" || hostname.endsWith(".substackcdn.com")) {
      const embeddedUrl = extractEmbeddedUrl(`${parsed.pathname}${parsed.search}`);
      if (embeddedUrl) {
        return embeddedUrl;
      }
    }

    return parsed.href;
  } catch {
    return rawUrl;
  }
}

export function sanitizeFileSegment(input: string): string {
  return input
    .replace(/[^a-zA-Z0-9_-]+/g, "-")
    .replace(/-+/g, "-")
    .replace(/^[-_]+|[-_]+$/g, "")
    .slice(0, 48);
}

export function resolveFileStem(rawUrl: string, extension: string, fileNameHint?: string): string {
  const hintBase = fileNameHint?.trim();
  if (hintBase) {
    const parsed = path.posix.parse(hintBase);
    const stem = parsed.name || parsed.base;
    return sanitizeFileSegment(stem);
  }

  if (isDataUri(rawUrl)) {
    return "";
  }

  try {
    const parsed = new URL(rawUrl);
    const base = path.posix.basename(parsed.pathname);
    if (!base) {
      return "";
    }
    const decodedBase = safeDecodeURIComponent(base);
    const normalizedExtension = normalizeExtension(extension);
    const stripExtension = normalizedExtension ? new RegExp(`\\.${normalizedExtension}$`, "i") : null;
    const rawStem = stripExtension ? decodedBase.replace(stripExtension, "") : decodedBase;
    return sanitizeFileSegment(rawStem);
  } catch {
    return "";
  }
}

export function buildFileName(
  kind: MediaKind,
  index: number,
  sourceUrl: string,
  extension: string,
  fileNameHint?: string,
): string {
  const stem = resolveFileStem(sourceUrl, extension, fileNameHint);
  const prefix = kind === "image" ? "img" : "video";
  const serial = String(index).padStart(3, "0");
  const suffix = stem ? `-${stem}` : "";
  return `${prefix}-${serial}${suffix}.${extension}`;
}

export function toPosixPath(value: string): string {
  return value.split(path.sep).join(path.posix.sep);
}
