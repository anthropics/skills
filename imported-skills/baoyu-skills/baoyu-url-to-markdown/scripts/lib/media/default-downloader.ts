import path from "node:path";
import { mkdir, writeFile } from "node:fs/promises";
import {
  buildFileName,
  isDataUri,
  normalizeContentType,
  normalizeMediaUrl,
  resolveExtensionFromContentType,
  resolveExtensionFromUrl,
  resolveMediaKind,
  resolveOutputExtension,
  toPosixPath,
} from "./media-utils";
import type { MediaAsset, MediaDownloadRequest, MediaDownloadResult, MediaKind } from "./types";

const DOWNLOAD_USER_AGENT =
  "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/130.0.0.0 Safari/537.36";

function parseBase64DataUri(rawUrl: string): { contentType: string; bytes: Buffer } | null {
  const match = rawUrl.match(/^data:([^;,]+);base64,([A-Za-z0-9+/=\s]+)$/i);
  if (!match?.[1] || !match[2]) {
    return null;
  }

  const contentType = normalizeContentType(match[1]);
  if (!contentType) {
    return null;
  }

  try {
    const bytes = Buffer.from(match[2].replace(/\s+/g, ""), "base64");
    if (bytes.length === 0) {
      return null;
    }
    return { contentType, bytes };
  } catch {
    return null;
  }
}

function dedupeMedia(media: MediaAsset[]): MediaAsset[] {
  const deduped: MediaAsset[] = [];
  const seen = new Set<string>();
  for (const item of media) {
    const normalizedUrl = normalizeMediaUrl(item.url);
    if (!normalizedUrl || seen.has(normalizedUrl)) {
      continue;
    }
    seen.add(normalizedUrl);
    deduped.push({
      ...item,
      url: normalizedUrl,
    });
  }
  return deduped;
}

function toRelativePath(fromDir: string, absoluteTarget: string): string {
  const relative = path.relative(fromDir, absoluteTarget) || path.basename(absoluteTarget);
  return toPosixPath(relative);
}

export async function downloadMediaAssets(
  request: MediaDownloadRequest,
): Promise<MediaDownloadResult> {
  const dedupedMedia = dedupeMedia(request.media);
  const absoluteOutputPath = path.resolve(request.outputPath);
  const markdownDir = path.dirname(absoluteOutputPath);
  const baseDir = request.mediaDir ? path.resolve(request.mediaDir) : markdownDir;
  const replacements: MediaDownloadResult["replacements"] = [];

  let downloadedImages = 0;
  let downloadedVideos = 0;

  for (const asset of dedupedMedia) {
    try {
      let sourceUrl = normalizeMediaUrl(asset.url);
      let contentType = "";
      let extension: string | undefined;
      let kind: MediaKind | undefined;
      let bytes: Buffer | null = null;

      if (isDataUri(asset.url)) {
        const parsed = parseBase64DataUri(asset.url);
        if (!parsed) {
          request.log.warn(`Skipping unsupported embedded media: ${asset.url.slice(0, 32)}...`);
          continue;
        }

        contentType = parsed.contentType;
        extension =
          resolveExtensionFromContentType(contentType) ??
          resolveExtensionFromUrl(asset.fileNameHint ?? "");
        kind = resolveMediaKind(sourceUrl, contentType, extension, asset.kind);
        bytes = parsed.bytes;
      } else {
        const response = await fetch(sourceUrl, {
          method: "GET",
          redirect: "follow",
          headers: {
            "user-agent": DOWNLOAD_USER_AGENT,
            ...(asset.headers ?? {}),
          },
        });

        if (!response.ok) {
          request.log.warn(`Skipping media (${response.status}): ${asset.url}`);
          continue;
        }

        sourceUrl = normalizeMediaUrl(response.url || sourceUrl);
        contentType = normalizeContentType(response.headers.get("content-type"));
        extension =
          resolveExtensionFromUrl(sourceUrl) ??
          resolveExtensionFromUrl(asset.url) ??
          resolveExtensionFromUrl(asset.fileNameHint ?? "");
        kind = resolveMediaKind(sourceUrl, contentType, extension, asset.kind);
        bytes = Buffer.from(await response.arrayBuffer());
      }

      if (!kind || !bytes) {
        request.log.debug(`Skipping media with unresolved kind: ${asset.url}`);
        continue;
      }

      const outputExtension = resolveOutputExtension(contentType, extension, kind);
      const nextIndex = kind === "image" ? downloadedImages + 1 : downloadedVideos + 1;
      const dirName = kind === "image" ? "imgs" : "videos";
      const targetDir = path.join(baseDir, dirName);
      await mkdir(targetDir, { recursive: true });

      const fileName = buildFileName(kind, nextIndex, sourceUrl, outputExtension, asset.fileNameHint);
      const absolutePath = path.join(targetDir, fileName);
      await writeFile(absolutePath, bytes);

      replacements.push({
        url: asset.url,
        localPath: toRelativePath(markdownDir, absolutePath),
        absolutePath,
        kind,
      });

      if (kind === "image") {
        downloadedImages = nextIndex;
      } else {
        downloadedVideos = nextIndex;
      }
    } catch (error) {
      const message = error instanceof Error ? error.message : String(error);
      request.log.warn(`Failed to download media ${asset.url}: ${message}`);
    }
  }

  return {
    replacements,
    downloadedImages,
    downloadedVideos,
    imageDir: downloadedImages > 0 ? path.join(baseDir, "imgs") : null,
    videoDir: downloadedVideos > 0 ? path.join(baseDir, "videos") : null,
  };
}
