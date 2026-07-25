import type { Logger } from "../utils/logger";

export type MediaKind = "image" | "video";

export interface MediaAsset {
  url: string;
  kind?: MediaKind;
  role?: "cover" | "inline" | "attachment";
  alt?: string;
  fileNameHint?: string;
  headers?: Record<string, string>;
}

export interface MediaReplacement {
  url: string;
  localPath: string;
  absolutePath: string;
  kind: MediaKind;
}

export interface MediaDownloadRequest {
  media: MediaAsset[];
  outputPath: string;
  mediaDir?: string;
  log: Logger;
}

export interface MediaDownloadResult {
  replacements: MediaReplacement[];
  downloadedImages: number;
  downloadedVideos: number;
  imageDir: string | null;
  videoDir: string | null;
}
