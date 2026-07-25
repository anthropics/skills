import type { TranscriptError } from "./types.ts";

export function extractVideoId(input: string): string {
  input = input.replace(/\\/g, "").trim();
  const patterns = [
    /(?:youtube\.com\/watch\?.*v=|youtu\.be\/|youtube\.com\/embed\/|youtube\.com\/v\/|youtube\.com\/shorts\/)([a-zA-Z0-9_-]{11})/,
    /^([a-zA-Z0-9_-]{11})$/,
  ];
  for (const pattern of patterns) {
    const match = input.match(pattern);
    if (match) return match[1];
  }
  return input;
}

export function slugify(value: string): string {
  return value
    .toLowerCase()
    .replace(/[^\w\s-]/g, "")
    .replace(/\s+/g, "-")
    .replace(/-+/g, "-")
    .replace(/^-|-$/g, "") || "untitled";
}

export function htmlUnescape(value: string): string {
  return value
    .replace(/&amp;/g, "&")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'")
    .replace(/&#x27;/g, "'")
    .replace(/&#x2F;/g, "/")
    .replace(/&apos;/g, "'")
    .replace(/&#(\d+);/g, (_, n) => String.fromCharCode(parseInt(n)))
    .replace(/&#x([0-9a-fA-F]+);/g, (_, n) => String.fromCharCode(parseInt(n, 16)));
}

export function stripTags(value: string): string {
  return value.replace(/<[^>]*>/g, "");
}

export function makeError(message: string, code?: string): Error {
  const error = new Error(message) as TranscriptError;
  if (code) error.code = code;
  return error;
}

export function normalizeError(error: unknown): TranscriptError {
  if (error instanceof Error) {
    const known = error as TranscriptError;
    if (known.code) return known;
    const message = known.message || String(error);
    const lower = message.toLowerCase();
    if (lower.includes("bot detected")) known.code = "BOT_DETECTED";
    else if (lower.includes("age restricted")) known.code = "AGE_RESTRICTED";
    else if (lower.includes("video unavailable")) known.code = "VIDEO_UNAVAILABLE";
    else if (lower.includes("transcripts disabled")) known.code = "TRANSCRIPTS_DISABLED";
    else if (lower.includes("no transcript found")) known.code = "NO_TRANSCRIPT";
    else if (lower.includes("invalid video id")) known.code = "INVALID_VIDEO_ID";
    else if (lower.includes("ip blocked") || lower.includes("recaptcha") || lower.includes("http 429")) known.code = "IP_BLOCKED";
    else if (lower.includes("cannot extract api key")) known.code = "PAGE_FETCH_FAILED";
    else if (lower.includes("innertube api") || lower.includes("http 403")) known.code = "INNERTUBE_REJECTED";
    else if (lower.includes("yt-dlp fallback failed")) known.code = "YT_DLP_FAILED";
    return known;
  }
  return makeError(String(error), "UNKNOWN") as TranscriptError;
}

export function shouldTryAlternateClient(error: unknown): boolean {
  const code = normalizeError(error).code;
  return code === "BOT_DETECTED" || code === "IP_BLOCKED" || code === "INNERTUBE_REJECTED" || code === "AGE_RESTRICTED" || code === "VIDEO_UNAVAILABLE";
}

export function shouldTryYtDlpFallback(error: unknown): boolean {
  const code = normalizeError(error).code;
  return code === "BOT_DETECTED" || code === "IP_BLOCKED" || code === "INNERTUBE_REJECTED" || code === "PAGE_FETCH_FAILED" || code === "AGE_RESTRICTED" || code === "VIDEO_UNAVAILABLE";
}

export function normalizePublishDate(uploadDate?: string): string {
  if (!uploadDate || !/^\d{8}$/.test(uploadDate)) return uploadDate || "";
  return `${uploadDate.slice(0, 4)}-${uploadDate.slice(4, 6)}-${uploadDate.slice(6, 8)}`;
}
