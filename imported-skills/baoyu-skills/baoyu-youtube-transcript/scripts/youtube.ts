import { spawnSync } from "child_process";
import { writeFileSync } from "fs";

import { makeError, normalizeError, normalizePublishDate, shouldTryAlternateClient, shouldTryYtDlpFallback } from "./shared.ts";
import { findTranscript, parseTranscriptPayload } from "./transcript.ts";
import type {
  Chapter,
  InnerTubeClient,
  InnerTubeSession,
  LanguageMeta,
  Options,
  Snippet,
  TranscriptInfo,
  VideoMeta,
  VideoSource,
  YtDlpInfo,
  YtDlpTrack,
} from "./types.ts";

const WATCH_URL = "https://www.youtube.com/watch?v=";
const INNERTUBE_URL = "https://www.youtube.com/youtubei/v1/player";
const WATCH_PAGE_USER_AGENT =
  "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/134.0.0.0 Safari/537.36";
const DEFAULT_WEB_CLIENT_VERSION = "2.20260320.08.00";
const YT_DLP_MAX_BUFFER = 32 * 1024 * 1024;

let cachedYtDlpCommand: { command: string; args: string[]; label: string } | null | undefined;

const INNER_TUBE_CLIENTS: InnerTubeClient[] = [
  {
    id: "android",
    clientName: "ANDROID",
    clientHeaderName: "3",
    clientVersion: "20.10.38",
    userAgent:
      "com.google.android.youtube/20.10.38 (Linux; U; Android 14; en_US; Pixel 8 Pro; Build/AP1A.240405.002)",
    extraContext: {
      clientFormFactor: "SMALL_FORM_FACTOR",
      androidSdkVersion: 34,
      osName: "Android",
      osVersion: "14",
      platform: "MOBILE",
    },
  },
  {
    id: "web",
    clientName: "WEB",
    clientHeaderName: "1",
    userAgent: WATCH_PAGE_USER_AGENT,
  },
  {
    id: "ios",
    clientName: "IOS",
    clientHeaderName: "5",
    clientVersion: "20.10.4",
    userAgent:
      "com.google.ios.youtube/20.10.4 (iPhone16,2; U; CPU iOS 18_3 like Mac OS X; en_US)",
    extraContext: {
      deviceMake: "Apple",
      deviceModel: "iPhone16,2",
      osName: "iPhone",
      osVersion: "18.3.0.22D5054f",
      platform: "MOBILE",
    },
  },
];

async function fetchHtml(videoId: string): Promise<string> {
  const watchUrl = `${WATCH_URL}${videoId}&hl=en&persist_hl=1&has_verified=1&bpctr=9999999999`;
  const baseHeaders = {
    Accept: "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9",
    "Cache-Control": "no-cache",
    Pragma: "no-cache",
    "User-Agent": WATCH_PAGE_USER_AGENT,
  };
  const response = await fetch(watchUrl, { headers: baseHeaders });
  if (!response.ok) throw new Error(`HTTP ${response.status} fetching video page`);
  let html = await response.text();
  if (html.includes('action="https://consent.youtube.com/s"')) {
    const consentValue = html.match(/name="v" value="(.*?)"/);
    if (!consentValue) throw new Error("Failed to create consent cookie");
    const consentResponse = await fetch(watchUrl, {
      headers: {
        ...baseHeaders,
        Cookie: `CONSENT=YES+${consentValue[1]}`,
      },
    });
    if (!consentResponse.ok) throw new Error(`HTTP ${consentResponse.status} fetching video page (consent)`);
    html = await consentResponse.text();
  }
  return html;
}

function extractSession(html: string, videoId: string): InnerTubeSession {
  const apiKey = html.match(/"INNERTUBE_API_KEY":\s*"([a-zA-Z0-9_-]+)"/)?.[1];
  if (!apiKey) {
    if (html.includes('class="g-recaptcha"')) throw new Error(`IP blocked for ${videoId} (reCAPTCHA)`);
    throw new Error(`Cannot extract API key for ${videoId}`);
  }
  const webClientVersion =
    html.match(/"INNERTUBE_CLIENT_VERSION":\s*"([^"]+)"/)?.[1] ||
    html.match(/"clientVersion":"([^"]+)"/)?.[1] ||
    DEFAULT_WEB_CLIENT_VERSION;
  const visitorData =
    html.match(/"VISITOR_DATA":"([^"]+)"/)?.[1] ||
    html.match(/"visitorData":"([^"]+)"/)?.[1] ||
    "";
  return { apiKey, webClientVersion, visitorData };
}

function buildInnerTubeContext(client: InnerTubeClient, session: InnerTubeSession, videoId: string) {
  return {
    context: {
      client: {
        hl: "en",
        gl: "US",
        utcOffsetMinutes: 0,
        visitorData: session.visitorData,
        clientName: client.clientName,
        clientVersion: client.clientVersion || session.webClientVersion,
        ...client.extraContext,
      },
      request: { useSsl: true },
    },
    videoId,
  };
}

async function fetchInnertubeData(videoId: string, session: InnerTubeSession, client: InnerTubeClient): Promise<any> {
  const clientVersion = client.clientVersion || session.webClientVersion;
  const headers: Record<string, string> = {
    Accept: "application/json",
    "Accept-Language": "en-US,en;q=0.9",
    "Content-Type": "application/json",
    Origin: "https://www.youtube.com",
    Referer: `${WATCH_URL}${videoId}`,
    "User-Agent": client.userAgent,
    "X-YouTube-Client-Name": client.clientHeaderName || "1",
    "X-YouTube-Client-Version": clientVersion,
  };
  if (session.visitorData) headers["X-Goog-Visitor-Id"] = session.visitorData;
  const response = await fetch(`${INNERTUBE_URL}?key=${session.apiKey}&prettyPrint=false`, {
    method: "POST",
    headers,
    body: JSON.stringify(buildInnerTubeContext(client, session, videoId)),
  });
  if (response.status === 429) throw new Error(`IP blocked for ${videoId} (429)`);
  if (!response.ok) throw new Error(`HTTP ${response.status} from InnerTube API`);
  return response.json();
}

function assertPlayability(data: any, videoId: string) {
  const playabilityStatus = data?.playabilityStatus;
  if (!playabilityStatus) return;
  const status = playabilityStatus.status;
  if (status === "OK" || !status) return;
  const reason = playabilityStatus.reason || "";
  const reasonLower = reason.toLowerCase();
  if (status === "LOGIN_REQUIRED") {
    if (reasonLower.includes("bot")) throw makeError(`Request blocked for ${videoId}: bot detected`, "BOT_DETECTED");
    if (reasonLower.includes("inappropriate")) throw makeError(`Age restricted: ${videoId}`, "AGE_RESTRICTED");
  }
  if (status === "ERROR" && reasonLower.includes("unavailable")) {
    if (videoId.startsWith("http")) throw makeError("Invalid video ID: pass the ID, not the URL", "INVALID_VIDEO_ID");
    throw makeError(`Video unavailable: ${videoId}`, "VIDEO_UNAVAILABLE");
  }
  const subreasons = playabilityStatus.errorScreen?.playerErrorMessageRenderer?.subreason?.runs?.map((run: any) => run.text).join("") || "";
  throw new Error(`Video unplayable (${videoId}): ${reason} ${subreasons}`.trim());
}

function extractCaptionsJson(data: any, videoId: string): any {
  assertPlayability(data, videoId);
  const captionsJson = data?.captions?.playerCaptionsTracklistRenderer;
  if (!captionsJson || !captionsJson.captionTracks) throw makeError(`Transcripts disabled for ${videoId}`, "TRANSCRIPTS_DISABLED");
  return captionsJson;
}

function buildTranscriptList(captionsJson: any): TranscriptInfo[] {
  const translationLanguages = (captionsJson.translationLanguages || []).map((language: any) => ({
    language: language.languageName?.runs?.[0]?.text || language.languageName?.simpleText || "",
    languageCode: language.languageCode,
  }));
  return (captionsJson.captionTracks || []).map((track: any) => ({
    language: track.name?.runs?.[0]?.text || track.name?.simpleText || "",
    languageCode: track.languageCode,
    isGenerated: track.kind === "asr",
    isTranslatable: !!track.isTranslatable,
    baseUrl: track.baseUrl || "",
    translationLanguages: track.isTranslatable ? translationLanguages : [],
  }));
}

export async function fetchTranscriptSnippets(
  info: TranscriptInfo,
  translateTo?: string
): Promise<{ snippets: Snippet[]; language: string; languageCode: string }> {
  let url = info.baseUrl;
  let language = info.language;
  let languageCode = info.languageCode;
  if (translateTo) {
    if (!info.isTranslatable) throw new Error(`Transcript ${info.languageCode} is not translatable`);
    const translatedLanguage = info.translationLanguages.find((entry) => entry.languageCode === translateTo);
    if (!translatedLanguage) throw new Error(`Translation language ${translateTo} not available`);
    url += `&tlang=${translateTo}`;
    language = translatedLanguage.language;
    languageCode = translateTo;
  }
  const response = await fetch(url, {
    headers: {
      "Accept-Language": "en-US,en;q=0.9",
      "User-Agent": WATCH_PAGE_USER_AGENT,
    },
  });
  if (!response.ok) throw new Error(`HTTP ${response.status} fetching transcript`);
  return {
    snippets: parseTranscriptPayload(await response.text(), url),
    language,
    languageCode,
  };
}

function buildYtDlpVideoSource(videoId: string, info: YtDlpInfo): VideoSource {
  const transcripts = buildTranscriptListFromYtDlp(info);
  if (!transcripts.length) throw makeError(`Transcripts disabled for ${videoId}`, "TRANSCRIPTS_DISABLED");
  return { kind: "yt-dlp", info, transcripts };
}

function getRequestedLanguages(
  source: VideoSource,
  opts: Pick<Options, "languages" | "translate">
): string[] {
  return source.kind === "yt-dlp" && opts.translate ? [opts.translate] : opts.languages;
}

export async function fetchTranscriptWithFallback(
  videoId: string,
  source: VideoSource,
  opts: Pick<Options, "languages" | "translate" | "excludeGenerated" | "excludeManual">,
  fetchSnippets: (
    info: TranscriptInfo,
    translateTo?: string
  ) => Promise<{ snippets: Snippet[]; language: string; languageCode: string }> = fetchTranscriptSnippets,
  fetchFallbackSource: (videoId: string) => Promise<VideoSource> | VideoSource = (requestedVideoId) =>
    buildYtDlpVideoSource(requestedVideoId, fetchYtDlpInfo(requestedVideoId)),
  logWarning: (message: string) => void = (message) => console.error(message)
): Promise<{
  source: VideoSource;
  transcript: TranscriptInfo;
  snippets: Snippet[];
  language: string;
  languageCode: string;
}> {
  const transcript = findTranscript(
    source.transcripts,
    getRequestedLanguages(source, opts),
    opts.excludeGenerated,
    opts.excludeManual
  );
  const result = await fetchSnippets(transcript, source.kind === "yt-dlp" ? undefined : opts.translate || undefined);
  if (result.snippets.length > 0) return { source, transcript, ...result };

  if (source.kind === "yt-dlp") {
    throw makeError(`Transcript fetch returned empty snippets for ${videoId}`, "EMPTY_TRANSCRIPT");
  }

  logWarning(`Warning (${videoId}): Transcript fetch returned empty snippets. Retrying with yt-dlp fallback.`);
  const fallbackSource = await fetchFallbackSource(videoId);
  const fallbackTranscript = findTranscript(
    fallbackSource.transcripts,
    getRequestedLanguages(fallbackSource, opts),
    opts.excludeGenerated,
    opts.excludeManual
  );
  const fallbackResult = await fetchSnippets(
    fallbackTranscript,
    fallbackSource.kind === "yt-dlp" ? undefined : opts.translate || undefined
  );
  if (!fallbackResult.snippets.length) {
    throw makeError(`Transcript fetch returned empty snippets for ${videoId} after yt-dlp fallback`, "EMPTY_TRANSCRIPT");
  }
  return { source: fallbackSource, transcript: fallbackTranscript, ...fallbackResult };
}

export function detectYtDlpCommand(): { command: string; args: string[]; label: string } | null {
  if (cachedYtDlpCommand !== undefined) return cachedYtDlpCommand;
  const candidates = [
    { command: "yt-dlp", args: [], label: "yt-dlp" },
    { command: "uvx", args: ["--from", "yt-dlp", "yt-dlp"], label: "uvx --from yt-dlp yt-dlp" },
    { command: "python3", args: ["-m", "yt_dlp"], label: "python3 -m yt_dlp" },
  ];
  for (const candidate of candidates) {
    const probe = spawnSync(candidate.command, [...candidate.args, "--version"], {
      encoding: "utf8",
      maxBuffer: 1024 * 1024,
    });
    if (probe.status !== 0) continue;

    const helpProbe = spawnSync(candidate.command, [...candidate.args, "--help"], {
      encoding: "utf8",
      maxBuffer: 2 * 1024 * 1024,
    });
    const helpText = `${helpProbe.stdout || ""}\n${helpProbe.stderr || ""}`;
    const supportsRequiredFlags =
      helpProbe.status === 0 &&
      helpText.includes("--js-runtimes") &&
      helpText.includes("--remote-components");

    if (supportsRequiredFlags) {
      cachedYtDlpCommand = candidate;
      return candidate;
    }
  }
  cachedYtDlpCommand = null;
  return cachedYtDlpCommand;
}

export function selectYtDlpTrack(entries: YtDlpTrack[]): YtDlpTrack | null {
  const preferredExts = ["json3", "srv3", "srv2", "srv1", "ttml", "vtt"];
  for (const ext of preferredExts) {
    const match = entries.find((entry) => entry.url && entry.ext === ext);
    if (match) return match;
  }
  return entries.find((entry) => !!entry.url) || null;
}

export function buildTranscriptListFromYtDlp(info: YtDlpInfo): TranscriptInfo[] {
  const translationLanguages = Object.entries(info.automatic_captions || {}).map(([languageCode, entries]) => ({
    language: entries.find((entry) => entry.name)?.name || languageCode,
    languageCode,
  }));
  const manual = Object.entries(info.subtitles || {}).flatMap(([languageCode, entries]) => {
    const selected = selectYtDlpTrack(entries);
    if (!selected?.url) return [];
    return [{
      language: selected.name || languageCode,
      languageCode,
      isGenerated: false,
      isTranslatable: translationLanguages.length > 0,
      baseUrl: selected.url,
      translationLanguages,
    }];
  });
  const generated = Object.entries(info.automatic_captions || {}).flatMap(([languageCode, entries]) => {
    const selected = selectYtDlpTrack(entries);
    if (!selected?.url) return [];
    return [{
      language: selected.name || languageCode,
      languageCode,
      isGenerated: true,
      isTranslatable: translationLanguages.length > 0,
      baseUrl: selected.url,
      translationLanguages,
    }];
  });
  return [...manual, ...generated];
}

function fetchYtDlpInfo(videoId: string): YtDlpInfo {
  const command = detectYtDlpCommand();
  if (!command) {
    throw makeError(
      `Request blocked for ${videoId}: bot detected. yt-dlp fallback unavailable (install yt-dlp or uv).`,
      "YT_DLP_UNAVAILABLE"
    );
  }

  const args = [
    ...command.args,
    "-J",
    "--skip-download",
    "--js-runtimes",
    "bun",
    "--remote-components",
    "ejs:github",
  ];
  const cookiesFromBrowser = process.env.YOUTUBE_TRANSCRIPT_COOKIES_FROM_BROWSER?.trim();
  if (cookiesFromBrowser) args.push("--cookies-from-browser", cookiesFromBrowser);
  args.push(`${WATCH_URL}${videoId}`);

  const result = spawnSync(command.command, args, {
    encoding: "utf8",
    maxBuffer: YT_DLP_MAX_BUFFER,
  });
  if (result.status !== 0) {
    const stderr = (result.stderr || "").trim();
    const stdout = (result.stdout || "").trim();
    const detail = stderr || stdout || `exit ${result.status ?? "unknown"}`;
    throw makeError(`yt-dlp fallback failed for ${videoId} (${command.label}): ${detail}`, "YT_DLP_FAILED");
  }
  return JSON.parse(result.stdout);
}

async function fetchInnertubeSource(videoId: string): Promise<VideoSource> {
  const html = await fetchHtml(videoId);
  const session = extractSession(html, videoId);
  const attempts: string[] = [];
  let lastError: Error | null = null;

  for (const client of INNER_TUBE_CLIENTS) {
    try {
      const data = await fetchInnertubeData(videoId, session, client);
      const captionsJson = extractCaptionsJson(data, videoId);
      return { kind: "innertube", data, transcripts: buildTranscriptList(captionsJson) };
    } catch (error) {
      const normalized = normalizeError(error);
      attempts.push(`${client.id}: ${normalized.message}`);
      lastError = normalized;
      if (!shouldTryAlternateClient(normalized)) break;
    }
  }

  if (!lastError) throw makeError(`Unable to fetch transcript metadata for ${videoId}`, "UNKNOWN");
  if (attempts.length > 1) {
    throw makeError(`${lastError.message}. Tried clients: ${attempts.join("; ")}`, normalizeError(lastError).code);
  }
  throw lastError;
}

export async function resolveVideoSource(
  videoId: string,
  fetchPrimary: (videoId: string) => Promise<VideoSource>,
  fetchFallback: (videoId: string) => YtDlpInfo,
  logWarning: (message: string) => void = (message) => console.error(message)
): Promise<VideoSource> {
  try {
    return await fetchPrimary(videoId);
  } catch (error) {
    const normalized = normalizeError(error);
    if (!shouldTryYtDlpFallback(normalized)) throw normalized;
    logWarning(`Warning (${videoId}): ${normalized.message}. Retrying with yt-dlp fallback.`);
    return buildYtDlpVideoSource(videoId, fetchFallback(videoId));
  }
}

export async function fetchVideoSource(videoId: string): Promise<VideoSource> {
  return resolveVideoSource(videoId, fetchInnertubeSource, fetchYtDlpInfo);
}

export function parseChapters(description: string, duration: number = 0): Chapter[] {
  const raw: { title: string; start: number }[] = [];
  for (const line of description.split("\n")) {
    const match = line.trim().match(/^(?:(\d{1,2}):)?(\d{1,2}):(\d{2})\s+(.+)$/);
    if (match) {
      const hours = match[1] ? parseInt(match[1]) : 0;
      raw.push({ title: match[4].trim(), start: hours * 3600 + parseInt(match[2]) * 60 + parseInt(match[3]) });
    }
  }
  if (raw.length < 2) return [];
  return raw.map((chapter, index) => ({
    title: chapter.title,
    start: chapter.start,
    end: index < raw.length - 1 ? raw[index + 1].start : Math.max(duration, chapter.start),
  }));
}

export function getThumbnailUrls(videoId: string, data: any): string[] {
  const urls = [
    `https://i.ytimg.com/vi/${videoId}/maxresdefault.jpg`,
    `https://i.ytimg.com/vi/${videoId}/hqdefault.jpg`,
  ];
  const thumbnails = data?.videoDetails?.thumbnail?.thumbnails ||
    data?.microformat?.playerMicroformatRenderer?.thumbnail?.thumbnails ||
    [];
  if (thumbnails.length) {
    const sorted = [...thumbnails].sort((a: any, b: any) => (b.width || 0) - (a.width || 0));
    for (const thumbnail of sorted) {
      if (thumbnail.url && !urls.includes(thumbnail.url)) urls.push(thumbnail.url);
    }
  }
  return urls;
}

export function getYtDlpThumbnailUrls(videoId: string, info: YtDlpInfo): string[] {
  const urls = getThumbnailUrls(videoId, null);
  const thumbnails = Array.isArray(info.thumbnails) ? info.thumbnails : [];
  const sorted = [...thumbnails].sort((a, b) => (b?.width || 0) - (a?.width || 0));
  for (const thumbnail of sorted) {
    if (thumbnail?.url && !urls.includes(thumbnail.url)) urls.push(thumbnail.url);
  }
  if (info.thumbnail && !urls.includes(info.thumbnail)) urls.push(info.thumbnail);
  return urls;
}

export function buildVideoMeta(data: any, videoId: string, language: LanguageMeta, chapters: Chapter[]): VideoMeta {
  const videoDetails = data?.videoDetails || {};
  const microformat = data?.microformat?.playerMicroformatRenderer || {};
  return {
    videoId,
    title: videoDetails.title || microformat.title?.simpleText || "",
    channel: videoDetails.author || microformat.ownerChannelName || "",
    channelId: videoDetails.channelId || microformat.externalChannelId || "",
    description: videoDetails.shortDescription || microformat.description?.simpleText || "",
    duration: parseInt(videoDetails.lengthSeconds || "0"),
    publishDate: microformat.publishDate || microformat.uploadDate || "",
    url: `${WATCH_URL}${videoId}`,
    coverImage: "",
    thumbnailUrl: getThumbnailUrls(videoId, data)[0],
    language,
    chapters,
  };
}

export function buildVideoMetaFromYtDlp(
  info: YtDlpInfo,
  videoId: string,
  language: LanguageMeta,
  chapters: Chapter[]
): VideoMeta {
  return {
    videoId,
    title: info.title || "",
    channel: info.channel || info.uploader || "",
    channelId: info.channel_id || info.uploader_id || "",
    description: info.description || "",
    duration: Number(info.duration || 0),
    publishDate: normalizePublishDate(info.upload_date),
    url: info.webpage_url || `${WATCH_URL}${videoId}`,
    coverImage: "",
    thumbnailUrl: getYtDlpThumbnailUrls(videoId, info)[0] || "",
    language,
    chapters,
  };
}

export async function downloadCoverImage(urls: string[], outputPath: string): Promise<boolean> {
  for (const url of urls) {
    try {
      const response = await fetch(url);
      if (response.ok) {
        writeFileSync(outputPath, Buffer.from(await response.arrayBuffer()));
        return true;
      }
    } catch {}
  }
  return false;
}
