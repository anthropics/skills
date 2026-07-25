import path from "node:path";
import type { NetworkEntry } from "../../browser/network-journal";
import type { XMedia, XQuotedTweet, XTweet, XUser, JsonObject } from "./types";

const X_IMAGE_EXTENSIONS = new Set(["jpg", "jpeg", "png", "webp", "gif", "bmp", "avif"]);

function emptyObject(): JsonObject {
  return {};
}

export function isRecord(value: unknown): value is JsonObject {
  return Boolean(value) && typeof value === "object" && !Array.isArray(value);
}

export function walk(value: unknown, visitor: (node: unknown) => boolean | void): boolean {
  if (visitor(value)) {
    return true;
  }

  if (Array.isArray(value)) {
    for (const item of value) {
      if (walk(item, visitor)) {
        return true;
      }
    }
    return false;
  }

  if (isRecord(value)) {
    for (const child of Object.values(value)) {
      if (walk(child, visitor)) {
        return true;
      }
    }
  }

  return false;
}

function hasTweetText(node: JsonObject): boolean {
  const legacy = isRecord(node.legacy) ? node.legacy : emptyObject();
  return (
    typeof legacy.full_text === "string" ||
    typeof getNoteTweetText(node) === "string"
  );
}

export function findTweetNodeById(payload: unknown, tweetId: string): JsonObject | null {
  let match: JsonObject | null = null;

  walk(payload, (node) => {
    if (!isRecord(node) || typeof node.rest_id !== "string" || !isRecord(node.legacy)) {
      return false;
    }

    if (!hasTweetText(node)) {
      return false;
    }

    if (node.rest_id === tweetId) {
      match = node;
      return true;
    }

    return false;
  });

  return match;
}

export function findTweetNode(payload: unknown, statusId: string): JsonObject | null {
  let firstMatch: JsonObject | null = null;
  const exactMatch = findTweetNodeById(payload, statusId);
  if (exactMatch) {
    return exactMatch;
  }

  walk(payload, (node) => {
    if (!isRecord(node) || typeof node.rest_id !== "string" || !isRecord(node.legacy)) {
      return false;
    }
    if (!hasTweetText(node)) {
      return false;
    }
    if (!firstMatch) {
      firstMatch = node;
    }
    return false;
  });

  return firstMatch;
}

export function getLegacy(tweet: JsonObject): JsonObject {
  return isRecord(tweet.legacy) ? tweet.legacy : emptyObject();
}

export function unwrapTweetResult(node: unknown): JsonObject | null {
  if (!isRecord(node)) {
    return null;
  }

  if (node.__typename === "TweetWithVisibilityResults" && isRecord(node.tweet)) {
    return unwrapTweetResult(node.tweet);
  }

  const tweet = isRecord(node.tweet) ? (node.tweet as JsonObject) : node;
  if (typeof tweet.rest_id !== "string" || !isRecord(tweet.legacy)) {
    return null;
  }

  return tweet;
}

export function getUser(tweet: JsonObject): XUser {
  const result =
    isRecord(tweet.core) &&
    isRecord(tweet.core.user_results) &&
    isRecord(tweet.core.user_results.result)
      ? (tweet.core.user_results.result as JsonObject)
      : emptyObject();
  const legacy = isRecord(result.legacy) ? result.legacy : emptyObject();
  const core = isRecord(result.core) ? result.core : emptyObject();
  return {
    name:
      (typeof legacy.name === "string" ? legacy.name : undefined) ??
      (typeof core.name === "string" ? core.name : undefined),
    screenName:
      (typeof legacy.screen_name === "string" ? legacy.screen_name : undefined) ??
      (typeof core.screen_name === "string" ? core.screen_name : undefined),
  };
}

function getNoteTweetResult(tweet: JsonObject): JsonObject | null {
  if (
    !isRecord(tweet.note_tweet) ||
    !isRecord(tweet.note_tweet.note_tweet_results) ||
    !isRecord(tweet.note_tweet.note_tweet_results.result)
  ) {
    return null;
  }

  return tweet.note_tweet.note_tweet_results.result as JsonObject;
}

function getNoteTweetText(tweet: JsonObject): string | undefined {
  const noteTweet = getNoteTweetResult(tweet);
  return typeof noteTweet?.text === "string" ? noteTweet.text : undefined;
}

interface TweetUrlEntity {
  url: string;
  expandedUrl?: string;
  displayUrl?: string;
}

function collectTweetUrlEntities(values: unknown[]): TweetUrlEntity[] {
  return values.reduce<TweetUrlEntity[]>((entities, value) => {
      if (!isRecord(value) || typeof value.url !== "string" || !value.url) {
        return entities;
      }

      entities.push({
        url: value.url,
        expandedUrl: typeof value.expanded_url === "string" ? value.expanded_url : undefined,
        displayUrl: typeof value.display_url === "string" ? value.display_url : undefined,
      });

      return entities;
    }, []);
}

function getTweetUrlEntities(tweet: JsonObject): TweetUrlEntity[] {
  const noteTweet = getNoteTweetResult(tweet);
  const noteTweetEntitySet = noteTweet && isRecord(noteTweet.entity_set) ? noteTweet.entity_set : emptyObject();
  const noteTweetUrls = collectTweetUrlEntities(Array.isArray(noteTweetEntitySet.urls) ? noteTweetEntitySet.urls : []);

  const legacy = getLegacy(tweet);
  const legacyEntities = isRecord(legacy.entities) ? legacy.entities : emptyObject();
  const legacyUrls = collectTweetUrlEntities(Array.isArray(legacyEntities.urls) ? legacyEntities.urls : []);

  const seen = new Set<string>();
  return [...noteTweetUrls, ...legacyUrls].filter((value) => {
    if (seen.has(value.url)) {
      return false;
    }
    seen.add(value.url);
    return true;
  });
}

export function getTweetText(tweet: JsonObject): string {
  const legacy = getLegacy(tweet);
  let text =
    getNoteTweetText(tweet) ?? (typeof legacy.full_text === "string" ? legacy.full_text : "");

  for (const value of getTweetUrlEntities(tweet)) {
    const replacement =
      (typeof value.expandedUrl === "string" && value.expandedUrl) ||
      (typeof value.displayUrl === "string" && value.displayUrl) ||
      value.url;
    text = text.replaceAll(value.url, replacement);
  }

  const extendedEntities = isRecord(legacy.extended_entities) ? legacy.extended_entities : emptyObject();
  const media = Array.isArray(extendedEntities.media) ? extendedEntities.media : [];
  for (const value of media) {
    if (isRecord(value) && typeof value.url === "string") {
      text = text.replaceAll(value.url, "").trim();
    }
  }

  return text.replace(/\n{3,}/g, "\n\n").trim();
}

function normalizeXImageExtension(raw: string | undefined | null): string | undefined {
  if (!raw) {
    return undefined;
  }

  const normalized = raw.replace(/^\./, "").trim().toLowerCase();
  if (!normalized) {
    return undefined;
  }

  return normalized === "jpeg" ? "jpg" : normalized;
}

export function toHighResXImageUrl(rawUrl: string): string {
  try {
    const parsed = new URL(rawUrl);
    if (parsed.hostname.toLowerCase() !== "pbs.twimg.com") {
      return rawUrl;
    }

    const pathExtension = normalizeXImageExtension(path.posix.extname(parsed.pathname));
    const format = normalizeXImageExtension(parsed.searchParams.get("format")) ?? pathExtension;
    if (!format || !X_IMAGE_EXTENSIONS.has(format)) {
      return rawUrl;
    }

    if (pathExtension) {
      parsed.pathname = parsed.pathname.replace(new RegExp(`\\.${pathExtension}$`, "i"), "");
    }

    parsed.searchParams.set("format", format);
    parsed.searchParams.set("name", "4096x4096");
    return parsed.toString();
  } catch {
    return rawUrl;
  }
}

function getVideoVariantBitrate(variant: JsonObject): number {
  const value = variant.bitrate ?? variant.bit_rate;
  return typeof value === "number" && Number.isFinite(value) ? value : 0;
}

function getVideoVariantContentType(variant: JsonObject): string {
  const value = variant.content_type ?? variant.contentType;
  return typeof value === "string" ? value.toLowerCase() : "";
}

export function resolveBestXVideoVariantUrl(mediaInfo: unknown): string | undefined {
  if (!isRecord(mediaInfo)) {
    return undefined;
  }

  const variantsSource =
    Array.isArray(mediaInfo.variants)
      ? mediaInfo.variants
      : isRecord(mediaInfo.video_info) && Array.isArray(mediaInfo.video_info.variants)
        ? mediaInfo.video_info.variants
        : [];

  const variants = variantsSource
    .filter(
      (variant): variant is JsonObject =>
        isRecord(variant) && typeof variant.url === "string" && variant.url.length > 0,
    )
    .filter((variant) => getVideoVariantContentType(variant) === "video/mp4")
    .sort((left, right) => getVideoVariantBitrate(right) - getVideoVariantBitrate(left));

  return typeof variants[0]?.url === "string" ? variants[0].url : undefined;
}

export function getTweetMedia(tweet: JsonObject): XMedia[] {
  const legacy = getLegacy(tweet);
  const extendedEntities = isRecord(legacy.extended_entities) ? legacy.extended_entities : emptyObject();
  const media = Array.isArray(extendedEntities.media) ? extendedEntities.media : [];

  return media
    .map((value) => {
      if (!isRecord(value) || typeof value.type !== "string") {
        return null;
      }
      if (value.type === "photo" && typeof value.media_url_https === "string") {
        return {
          type: value.type,
          url: toHighResXImageUrl(value.media_url_https),
          alt: typeof value.ext_alt_text === "string" ? value.ext_alt_text : undefined,
        };
      }
      if (value.type === "video" || value.type === "animated_gif") {
        const videoUrl = resolveBestXVideoVariantUrl(value);
        if (!videoUrl) {
          return null;
        }
        return {
          type: value.type,
          url: videoUrl,
        };
      }
      return null;
    })
    .filter((value): value is XMedia => value !== null);
}

export function getTweetUrl(tweet: JsonObject, fallbackUrl: string): string {
  const user = getUser(tweet);
  const fallbackScreenName = extractScreenNameFromUrl(fallbackUrl);
  const id = typeof tweet.rest_id === "string" ? tweet.rest_id : "";
  const screenName = user.screenName ?? fallbackScreenName;
  if (screenName && id) {
    return `https://x.com/${screenName}/status/${id}`;
  }
  return fallbackUrl;
}

export function getQuotedTweet(tweet: JsonObject, fallbackUrl: string): XQuotedTweet | undefined {
  const quoted = unwrapTweetResult(
    isRecord(tweet.quoted_status_result) ? tweet.quoted_status_result.result : null,
  );
  if (!quoted) {
    return undefined;
  }

  const user = getUser(quoted);
  return {
    id: typeof quoted.rest_id === "string" ? quoted.rest_id : "",
    author: user.screenName,
    authorName: user.name,
    text: getTweetText(quoted),
    url: getTweetUrl(quoted, fallbackUrl),
    media: getTweetMedia(quoted),
  };
}

export function extractScreenNameFromUrl(url: string): string | undefined {
  try {
    const parsed = new URL(url);
    const match = parsed.pathname.match(/^\/([^/]+)\/(?:status|article)\//);
    if (!match) {
      return undefined;
    }
    if (match[1] === "i") {
      return undefined;
    }
    return match[1];
  } catch {
    return undefined;
  }
}

export function toXTweet(tweet: JsonObject, fallbackUrl: string): XTweet {
  const legacy = getLegacy(tweet);
  const user = getUser(tweet);
  const fallbackScreenName = extractScreenNameFromUrl(fallbackUrl);
  const screenName = user.screenName ?? fallbackScreenName;
  return {
    id: typeof tweet.rest_id === "string" ? tweet.rest_id : "",
    author: screenName,
    authorName: user.name,
    text: getTweetText(tweet),
    likes: typeof legacy.favorite_count === "number" ? legacy.favorite_count : 0,
    retweets: typeof legacy.retweet_count === "number" ? legacy.retweet_count : 0,
    replies: typeof legacy.reply_count === "number" ? legacy.reply_count : 0,
    createdAt: typeof legacy.created_at === "string" ? legacy.created_at : undefined,
    inReplyTo: typeof legacy.in_reply_to_status_id_str === "string" ? legacy.in_reply_to_status_id_str : undefined,
    url: getTweetUrl(tweet, fallbackUrl),
    media: getTweetMedia(tweet),
    quotedTweet: getQuotedTweet(tweet, fallbackUrl),
  };
}

export function normalizeTitle(text: string, fallback: string): string {
  const firstLine = text.split("\n")[0]?.trim();
  if (!firstLine) {
    return fallback;
  }
  return firstLine.slice(0, 120);
}

export function formatTweetAuthor(tweet: XTweet): string | undefined {
  if (tweet.author && tweet.authorName) {
    return `${tweet.authorName} (@${tweet.author})`;
  }
  if (tweet.author) {
    return `@${tweet.author}`;
  }
  return tweet.authorName;
}

export function getTweetAuthorMetadata(tweet: XTweet): Record<string, unknown> {
  return {
    authorName: tweet.authorName,
    authorUsername: tweet.author,
    authorUrl: tweet.author ? `https://x.com/${tweet.author}` : undefined,
  };
}

export function formatMediaList(media: XMedia[]): string[] {
  return media.map((item) => {
    if (item.type === "photo") {
      return `photo: ${item.url}`;
    }
    return `${item.type}: ${item.url}`;
  });
}

export function filterXGraphQlEntries(entries: NetworkEntry[]): NetworkEntry[] {
  return entries.filter((entry) => entry.url.includes("/graphql/"));
}
