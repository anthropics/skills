import type { ExtractedDocument } from "../../extract/document";
import {
  findTweetNode,
  findTweetNodeById,
  formatMediaList,
  formatTweetAuthor,
  getTweetAuthorMetadata,
  getTweetText,
  getUser,
  isRecord,
  normalizeTitle,
  resolveBestXVideoVariantUrl,
  toHighResXImageUrl,
  toXTweet,
} from "./shared";
import type { JsonObject } from "./types";

interface ArticleMedia {
  kind: "image" | "video";
  url: string;
}

function resolveArticleMedia(mediaInfo: JsonObject): ArticleMedia | null {
  const videoUrl = resolveBestXVideoVariantUrl(mediaInfo);
  if (videoUrl) {
    return {
      kind: "video",
      url: videoUrl,
    };
  }

  const rawUrl =
    (typeof mediaInfo.original_img_url === "string" && mediaInfo.original_img_url) ||
    (typeof mediaInfo.url === "string" && mediaInfo.url) ||
    "";

  if (!rawUrl) {
    return null;
  }

  return {
    kind: "image",
    url: toHighResXImageUrl(rawUrl),
  };
}

function resolveArticleMediaUrl(mediaInfo: JsonObject): string {
  return resolveArticleMedia(mediaInfo)?.url ?? "";
}

function normalizeEntityMap(entityMap: unknown): Map<string, JsonObject> {
  const normalized = new Map<string, JsonObject>();

  if (Array.isArray(entityMap)) {
    for (const entry of entityMap) {
      if (!isRecord(entry)) {
        continue;
      }

      const key =
        typeof entry.key === "string" || typeof entry.key === "number"
          ? String(entry.key)
          : undefined;
      const value = isRecord(entry.value) ? entry.value : undefined;
      if (!key || !value) {
        continue;
      }
      normalized.set(key, value);
    }

    return normalized;
  }

  if (!isRecord(entityMap)) {
    return normalized;
  }

  for (const [key, value] of Object.entries(entityMap)) {
    if (!isRecord(value)) {
      continue;
    }
    normalized.set(key, value);
  }

  return normalized;
}

function getEntityMarkdown(entityMap: Map<string, JsonObject>, entityKey: unknown): string | null {
  const key =
    typeof entityKey === "string" || typeof entityKey === "number"
      ? String(entityKey)
      : undefined;
  if (!key) {
    return null;
  }

  const entity = entityMap.get(key);
  if (!entity || entity.type !== "MARKDOWN") {
    return null;
  }

  const data = isRecord(entity.data) ? entity.data : {};
  if (typeof data.markdown !== "string") {
    return null;
  }

  const markdown = data.markdown.trim();
  return markdown || null;
}

function getLinkUrl(entityMap: Map<string, JsonObject>, entityKey: unknown): string | null {
  const key =
    typeof entityKey === "string" || typeof entityKey === "number"
      ? String(entityKey)
      : undefined;
  if (!key) {
    return null;
  }

  const entity = entityMap.get(key);
  if (!entity || entity.type !== "LINK") {
    return null;
  }

  const data = isRecord(entity.data) ? entity.data : {};
  const candidates = [
    data.expanded_url,
    data.expandedUrl,
    data.original_url,
    data.originalUrl,
    data.url,
    data.display_url,
    data.displayUrl,
  ];

  for (const candidate of candidates) {
    if (typeof candidate === "string" && candidate.trim()) {
      return candidate.trim();
    }
  }

  return null;
}

function getTweetId(entityMap: Map<string, JsonObject>, entityKey: unknown): string | null {
  const key =
    typeof entityKey === "string" || typeof entityKey === "number"
      ? String(entityKey)
      : undefined;
  if (!key) {
    return null;
  }

  const entity = entityMap.get(key);
  if (!entity || entity.type !== "TWEET") {
    return null;
  }

  const data = isRecord(entity.data) ? entity.data : {};
  if (typeof data.tweetId !== "string") {
    return null;
  }

  return data.tweetId;
}

function buildMediaMap(articleResult: JsonObject): Map<string, ArticleMedia> {
  const mediaMap = new Map<string, ArticleMedia>();
  const mediaEntities = Array.isArray(articleResult.media_entities) ? articleResult.media_entities : [];

  for (const entity of mediaEntities) {
    if (!isRecord(entity) || typeof entity.media_id !== "string" || !isRecord(entity.media_info)) {
      continue;
    }

    const media = resolveArticleMedia(entity.media_info);
    if (media) {
      mediaMap.set(entity.media_id, media);
    }
  }

  const coverMedia = isRecord(articleResult.cover_media) ? articleResult.cover_media : null;
  if (coverMedia && typeof coverMedia.media_id === "string" && isRecord(coverMedia.media_info)) {
    const media = resolveArticleMedia(coverMedia.media_info);
    if (media) {
      mediaMap.set(coverMedia.media_id, media);
    }
  }

  return mediaMap;
}

function getMediaMarkdown(
  entityMap: Map<string, JsonObject>,
  entityKey: unknown,
  mediaMap: Map<string, ArticleMedia>,
): string[] {
  const key =
    typeof entityKey === "string" || typeof entityKey === "number"
      ? String(entityKey)
      : undefined;
  if (!key) {
    return [];
  }

  const entity = entityMap.get(key);
  if (!entity || entity.type !== "MEDIA") {
    return [];
  }

  const data = isRecord(entity.data) ? entity.data : {};
  const mediaItems = Array.isArray(data.mediaItems) ? data.mediaItems : [];
  const media: ArticleMedia[] = [];

  for (const item of mediaItems) {
    if (!isRecord(item) || typeof item.mediaId !== "string") {
      continue;
    }
    const mediaItem = mediaMap.get(item.mediaId);
    if (mediaItem && !media.some((value) => value.url === mediaItem.url)) {
      media.push(mediaItem);
    }
  }

  return media.map((item) => item.kind === "image" ? `![](${item.url})` : `[video](${item.url})`);
}

function resolveTweetMarkdown(payloads: unknown[], tweetId: string, pageUrl: string): string | null {
  for (const payload of payloads) {
    const tweet = findTweetNodeById(payload, tweetId);
    if (!tweet) {
      continue;
    }

    const xTweet = toXTweet(tweet, pageUrl);
    const author = formatTweetAuthor(xTweet) ?? xTweet.url;
    const lines = [`> ${author}`, ...xTweet.text.split("\n").map((line) => `> ${line}`)];

    const media = formatMediaList(xTweet.media).map((line) =>
      line.startsWith("photo: ") ? `> ![](${line.slice("photo: ".length)})` : `> - ${line}`,
    );

    const parts = [lines.join("\n")];
    if (media.length > 0) {
      parts.push([">", ...media].join("\n"));
    }
    parts.push(`> ${xTweet.url}`);

    return parts.join("\n").trim();
  }

  return `> Embedded tweet: https://x.com/i/status/${tweetId}`;
}

function replaceLinkEntities(text: string, block: JsonObject, entityMap: Map<string, JsonObject>): string {
  const entityRanges = Array.isArray(block.entityRanges) ? block.entityRanges : [];
  const replacements = entityRanges
    .filter((range): range is JsonObject => isRecord(range))
    .map((range) => {
      const offset = typeof range.offset === "number" ? range.offset : -1;
      const length = typeof range.length === "number" ? range.length : -1;
      const url = getLinkUrl(entityMap, range.key);
      return { offset, length, url };
    })
    .filter((range) => range.offset >= 0 && range.length > 0 && range.url)
    .sort((left, right) => right.offset - left.offset);

  let next = text;
  for (const replacement of replacements) {
    next =
      next.slice(0, replacement.offset) +
      replacement.url +
      next.slice(replacement.offset + replacement.length);
  }
  return next;
}

function renderAtomicBlock(
  block: JsonObject,
  entityMap: Map<string, JsonObject>,
  mediaMap: Map<string, ArticleMedia>,
  payloads: unknown[],
  pageUrl: string,
): string | null {
  const entityRanges = Array.isArray(block.entityRanges) ? block.entityRanges : [];
  const parts: string[] = [];

  for (const range of entityRanges) {
    if (!isRecord(range)) {
      continue;
    }

    const markdown = getEntityMarkdown(entityMap, range.key);
    if (markdown) {
      parts.push(markdown);
      continue;
    }

    const mediaMarkdown = getMediaMarkdown(entityMap, range.key, mediaMap);
    if (mediaMarkdown.length > 0) {
      parts.push(mediaMarkdown.join("\n\n"));
      continue;
    }

    const tweetId = getTweetId(entityMap, range.key);
    if (tweetId) {
      const tweetMarkdown = resolveTweetMarkdown(payloads, tweetId, pageUrl);
      if (tweetMarkdown) {
        parts.push(tweetMarkdown);
      }
    }
  }

  if (parts.length === 0) {
    return null;
  }

  return parts.join("\n\n");
}

function renderArticleBlocks(
  blocks: unknown[],
  entityMap: Map<string, JsonObject>,
  mediaMap: Map<string, ArticleMedia>,
  payloads: unknown[],
  pageUrl: string,
): string {
  const parts: string[] = [];
  let orderedCounter = 0;

  for (const block of blocks) {
    if (!isRecord(block)) {
      continue;
    }

    const blockType = typeof block.type === "string" ? block.type : "unstyled";
    const rawText = typeof block.text === "string" ? block.text : "";
    const text = replaceLinkEntities(rawText, block, entityMap).trim();
    if (!text && blockType !== "atomic") {
      continue;
    }

    if (blockType !== "ordered-list-item") {
      orderedCounter = 0;
    }

    switch (blockType) {
      case "header-one":
        parts.push(`# ${text}`);
        break;
      case "header-two":
        parts.push(`## ${text}`);
        break;
      case "header-three":
        parts.push(`### ${text}`);
        break;
      case "blockquote":
        parts.push(`> ${text}`);
        break;
      case "unordered-list-item":
        parts.push(`- ${text}`);
        break;
      case "ordered-list-item":
        orderedCounter += 1;
        parts.push(`${orderedCounter}. ${text}`);
        break;
      case "code-block":
        parts.push(`\`\`\`\n${text}\n\`\`\``);
        break;
      case "atomic": {
        const markdown = renderAtomicBlock(block, entityMap, mediaMap, payloads, pageUrl);
        if (markdown) {
          parts.push(markdown);
        }
        break;
      }
      default:
        parts.push(text);
        break;
    }
  }

  return parts.join("\n\n").trim();
}

function getArticleResult(tweet: JsonObject): JsonObject | null {
  if (
    isRecord(tweet.article) &&
    isRecord(tweet.article.article_results) &&
    isRecord(tweet.article.article_results.result)
  ) {
    return tweet.article.article_results.result as JsonObject;
  }
  return null;
}

function extractSummary(markdown: string): string | undefined {
  const segments = markdown
    .split(/\n\n+/)
    .map((segment) => segment.trim())
    .filter(Boolean);

  const preferred = segments.find((segment) => !/^(#|>|- |\d+\. |\`\`\`)/.test(segment));
  return preferred?.slice(0, 220);
}

export function extractArticleDocumentFromPayload(
  payload: unknown,
  statusId: string,
  pageUrl: string,
  payloads: unknown[] = [payload],
): ExtractedDocument | null {
  const tweet = findTweetNode(payload, statusId);
  if (!tweet) {
    return null;
  }

  const articleResult = getArticleResult(tweet);
  if (!articleResult) {
    return null;
  }

  const title = typeof articleResult.title === "string" ? articleResult.title.trim() : undefined;
  const contentState = isRecord(articleResult.content_state) ? articleResult.content_state : {};
  const blocks = Array.isArray(contentState.blocks) ? contentState.blocks : [];
  const entityMap = normalizeEntityMap(contentState.entityMap);
  const mediaMap = buildMediaMap(articleResult);
  const richMarkdown = renderArticleBlocks(blocks, entityMap, mediaMap, payloads, pageUrl);
  const plainText = typeof articleResult.plain_text === "string" ? articleResult.plain_text.trim() : "";
  const markdown = richMarkdown || plainText || getTweetText(tweet);
  if (!markdown) {
    return null;
  }

  const xTweet = toXTweet(tweet, pageUrl);
  const user = getUser(tweet);
  const coverMedia = isRecord(articleResult.cover_media) ? articleResult.cover_media : null;
  const coverMediaInfo = coverMedia && isRecord(coverMedia.media_info) ? coverMedia.media_info : null;
  const coverImage = coverMediaInfo ? resolveArticleMediaUrl(coverMediaInfo) || undefined : undefined;

  return {
    url: pageUrl,
    canonicalUrl: xTweet.url,
    title: title || normalizeTitle(xTweet.text, "X Article"),
    author: formatTweetAuthor(xTweet),
    siteName: "X",
    publishedAt: xTweet.createdAt,
    summary: extractSummary(markdown) || xTweet.text.slice(0, 200) || undefined,
    adapter: "x",
    metadata: {
      kind: "x/article",
      tweetId: xTweet.id,
      coverImage,
      authorName: xTweet.authorName ?? user.name,
      authorUsername: xTweet.author ?? user.screenName,
      authorUrl: (xTweet.author ?? user.screenName) ? `https://x.com/${xTweet.author ?? user.screenName}` : undefined,
      ...getTweetAuthorMetadata(xTweet),
    },
    content: [{ type: "markdown", markdown }],
  };
}
