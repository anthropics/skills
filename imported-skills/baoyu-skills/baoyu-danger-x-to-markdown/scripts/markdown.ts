import type {
  ArticleBlock,
  ArticleContentState,
  ArticleEntity,
  ArticleEntityMapEntry,
  ArticleMediaInfo,
} from "./types.js";

export type ReferencedTweetInfo = {
  id: string;
  url: string;
  authorName?: string;
  authorUsername?: string;
  text?: string;
};

export type FormatArticleOptions = {
  referencedTweets?: Map<string, ReferencedTweetInfo>;
};

type ResolvedMediaAsset =
  | {
      kind: "image";
      url: string;
    }
  | {
      kind: "video";
      url: string;
      posterUrl?: string;
    };

function coerceArticleEntity(value: unknown): ArticleEntity | null {
  if (!value || typeof value !== "object") return null;
  const candidate = value as ArticleEntity;
  if (
    typeof candidate.title === "string" ||
    typeof candidate.plain_text === "string" ||
    typeof candidate.preview_text === "string" ||
    candidate.content_state
  ) {
    return candidate;
  }
  return null;
}

function escapeMarkdownAlt(text: string): string {
  return text.replace(/[\[\]]/g, "\\$&");
}

function normalizeCaption(caption?: string): string {
  const trimmed = caption?.trim();
  if (!trimmed) return "";
  return trimmed.replace(/\s+/g, " ");
}

function summarizeTweetText(text?: string): string {
  const trimmed = text?.trim();
  if (!trimmed) return "";
  const normalized = trimmed
    .split(/\r?\n+/)
    .map((line) => line.trim())
    .filter(Boolean)
    .join(" ");
  if (normalized.length <= 280) return normalized;
  return `${normalized.slice(0, 277)}...`;
}

function buildTweetUrl(tweetId?: string, username?: string): string | null {
  if (!tweetId) return null;
  if (username) {
    return `https://x.com/${username}/status/${tweetId}`;
  }
  return `https://x.com/i/web/status/${tweetId}`;
}

type EntityLookup = {
  byIndex: Map<number, ArticleEntityMapEntry>;
  byLogicalKey: Map<number, ArticleEntityMapEntry>;
};

function buildEntityLookup(
  entityMap: ArticleContentState["entityMap"] | undefined
): EntityLookup {
  const lookup: EntityLookup = {
    byIndex: new Map<number, ArticleEntityMapEntry>(),
    byLogicalKey: new Map<number, ArticleEntityMapEntry>(),
  };

  if (!entityMap) return lookup;

  for (const [idx, entry] of Object.entries(entityMap)) {
    const idxNum = Number(idx);
    if (Number.isFinite(idxNum)) {
      lookup.byIndex.set(idxNum, entry);
    }

    const logicalKey = parseInt(entry?.key ?? "", 10);
    if (Number.isFinite(logicalKey) && !lookup.byLogicalKey.has(logicalKey)) {
      lookup.byLogicalKey.set(logicalKey, entry);
    }
  }

  return lookup;
}

function resolveEntityEntry(
  entityKey: number | undefined,
  entityMap: ArticleContentState["entityMap"] | undefined,
  lookup: EntityLookup
): ArticleEntityMapEntry | undefined {
  if (entityKey === undefined) return undefined;

  const byLogicalKey = lookup.byLogicalKey.get(entityKey);
  if (byLogicalKey) return byLogicalKey;

  const byIndex = lookup.byIndex.get(entityKey);
  if (byIndex) return byIndex;

  if (!entityMap) return undefined;
  return entityMap[String(entityKey)];
}

function resolveVideoUrl(info?: ArticleMediaInfo): string | undefined {
  if (!info) return undefined;
  const variants = info.variants ?? [];
  const mp4 = variants
    .filter((variant) => variant?.content_type?.includes("video"))
    .sort((a, b) => (b.bit_rate ?? 0) - (a.bit_rate ?? 0))[0];
  return mp4?.url ?? variants.find((variant) => typeof variant?.url === "string")?.url;
}

function resolveMediaAsset(info?: ArticleMediaInfo): ResolvedMediaAsset | undefined {
  if (!info) return undefined;

  const posterUrl = info.preview_image?.original_img_url ?? info.original_img_url;
  const videoUrl = resolveVideoUrl(info);
  if (videoUrl) {
    return {
      kind: "video",
      url: videoUrl,
      posterUrl,
    };
  }

  const imageUrl = info.original_img_url ?? info.preview_image?.original_img_url;
  if (imageUrl) {
    return {
      kind: "image",
      url: imageUrl,
    };
  }

  return undefined;
}

function resolveFallbackMediaAsset(rawUrl?: string): ResolvedMediaAsset | undefined {
  if (!rawUrl) return undefined;

  if (/^https:\/\/video\.twimg\.com\//i.test(rawUrl) || /\.(mp4|m4v|mov|webm)(?:$|[?#])/i.test(rawUrl)) {
    return {
      kind: "video",
      url: rawUrl,
    };
  }

  return {
    kind: "image",
    url: rawUrl,
  };
}

function resolveCoverUrl(info?: ArticleMediaInfo): string | undefined {
  if (!info) return undefined;
  return info.original_img_url ?? info.preview_image?.original_img_url;
}

function buildMediaIdentity(asset: ResolvedMediaAsset): string {
  return asset.kind === "video"
    ? `video:${asset.url}:${asset.posterUrl ?? ""}`
    : `image:${asset.url}`;
}

function renderMediaLines(
  asset: ResolvedMediaAsset,
  altText: string,
  usedUrls: Set<string>
): string[] {
  if (asset.kind === "video") {
    const lines: string[] = [];
    if (asset.posterUrl && !usedUrls.has(asset.posterUrl)) {
      usedUrls.add(asset.posterUrl);
      lines.push(`![${altText || "video"}](${asset.posterUrl})`);
    }
    if (!usedUrls.has(asset.url)) {
      usedUrls.add(asset.url);
      lines.push(`[video](${asset.url})`);
    }
    return lines;
  }

  if (usedUrls.has(asset.url)) {
    return [];
  }

  usedUrls.add(asset.url);
  return [`![${altText}](${asset.url})`];
}

function buildMediaById(article: ArticleEntity): Map<string, ResolvedMediaAsset> {
  const map = new Map<string, ResolvedMediaAsset>();
  for (const entity of article.media_entities ?? []) {
    if (!entity?.media_id) continue;
    const asset = resolveMediaAsset(entity.media_info);
    if (asset) {
      map.set(entity.media_id, asset);
    }
  }
  return map;
}

function collectMediaAssets(article: ArticleEntity): ResolvedMediaAsset[] {
  const assets: ResolvedMediaAsset[] = [];
  const seen = new Set<string>();
  const addAsset = (asset?: ResolvedMediaAsset) => {
    if (!asset) return;
    const identity = buildMediaIdentity(asset);
    if (seen.has(identity)) return;
    seen.add(identity);
    assets.push(asset);
  };

  for (const entity of article.media_entities ?? []) {
    addAsset(resolveMediaAsset(entity?.media_info));
  }

  return assets;
}

function resolveEntityMediaLines(
  entityKey: number | undefined,
  entityMap: ArticleContentState["entityMap"] | undefined,
  entityLookup: EntityLookup,
  mediaById: Map<string, ResolvedMediaAsset>,
  usedUrls: Set<string>
): string[] {
  if (entityKey === undefined) return [];
  const entry = resolveEntityEntry(entityKey, entityMap, entityLookup);
  const value = entry?.value;
  if (!value) return [];
  const type = value.type;
  if (type !== "MEDIA" && type !== "IMAGE") return [];

  const caption = normalizeCaption(value.data?.caption);
  const altText = caption ? escapeMarkdownAlt(caption) : "";
  const lines: string[] = [];

  const mediaItems = value.data?.mediaItems ?? [];
  for (const item of mediaItems) {
    const mediaId =
      typeof item?.mediaId === "string"
        ? item.mediaId
        : typeof item?.media_id === "string"
          ? item.media_id
          : undefined;
    const asset = mediaId ? mediaById.get(mediaId) : undefined;
    if (asset) {
      lines.push(...renderMediaLines(asset, altText, usedUrls));
    }
  }

  const fallbackUrl = typeof value.data?.url === "string" ? value.data.url : undefined;
  const fallbackAsset = resolveFallbackMediaAsset(fallbackUrl);
  if (fallbackAsset) {
    lines.push(...renderMediaLines(fallbackAsset, altText, usedUrls));
  }

  return lines;
}

function resolveEntityTweetLines(
  entityKey: number | undefined,
  entityMap: ArticleContentState["entityMap"] | undefined,
  entityLookup: EntityLookup,
  referencedTweets?: Map<string, ReferencedTweetInfo>
): string[] {
  if (entityKey === undefined) return [];
  const entry = resolveEntityEntry(entityKey, entityMap, entityLookup);
  const value = entry?.value;
  if (!value || value.type !== "TWEET") return [];

  const tweetId = typeof value.data?.tweetId === "string" ? value.data.tweetId : "";
  if (!tweetId) return [];

  const referenced = referencedTweets?.get(tweetId);
  const url =
    referenced?.url ??
    buildTweetUrl(tweetId, referenced?.authorUsername) ??
    `https://x.com/i/web/status/${tweetId}`;

  const authorText =
    referenced?.authorName && referenced?.authorUsername
      ? `${referenced.authorName} (@${referenced.authorUsername})`
      : referenced?.authorUsername
        ? `@${referenced.authorUsername}`
        : referenced?.authorName;

  const lines: string[] = [];
  lines.push(`> 引用推文${authorText ? `：${authorText}` : ""}`);

  const summary = summarizeTweetText(referenced?.text);
  if (summary) {
    lines.push(`> ${summary}`);
  }

  lines.push(`> ${url}`);
  return lines;
}

function resolveEntityMarkdownLines(
  entityKey: number | undefined,
  entityMap: ArticleContentState["entityMap"] | undefined,
  entityLookup: EntityLookup
): string[] {
  if (entityKey === undefined) return [];
  const entry = resolveEntityEntry(entityKey, entityMap, entityLookup);
  const value = entry?.value;
  if (!value || value.type !== "MARKDOWN") return [];

  const markdown = typeof value.data?.markdown === "string" ? value.data.markdown : "";
  const normalized = markdown.replace(/\r\n/g, "\n").trimEnd();
  if (!normalized) return [];
  return normalized.split("\n");
}

function buildMediaLinkMap(
  entityMap: ArticleContentState["entityMap"] | undefined
): Map<number, string> {
  const map = new Map<number, string>();
  if (!entityMap) return map;

  const mediaEntries: { idx: number; key: number }[] = [];
  const linkEntries: { key: number; url: string }[] = [];

  for (const [idx, entry] of Object.entries(entityMap)) {
    const value = entry?.value;
    if (!value) continue;
    const key = parseInt(entry?.key ?? "", 10);
    if (isNaN(key)) continue;

    if (value.type === "MEDIA" || value.type === "IMAGE") {
      mediaEntries.push({ idx: Number(idx), key });
    } else if (value.type === "LINK" && typeof value.data?.url === "string") {
      linkEntries.push({ key, url: value.data.url });
    }
  }

  if (mediaEntries.length === 0 || linkEntries.length === 0) return map;

  mediaEntries.sort((a, b) => a.key - b.key);
  linkEntries.sort((a, b) => a.key - b.key);

  const pool = [...linkEntries];
  for (const media of mediaEntries) {
    if (pool.length === 0) break;
    let linkIdx = pool.findIndex((l) => l.key > media.key);
    if (linkIdx === -1) linkIdx = 0;
    const link = pool.splice(linkIdx, 1)[0]!;
    map.set(media.idx, link.url);
    map.set(media.key, link.url);
  }

  return map;
}

function renderInlineLinks(
  text: string,
  entityRanges: Array<{ key?: number; offset?: number; length?: number }>,
  entityMap: ArticleContentState["entityMap"] | undefined,
  entityLookup: EntityLookup,
  mediaLinkMap: Map<number, string>
): string {
  if (!entityMap || entityRanges.length === 0) return text;

  const valid = entityRanges.filter(
    (r) =>
      typeof r.key === "number" &&
      typeof r.offset === "number" &&
      typeof r.length === "number" &&
      r.length > 0
  );
  if (valid.length === 0) return text;

  const sorted = [...valid].sort((a, b) => (b.offset ?? 0) - (a.offset ?? 0));

  let result = text;
  for (const range of sorted) {
    const offset = range.offset!;
    const length = range.length!;
    const key = range.key!;

    const entry = resolveEntityEntry(key, entityMap, entityLookup);
    const value = entry?.value;
    if (!value) continue;

    let url: string | undefined;
    if (value.type === "LINK" && typeof value.data?.url === "string") {
      url = value.data.url;
    } else if (value.type === "MEDIA" || value.type === "IMAGE") {
      url = mediaLinkMap.get(key);
    }

    if (!url) continue;

    const linkText = result.slice(offset, offset + length);
    result =
      result.slice(0, offset) +
      `[${linkText}](${url})` +
      result.slice(offset + length);
  }

  return result;
}

function renderContentBlocks(
  blocks: ArticleBlock[],
  entityMap: ArticleContentState["entityMap"] | undefined,
  entityLookup: EntityLookup,
  mediaById: Map<string, ResolvedMediaAsset>,
  usedUrls: Set<string>,
  mediaLinkMap: Map<number, string>,
  referencedTweets?: Map<string, ReferencedTweetInfo>
): string[] {
  const lines: string[] = [];
  let previousKind: "list" | "quote" | "heading" | "text" | "code" | "media" | null = null;
  let listKind: "ordered" | "unordered" | null = null;
  let orderedIndex = 0;
  let inCodeBlock = false;

  const pushBlock = (
    blockLines: string[],
    kind: "list" | "quote" | "heading" | "text" | "media"
  ) => {
    if (blockLines.length === 0) return;
    if (
      lines.length > 0 &&
      previousKind &&
      !(previousKind === kind && (kind === "list" || kind === "quote" || kind === "media"))
    ) {
      lines.push("");
    }
    lines.push(...blockLines);
    previousKind = kind;
  };

  const collectMediaLines = (block: ArticleBlock): string[] => {
    const ranges = Array.isArray(block.entityRanges) ? block.entityRanges : [];
    const mediaLines: string[] = [];
    for (const range of ranges) {
      if (typeof range?.key !== "number") continue;
      mediaLines.push(
        ...resolveEntityMediaLines(range.key, entityMap, entityLookup, mediaById, usedUrls)
      );
    }
    return mediaLines;
  };

  const collectTweetLines = (block: ArticleBlock): string[] => {
    const ranges = Array.isArray(block.entityRanges) ? block.entityRanges : [];
    const tweetLines: string[] = [];
    for (const range of ranges) {
      if (typeof range?.key !== "number") continue;
      tweetLines.push(
        ...resolveEntityTweetLines(range.key, entityMap, entityLookup, referencedTweets)
      );
    }
    return tweetLines;
  };

  const collectLinkLines = (block: ArticleBlock): string[] => {
    const ranges = Array.isArray(block.entityRanges) ? block.entityRanges : [];
    const linkLines: string[] = [];
    for (const range of ranges) {
      if (typeof range?.key !== "number") continue;
      const entry = resolveEntityEntry(range.key, entityMap, entityLookup);
      const value = entry?.value;
      if (value?.type !== "LINK") continue;
      const url = typeof value.data?.url === "string" ? value.data.url : "";
      if (url) {
        linkLines.push(url);
      }
    }
    return [...new Set(linkLines)];
  };

  const collectMarkdownLines = (block: ArticleBlock): string[] => {
    const ranges = Array.isArray(block.entityRanges) ? block.entityRanges : [];
    const markdownLines: string[] = [];
    for (const range of ranges) {
      if (typeof range?.key !== "number") continue;
      markdownLines.push(...resolveEntityMarkdownLines(range.key, entityMap, entityLookup));
    }
    return markdownLines;
  };

  const pushTrailingMedia = (mediaLines: string[]) => {
    if (mediaLines.length > 0) {
      pushBlock(mediaLines, "media");
    }
  };

  for (const block of blocks) {
    const type = typeof block?.type === "string" ? block.type : "unstyled";
    const rawText = typeof block?.text === "string" ? block.text : "";
    const ranges = Array.isArray(block.entityRanges) ? block.entityRanges : [];
    const text =
      type !== "atomic" && type !== "code-block"
        ? renderInlineLinks(rawText, ranges, entityMap, entityLookup, mediaLinkMap)
        : rawText;

    if (type === "code-block") {
      if (!inCodeBlock) {
        if (lines.length > 0) {
          lines.push("");
        }
        lines.push("```");
        inCodeBlock = true;
      }
      lines.push(text);
      previousKind = "code";
      listKind = null;
      orderedIndex = 0;
      continue;
    }

    if (type === "atomic") {
      if (inCodeBlock) {
        lines.push("```");
        inCodeBlock = false;
        previousKind = "code";
      }
      listKind = null;
      orderedIndex = 0;

      const tweetLines = collectTweetLines(block);
      if (tweetLines.length > 0) {
        pushBlock(tweetLines, "quote");
      }

      const markdownLines = collectMarkdownLines(block);
      if (markdownLines.length > 0) {
        pushBlock(markdownLines, "text");
      }

      const mediaLines = collectMediaLines(block);
      if (mediaLines.length > 0) {
        pushBlock(mediaLines, "media");
      }

      const linkLines = collectLinkLines(block);
      if (linkLines.length > 0) {
        pushBlock(linkLines, "text");
      }

      continue;
    }

    if (inCodeBlock) {
      lines.push("```");
      inCodeBlock = false;
      previousKind = "code";
    }

    if (type === "unordered-list-item") {
      listKind = "unordered";
      orderedIndex = 0;
      pushBlock([`- ${text}`], "list");
      pushTrailingMedia(collectMediaLines(block));
      continue;
    }

    if (type === "ordered-list-item") {
      if (listKind !== "ordered") {
        orderedIndex = 0;
      }
      listKind = "ordered";
      orderedIndex += 1;
      pushBlock([`${orderedIndex}. ${text}`], "list");
      pushTrailingMedia(collectMediaLines(block));
      continue;
    }

    listKind = null;
    orderedIndex = 0;

    switch (type) {
      case "header-one":
        pushBlock([`# ${text}`], "heading");
        pushTrailingMedia(collectMediaLines(block));
        break;
      case "header-two":
        pushBlock([`## ${text}`], "heading");
        pushTrailingMedia(collectMediaLines(block));
        break;
      case "header-three":
        pushBlock([`### ${text}`], "heading");
        pushTrailingMedia(collectMediaLines(block));
        break;
      case "header-four":
        pushBlock([`#### ${text}`], "heading");
        pushTrailingMedia(collectMediaLines(block));
        break;
      case "header-five":
        pushBlock([`##### ${text}`], "heading");
        pushTrailingMedia(collectMediaLines(block));
        break;
      case "header-six":
        pushBlock([`###### ${text}`], "heading");
        pushTrailingMedia(collectMediaLines(block));
        break;
      case "blockquote": {
        const quoteLines = text.length > 0 ? text.split("\n") : [""];
        pushBlock(quoteLines.map((line) => `> ${line}`), "quote");
        pushTrailingMedia(collectMediaLines(block));
        break;
      }
      default:
        if (/^XIMGPH_\d+$/.test(text.trim())) {
          pushTrailingMedia(collectMediaLines(block));
          break;
        }
        pushBlock([text], "text");
        pushTrailingMedia(collectMediaLines(block));
        break;
    }
  }

  if (inCodeBlock) {
    lines.push("```");
  }

  return lines;
}

export type FormatArticleResult = {
  markdown: string;
  coverUrl: string | null;
};

export function extractReferencedTweetIds(article: unknown): string[] {
  const candidate = coerceArticleEntity(article);
  const entityMap = candidate?.content_state?.entityMap;
  if (!entityMap) return [];

  const ids: string[] = [];
  const seen = new Set<string>();
  for (const entry of Object.values(entityMap)) {
    const value = entry?.value;
    if (value?.type !== "TWEET") continue;
    const tweetId = typeof value.data?.tweetId === "string" ? value.data.tweetId : "";
    if (!tweetId || seen.has(tweetId)) continue;
    seen.add(tweetId);
    ids.push(tweetId);
  }
  return ids;
}

export function formatArticleMarkdown(
  article: unknown,
  options: FormatArticleOptions = {}
): FormatArticleResult {
  const candidate = coerceArticleEntity(article);
  if (!candidate) {
    return { markdown: `\`\`\`json\n${JSON.stringify(article, null, 2)}\n\`\`\``, coverUrl: null };
  }

  const lines: string[] = [];
  const usedUrls = new Set<string>();
  const mediaById = buildMediaById(candidate);
  const title = typeof candidate.title === "string" ? candidate.title.trim() : "";
  if (title) {
    lines.push(`# ${title}`);
  }

  const coverUrl = resolveCoverUrl(candidate.cover_media?.media_info) ?? null;
  if (coverUrl) {
    usedUrls.add(coverUrl);
  }

  const blocks = candidate.content_state?.blocks;
  const entityMap = candidate.content_state?.entityMap;
  const entityLookup = buildEntityLookup(entityMap);
  if (Array.isArray(blocks) && blocks.length > 0) {
    const mediaLinkMap = buildMediaLinkMap(entityMap);
    const rendered = renderContentBlocks(
      blocks,
      entityMap,
      entityLookup,
      mediaById,
      usedUrls,
      mediaLinkMap,
      options.referencedTweets
    );
    if (rendered.length > 0) {
      if (lines.length > 0) lines.push("");
      lines.push(...rendered);
    }
  } else if (typeof candidate.plain_text === "string") {
    if (lines.length > 0) lines.push("");
    lines.push(candidate.plain_text.trim());
  } else if (typeof candidate.preview_text === "string") {
    if (lines.length > 0) lines.push("");
    lines.push(candidate.preview_text.trim());
  }

  const trailingMediaLines: string[] = [];
  for (const asset of collectMediaAssets(candidate)) {
    trailingMediaLines.push(...renderMediaLines(asset, "", usedUrls));
  }
  if (trailingMediaLines.length > 0) {
    lines.push("", "## Media", "");
    lines.push(...trailingMediaLines);
  }

  return { markdown: lines.join("\n").trimEnd(), coverUrl };
}
