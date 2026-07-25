type ThreadLike = {
  requestedId?: string;
  rootId?: string;
  tweets?: unknown[];
  totalTweets?: number;
  user?: any;
};

type TweetPhoto = {
  src: string;
  alt?: string;
};

type TweetVideo = {
  url: string;
  poster?: string;
  alt?: string;
  type?: string;
};

export type ThreadTweetsMarkdownOptions = {
  username?: string;
  headingLevel?: number;
  startIndex?: number;
  includeTweetUrls?: boolean;
};

export type ThreadMarkdownOptions = ThreadTweetsMarkdownOptions & {
  includeHeader?: boolean;
  title?: string;
  sourceUrl?: string;
};

function coerceThread(value: unknown): ThreadLike | null {
  if (!value || typeof value !== "object") return null;
  const candidate = value as ThreadLike;
  if (!Array.isArray(candidate.tweets)) return null;
  return candidate;
}

function escapeMarkdownAlt(text: string): string {
  return text.replace(/[\[\]]/g, "\\$&");
}

function normalizeAlt(text?: string | null): string {
  const trimmed = text?.trim();
  if (!trimmed) return "";
  return trimmed.replace(/\s+/g, " ");
}

function parseTweetText(tweet: any): string {
  const noteText = tweet?.note_tweet?.note_tweet_results?.result?.text;
  const legacyText = tweet?.legacy?.full_text ?? tweet?.legacy?.text ?? "";
  return (noteText ?? legacyText ?? "").trim();
}

function parsePhotos(tweet: any): TweetPhoto[] {
  const media = tweet?.legacy?.extended_entities?.media ?? [];
  return media
    .reduce((acc: TweetPhoto[], item: any) => {
      if (item?.type !== "photo") {
        return acc;
      }
      const src = item.media_url_https ?? item.media_url;
      if (!src) {
        return acc;
      }
      const alt = normalizeAlt(item.ext_alt_text);
      acc.push({ src, alt });
      return acc;
    }, [])
    .filter((photo) => Boolean(photo.src));
}

function parseVideos(tweet: any): TweetVideo[] {
  const media = tweet?.legacy?.extended_entities?.media ?? [];
  return media
    .reduce((acc: TweetVideo[], item: any) => {
      if (!item?.type || !["animated_gif", "video"].includes(item.type)) {
        return acc;
      }
      const variants = item?.video_info?.variants ?? [];
      const sources = variants
        .map((variant: any) => ({
          contentType: variant?.content_type,
          url: variant?.url,
          bitrate: variant?.bitrate ?? 0,
        }))
        .filter((variant: any) => Boolean(variant.url));

      const videoSources = sources.filter((variant: any) =>
        String(variant.contentType ?? "").includes("video")
      );
      const sorted = (videoSources.length > 0 ? videoSources : sources).sort(
        (a: any, b: any) => (b.bitrate ?? 0) - (a.bitrate ?? 0)
      );
      const best = sorted[0];
      if (!best?.url) {
        return acc;
      }
      const alt = normalizeAlt(item.ext_alt_text);
      acc.push({
        url: best.url,
        poster: item.media_url_https ?? item.media_url ?? undefined,
        alt,
        type: item.type,
      });
      return acc;
    }, [])
    .filter((video) => Boolean(video.url));
}

function unwrapTweetResult(result: any): any {
  if (!result) return null;
  if (result.__typename === "TweetWithVisibilityResults" && result.tweet) {
    return result.tweet;
  }
  return result;
}

function resolveTweetId(tweet: any): string | undefined {
  return tweet?.legacy?.id_str ?? tweet?.rest_id;
}

function buildTweetUrl(username: string | undefined, tweetId: string | undefined): string | null {
  if (!tweetId) return null;
  if (username) {
    return `https://x.com/${username}/status/${tweetId}`;
  }
  return `https://x.com/i/web/status/${tweetId}`;
}

function formatTweetMarkdown(
  tweet: any,
  index: number,
  options: ThreadTweetsMarkdownOptions
): string[] {
  const headingLevel = options.headingLevel ?? 2;
  const includeTweetUrls = options.includeTweetUrls ?? true;
  const headingPrefix = "#".repeat(Math.min(Math.max(headingLevel, 1), 6));
  const tweetId = resolveTweetId(tweet);
  const tweetUrl = includeTweetUrls ? buildTweetUrl(options.username, tweetId) : null;

  const lines: string[] = [];
  lines.push(`${headingPrefix} ${index}`);
  if (tweetUrl) {
    lines.push(tweetUrl);
  }
  lines.push("");

  const text = parseTweetText(tweet);
  const photos = parsePhotos(tweet);
  const videos = parseVideos(tweet);
  const quoted = unwrapTweetResult(tweet?.quoted_status_result?.result);

  const bodyLines: string[] = [];
  if (text) {
    bodyLines.push(...text.split(/\r?\n/));
  }

  const quotedLines = formatQuotedTweetMarkdown(quoted);
  if (quotedLines.length > 0) {
    if (bodyLines.length > 0) bodyLines.push("");
    bodyLines.push(...quotedLines);
  }

  const photoLines = photos.map((photo) => {
    const alt = photo.alt ? escapeMarkdownAlt(photo.alt) : "";
    return `![${alt}](${photo.src})`;
  });
  if (photoLines.length > 0) {
    if (bodyLines.length > 0) bodyLines.push("");
    bodyLines.push(...photoLines);
  }

  const videoLines: string[] = [];
  for (const video of videos) {
    if (video.poster) {
      const alt = video.alt ? escapeMarkdownAlt(video.alt) : "video";
      videoLines.push(`![${alt}](${video.poster})`);
    }
    videoLines.push(`[${video.type ?? "video"}](${video.url})`);
  }
  if (videoLines.length > 0) {
    if (bodyLines.length > 0) bodyLines.push("");
    bodyLines.push(...videoLines);
  }

  if (bodyLines.length === 0) {
    bodyLines.push("_No text or media._");
  }

  lines.push(...bodyLines);
  return lines;
}

function formatQuotedTweetMarkdown(quoted: any): string[] {
  if (!quoted) return [];
  const quotedUser = quoted?.core?.user_results?.result?.legacy;
  const quotedUsername = quotedUser?.screen_name;
  const quotedName = quotedUser?.name;
  const quotedAuthor =
    quotedUsername && quotedName
      ? `${quotedName} (@${quotedUsername})`
      : quotedUsername
        ? `@${quotedUsername}`
        : quotedName ?? "Unknown";

  const quotedId = resolveTweetId(quoted);
  const quotedUrl =
    buildTweetUrl(quotedUsername, quotedId) ??
    (quotedId ? `https://x.com/i/web/status/${quotedId}` : "unavailable");

  const quotedText = parseTweetText(quoted);
  const lines: string[] = [];
  lines.push(`Author: ${quotedAuthor}`);
  lines.push(`URL: ${quotedUrl}`);
  if (quotedText) {
    lines.push("", ...quotedText.split(/\r?\n/));
  } else {
    lines.push("", "(no content)");
  }

  return lines.map((line) => `> ${line}`.trimEnd());
}

export function formatThreadTweetsMarkdown(
  tweets: unknown[],
  options: ThreadTweetsMarkdownOptions = {}
): string {
  const lines: string[] = [];
  const startIndex = options.startIndex ?? 1;
  if (!Array.isArray(tweets) || tweets.length === 0) {
    return "";
  }

  tweets.forEach((tweet, index) => {
    if (lines.length > 0) {
      lines.push("");
    }
    lines.push(...formatTweetMarkdown(tweet, startIndex + index, options));
  });

  return lines.join("\n").trimEnd();
}

export function formatThreadMarkdown(
  thread: unknown,
  options: ThreadMarkdownOptions = {}
): string {
  const candidate = coerceThread(thread);
  if (!candidate) {
    return `\`\`\`json\n${JSON.stringify(thread, null, 2)}\n\`\`\``;
  }

  const tweets = candidate.tweets ?? [];
  const firstTweet = tweets[0] as any;
  const user = candidate.user ?? firstTweet?.core?.user_results?.result?.legacy;
  const username = user?.screen_name;
  const name = user?.name;

  const includeHeader = options.includeHeader ?? true;
  const lines: string[] = [];
  if (includeHeader) {
    if (options.title) {
      lines.push(`# ${options.title}`);
    } else if (username) {
      lines.push(`# Thread by @${username}${name ? ` (${name})` : ""}`);
    } else {
      lines.push("# Thread");
    }

    const sourceUrl = options.sourceUrl ?? buildTweetUrl(username, candidate.rootId ?? candidate.requestedId);
    if (sourceUrl) {
      lines.push(`Source: ${sourceUrl}`);
    }
    if (typeof candidate.totalTweets === "number") {
      lines.push(`Tweets: ${candidate.totalTweets}`);
    }
  }

  const tweetMarkdown = formatThreadTweetsMarkdown(tweets, {
    ...options,
    username,
  });

  if (tweetMarkdown) {
    if (lines.length > 0) {
      lines.push("");
    }
    lines.push(tweetMarkdown);
  }

  return lines.join("\n").trimEnd();
}
