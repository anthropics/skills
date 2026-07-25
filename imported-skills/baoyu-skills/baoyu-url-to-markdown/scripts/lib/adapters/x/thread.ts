import type { ExtractedDocument } from "../../extract/document";
import {
  formatMediaList,
  formatTweetAuthor,
  getLegacy,
  getTweetAuthorMetadata,
  isRecord,
  normalizeTitle,
  toXTweet,
  unwrapTweetResult,
} from "./shared";
import type { JsonObject, XQuotedTweet, XTweet } from "./types";

interface ParsedThreadTweet extends XTweet {
  userId?: string;
  conversationId?: string;
  inReplyToUserId?: string;
  sortTimestamp: number;
}

function compareTweetIds(left: string, right: string): number {
  try {
    const leftId = BigInt(left);
    const rightId = BigInt(right);
    if (leftId === rightId) {
      return 0;
    }
    return leftId < rightId ? -1 : 1;
  } catch {
    return left.localeCompare(right);
  }
}

function toTimestamp(value: string | undefined): number {
  if (!value) {
    return 0;
  }
  const parsed = Date.parse(value);
  return Number.isNaN(parsed) ? 0 : parsed;
}

function scoreParsedTweet(tweet: ParsedThreadTweet): number {
  return (
    (tweet.text ? 4 : 0) +
    (tweet.author ? 2 : 0) +
    (tweet.authorName ? 2 : 0) +
    (tweet.media.length > 0 ? 1 : 0)
  );
}

function toParsedThreadTweet(tweet: JsonObject, pageUrl: string): ParsedThreadTweet {
  const legacy = getLegacy(tweet);
  const xTweet = toXTweet(tweet, pageUrl);

  return {
    ...xTweet,
    userId: typeof legacy.user_id_str === "string" ? legacy.user_id_str : undefined,
    conversationId: typeof legacy.conversation_id_str === "string" ? legacy.conversation_id_str : undefined,
    inReplyToUserId: typeof legacy.in_reply_to_user_id_str === "string" ? legacy.in_reply_to_user_id_str : undefined,
    sortTimestamp: toTimestamp(xTweet.createdAt),
  };
}

function collectTweetFromItemContent(
  itemContent: unknown,
  pageUrl: string,
  tweets: Map<string, ParsedThreadTweet>,
): void {
  if (!isRecord(itemContent)) {
    return;
  }

  const tweet = unwrapTweetResult(
    isRecord(itemContent.tweet_results) ? itemContent.tweet_results.result : null,
  );
  if (!tweet || typeof tweet.rest_id !== "string") {
    return;
  }

  const parsed = toParsedThreadTweet(tweet, pageUrl);
  const existing = tweets.get(parsed.id);
  if (!existing || scoreParsedTweet(parsed) >= scoreParsedTweet(existing)) {
    tweets.set(parsed.id, parsed);
  }
}

function collectTweetsFromItems(
  items: unknown,
  pageUrl: string,
  tweets: Map<string, ParsedThreadTweet>,
): void {
  if (!Array.isArray(items)) {
    return;
  }

  for (const item of items) {
    if (!isRecord(item)) {
      continue;
    }

    if (isRecord(item.item) && isRecord(item.item.itemContent)) {
      collectTweetFromItemContent(item.item.itemContent, pageUrl, tweets);
      continue;
    }

    if (isRecord(item.itemContent)) {
      collectTweetFromItemContent(item.itemContent, pageUrl, tweets);
    }
  }
}

function getInstructions(payload: unknown): unknown[] {
  if (!isRecord(payload) || !isRecord(payload.data)) {
    return [];
  }

  const { data } = payload;
  return (
    (isRecord(data.threaded_conversation_with_injections_v2) &&
    Array.isArray(data.threaded_conversation_with_injections_v2.instructions)
      ? data.threaded_conversation_with_injections_v2.instructions
      : undefined) ??
    (isRecord(data.threaded_conversation_with_injections) &&
    Array.isArray(data.threaded_conversation_with_injections.instructions)
      ? data.threaded_conversation_with_injections.instructions
      : undefined) ??
    (isRecord(data.tweetResult) &&
    isRecord(data.tweetResult.result) &&
    isRecord(data.tweetResult.result.timeline) &&
    Array.isArray(data.tweetResult.result.timeline.instructions)
      ? data.tweetResult.result.timeline.instructions
      : [])
  );
}

function parseTweetDetailPayload(payload: unknown, pageUrl: string): ParsedThreadTweet[] {
  const tweets = new Map<string, ParsedThreadTweet>();

  const instructions = getInstructions(payload);
  for (const instruction of instructions) {
    if (!isRecord(instruction)) {
      continue;
    }

    collectTweetsFromItems(instruction.moduleItems, pageUrl, tweets);

    if (!Array.isArray(instruction.entries)) {
      continue;
    }

    for (const entry of instruction.entries) {
      if (!isRecord(entry)) {
        continue;
      }

      const content = isRecord(entry.content) ? entry.content : {};
      collectTweetFromItemContent(content.itemContent, pageUrl, tweets);
      collectTweetsFromItems(content.items, pageUrl, tweets);
    }
  }

  return Array.from(tweets.values());
}

function buildContinuousThread(tweets: ParsedThreadTweet[], statusId: string): ParsedThreadTweet[] {
  const byId = new Map<string, ParsedThreadTweet>();
  for (const tweet of tweets) {
    const existing = byId.get(tweet.id);
    if (!existing || scoreParsedTweet(tweet) >= scoreParsedTweet(existing)) {
      byId.set(tweet.id, tweet);
    }
  }

  const rootTweet = byId.get(statusId);
  if (!rootTweet?.userId || !rootTweet.conversationId) {
    return [];
  }

  const candidates = Array.from(byId.values()).filter(
    (tweet) =>
      tweet.id === statusId ||
      (tweet.userId === rootTweet.userId && tweet.conversationId === rootTweet.conversationId),
  );

  const repliesByParent = new Map<string, ParsedThreadTweet[]>();
  for (const tweet of candidates) {
    if (!tweet.inReplyTo || tweet.id === statusId) {
      continue;
    }
    const bucket = repliesByParent.get(tweet.inReplyTo) ?? [];
    bucket.push(tweet);
    bucket.sort((left, right) => {
      if (left.sortTimestamp !== right.sortTimestamp) {
        return left.sortTimestamp - right.sortTimestamp;
      }
      return compareTweetIds(left.id, right.id);
    });
    repliesByParent.set(tweet.inReplyTo, bucket);
  }

  const ancestorPath: ParsedThreadTweet[] = [rootTweet];
  const ancestorSeen = new Set<string>([rootTweet.id]);
  let currentAncestor = rootTweet;

  while (currentAncestor.inReplyTo) {
    const parent = byId.get(currentAncestor.inReplyTo);
    if (!parent || ancestorSeen.has(parent.id)) {
      break;
    }
    ancestorPath.unshift(parent);
    ancestorSeen.add(parent.id);
    currentAncestor = parent;
  }

  const chain = ancestorPath.slice();
  const seen = new Set<string>(chain.map((tweet) => tweet.id));
  let currentId = rootTweet.id;

  while (true) {
    const next = (repliesByParent.get(currentId) ?? []).find((tweet) => !seen.has(tweet.id));
    if (!next) {
      break;
    }
    chain.push(next);
    seen.add(next.id);
    currentId = next.id;
  }

  return chain;
}

export function extractThreadTweetsFromPayloads(
  payloads: unknown[],
  statusId: string,
  pageUrl: string,
): XTweet[] {
  const parsedTweets: ParsedThreadTweet[] = [];

  for (const payload of payloads) {
    parsedTweets.push(...parseTweetDetailPayload(payload, pageUrl));
  }

  return buildContinuousThread(parsedTweets, statusId).map(({ sortTimestamp: _sortTimestamp, ...tweet }) => tweet);
}

function buildQuotedTweetMarkdown(quotedTweet: XQuotedTweet): string {
  const author = quotedTweet.author ? `@${quotedTweet.author}` : "Unknown";
  const name = quotedTweet.authorName ? `${quotedTweet.authorName} ` : "";
  const lines: string[] = [`Quoted Tweet${quotedTweet.author || quotedTweet.authorName ? `: ${name}${author}`.trim() : ""}`];

  if (quotedTweet.text) {
    lines.push(...quotedTweet.text.split("\n"));
  }

  for (const mediaLine of formatMediaList(quotedTweet.media)) {
    lines.push(mediaLine);
  }

  return lines.map((line) => (line ? `> ${line}` : ">")).join("\n");
}

function buildThreadMarkdown(tweets: XTweet[]): string {
  return tweets
    .map((tweet, index) => {
      const lines: string[] = [];
      const author = tweet.author ? `@${tweet.author}` : "Unknown";
      const name = tweet.authorName ? `${tweet.authorName} ` : "";
      lines.push(`## ${index + 1}. ${name}${author}`.trim());
      if (tweet.createdAt) {
        lines.push(`_Published: ${tweet.createdAt}_`);
      }
      lines.push(tweet.text || "(No text)");
      const mediaLines = formatMediaList(tweet.media);
      if (mediaLines.length > 0) {
        lines.push(mediaLines.map((line) => `- ${line}`).join("\n"));
      }
      if (tweet.quotedTweet) {
        lines.push(buildQuotedTweetMarkdown(tweet.quotedTweet));
      }
      return lines.join("\n\n");
    })
    .join("\n\n");
}

export function extractThreadDocumentFromPayloads(
  payloads: unknown[],
  statusId: string,
  pageUrl: string,
): ExtractedDocument | null {
  const tweets = extractThreadTweetsFromPayloads(payloads, statusId, pageUrl);
  if (tweets.length <= 1) {
    return null;
  }

  const rootTweet = tweets[0];
  const rootAuthor = formatTweetAuthor(rootTweet);

  return {
    url: pageUrl,
    canonicalUrl: rootTweet.url,
    title: normalizeTitle(rootTweet.text, "X Thread"),
    author: rootAuthor,
    siteName: "X",
    publishedAt: rootTweet.createdAt,
    summary: rootTweet.text.slice(0, 200) || undefined,
    adapter: "x",
    metadata: {
      kind: "x/thread",
      tweetId: rootTweet.id,
      tweetCount: tweets.length,
      lastTweetId: tweets[tweets.length - 1]?.id,
      ...getTweetAuthorMetadata(rootTweet),
    },
    content: [{ type: "markdown", markdown: buildThreadMarkdown(tweets) }],
  };
}
