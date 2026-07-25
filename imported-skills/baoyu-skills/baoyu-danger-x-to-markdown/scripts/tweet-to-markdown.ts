#!/usr/bin/env npx tsx

import * as path from "node:path";
import { fileURLToPath } from "node:url";
import { hasRequiredXCookies, loadXCookies } from "./cookies.js";
import { fetchTweetThread } from "./thread.js";
import { formatArticleMarkdown } from "./markdown.js";
import { resolveReferencedTweetsFromArticle } from "./referenced-tweets.js";
import { formatThreadTweetsMarkdown } from "./thread-markdown.js";
import { resolveArticleEntityFromTweet } from "./tweet-article.js";

type TweetToMarkdownOptions = {
  log?: (message: string) => void;
};

function parseArgs(): { url?: string } {
  const args = process.argv.slice(2);
  let url: string | undefined;

  for (const arg of args) {
    if (!arg.startsWith("-") && !url) {
      url = arg;
    }
  }

  return { url };
}

function normalizeInputUrl(input: string): string {
  const trimmed = input.trim();
  if (!trimmed) return "";
  try {
    return new URL(trimmed).toString();
  } catch {
    return trimmed;
  }
}

function formatScriptCommand(fallback: string): string {
  const raw = process.argv[1];
  const displayPath = raw
    ? (() => {
        const relative = path.relative(process.cwd(), raw);
        return relative && !relative.startsWith("..") ? relative : raw;
      })()
    : fallback;
  const quotedPath = displayPath.includes(" ")
    ? `"${displayPath.replace(/"/g, '\\"')}"`
    : displayPath;
  return `npx -y bun ${quotedPath}`;
}

function parseTweetId(input: string): string | null {
  const trimmed = input.trim();
  if (!trimmed) return null;
  if (/^\d+$/.test(trimmed)) return trimmed;

  try {
    const parsed = new URL(trimmed);
    const match = parsed.pathname.match(/\/status(?:es)?\/(\d+)/);
    if (match?.[1]) return match[1];
  } catch {
    return null;
  }

  return null;
}

function buildTweetUrl(username: string | undefined, tweetId: string | undefined): string | null {
  if (!tweetId) return null;
  if (username) {
    return `https://x.com/${username}/status/${tweetId}`;
  }
  return `https://x.com/i/web/status/${tweetId}`;
}

function formatMetaMarkdown(meta: Record<string, string | number | null | undefined>): string {
  const lines = ["---"];
  for (const [key, value] of Object.entries(meta)) {
    if (value === undefined || value === null || value === "") continue;
    if (typeof value === "number") {
      lines.push(`${key}: ${value}`);
    } else {
      lines.push(`${key}: ${JSON.stringify(value)}`);
    }
  }
  lines.push("---");
  return lines.join("\n");
}

function extractTweetText(tweet: any): string {
  const noteText = tweet?.note_tweet?.note_tweet_results?.result?.text;
  const legacyText = tweet?.legacy?.full_text ?? tweet?.legacy?.text ?? "";
  return (noteText ?? legacyText ?? "").trim();
}

function isOnlyUrl(text: string): boolean {
  const trimmed = text.trim();
  if (!trimmed) return true;
  return /^https?:\/\/\S+$/.test(trimmed);
}

export async function tweetToMarkdown(
  inputUrl: string,
  options: TweetToMarkdownOptions = {}
): Promise<string> {
  const normalizedUrl = normalizeInputUrl(inputUrl);
  const tweetId = parseTweetId(normalizedUrl);
  if (!tweetId) {
    throw new Error("Invalid tweet url. Example: https://x.com/<user>/status/<tweet_id>");
  }

  const log = options.log ?? (() => {});
  log("[tweet-to-markdown] Loading cookies...");
  const cookieMap = await loadXCookies(log);
  if (!hasRequiredXCookies(cookieMap)) {
    throw new Error("Missing auth cookies. Provide X_AUTH_TOKEN and X_CT0 or log in via Chrome.");
  }

  log(`[tweet-to-markdown] Fetching thread for ${tweetId}...`);
  const thread = await fetchTweetThread(tweetId, cookieMap);
  if (!thread) {
    throw new Error("Failed to fetch thread.");
  }

  const tweets = thread.tweets ?? [];
  if (tweets.length === 0) {
    throw new Error("No tweets found in thread.");
  }

  const firstTweet = tweets[0] as any;
  const user = thread.user ?? firstTweet?.core?.user_results?.result?.legacy;
  const username = user?.screen_name;
  const name = user?.name;
  const author =
    username && name ? `${name} (@${username})` : username ? `@${username}` : name ?? null;
  const authorUrl = username ? `https://x.com/${username}` : undefined;
  const requestedUrl = normalizedUrl || buildTweetUrl(username, tweetId) || inputUrl.trim();
  const rootUrl = buildTweetUrl(username, thread.rootId ?? tweetId) ?? requestedUrl;

  const articleEntity = await resolveArticleEntityFromTweet(firstTweet, cookieMap);
  let coverImage: string | null = null;
  let remainingTweets = tweets;
  const parts: string[] = [];

  if (articleEntity) {
    const referencedTweets = await resolveReferencedTweetsFromArticle(articleEntity, cookieMap, { log });
    const articleResult = formatArticleMarkdown(articleEntity, { referencedTweets });
    coverImage = articleResult.coverUrl;
    const articleMarkdown = articleResult.markdown.trimEnd();
    if (articleMarkdown) {
      parts.push(articleMarkdown);
      const firstTweetText = extractTweetText(firstTweet);
      if (isOnlyUrl(firstTweetText)) {
        remainingTweets = tweets.slice(1);
      }
    }
  }

  const meta = formatMetaMarkdown({
    url: rootUrl,
    requestedUrl: requestedUrl,
    author,
    authorName: name ?? null,
    authorUsername: username ?? null,
    authorUrl: authorUrl ?? null,
    tweetCount: thread.totalTweets ?? tweets.length,
    coverImage,
  });

  parts.unshift(meta);

  if (remainingTweets.length > 0) {
    const hasArticle = parts.length > 1;
    if (hasArticle) {
      parts.push("## Thread");
    }
    const tweetMarkdown = formatThreadTweetsMarkdown(remainingTweets, {
      username,
      headingLevel: hasArticle ? 3 : 2,
      startIndex: 1,
      includeTweetUrls: true,
    });
    if (tweetMarkdown) {
      parts.push(tweetMarkdown);
    }
  }

  return parts.join("\n\n").trimEnd();
}

async function main() {
  const { url } = parseArgs();
  if (!url) {
    console.error("Usage:");
    console.error(`  ${formatScriptCommand("scripts/tweet-to-markdown.ts")} <tweet url>`);
    process.exit(1);
  }

  const markdown = await tweetToMarkdown(url, { log: console.log });
  console.log(markdown);
}

const isCliExecution =
  process.argv[1] && fileURLToPath(import.meta.url) === path.resolve(process.argv[1]);

if (isCliExecution) {
  main().catch((error) => {
    console.error(error instanceof Error ? error.message : error);
    process.exit(1);
  });
}
