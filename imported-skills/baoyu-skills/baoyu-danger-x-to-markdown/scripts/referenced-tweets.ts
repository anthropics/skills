import { fetchXTweet } from "./graphql.js";
import {
  extractReferencedTweetIds,
  type ReferencedTweetInfo,
} from "./markdown.js";

type ResolveReferencedTweetsOptions = {
  log?: (message: string) => void;
};

function extractReferencedTweetInfo(tweet: any, fallbackTweetId: string): ReferencedTweetInfo {
  const userCore = tweet?.core?.user_results?.result?.core;
  const userLegacy = tweet?.core?.user_results?.result?.legacy;

  const authorName =
    typeof userCore?.name === "string"
      ? userCore.name
      : typeof userLegacy?.name === "string"
        ? userLegacy.name
        : undefined;

  const authorUsername =
    typeof userCore?.screen_name === "string"
      ? userCore.screen_name
      : typeof userLegacy?.screen_name === "string"
        ? userLegacy.screen_name
        : undefined;

  const text =
    tweet?.note_tweet?.note_tweet_results?.result?.text ??
    tweet?.legacy?.full_text ??
    tweet?.legacy?.text ??
    undefined;

  const tweetId =
    typeof tweet?.rest_id === "string" && tweet.rest_id.length > 0
      ? tweet.rest_id
      : fallbackTweetId;

  const url = authorUsername
    ? `https://x.com/${authorUsername}/status/${tweetId}`
    : `https://x.com/i/web/status/${tweetId}`;

  return {
    id: tweetId,
    url,
    authorName,
    authorUsername,
    text: typeof text === "string" ? text : undefined,
  };
}

export async function resolveReferencedTweetsFromArticle(
  article: unknown,
  cookieMap: Record<string, string>,
  options: ResolveReferencedTweetsOptions = {}
): Promise<Map<string, ReferencedTweetInfo>> {
  const log = options.log ?? (() => {});
  const ids = extractReferencedTweetIds(article);
  const referencedTweets = new Map<string, ReferencedTweetInfo>();

  for (const id of ids) {
    try {
      const tweet = await fetchXTweet(id, cookieMap, false);
      const info = extractReferencedTweetInfo(tweet, id);
      referencedTweets.set(id, info);
    } catch (error) {
      log(
        `[x-to-markdown] Failed to fetch referenced tweet ${id}: ${
          error instanceof Error ? error.message : String(error)
        }`
      );
      referencedTweets.set(id, {
        id,
        url: `https://x.com/i/web/status/${id}`,
      });
    }
  }

  return referencedTweets;
}
