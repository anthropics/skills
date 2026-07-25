import type { ExtractedDocument, ContentBlock } from "../../extract/document";
import { findTweetNode, formatMediaList, formatTweetAuthor, getTweetAuthorMetadata, normalizeTitle, toXTweet } from "./shared";

export function extractSingleTweetDocumentFromPayload(
  payload: unknown,
  statusId: string,
  pageUrl: string,
): ExtractedDocument | null {
  const tweet = findTweetNode(payload, statusId);
  if (!tweet) {
    return null;
  }

  const xTweet = toXTweet(tweet, pageUrl);
  const content: ContentBlock[] = [];

  if (xTweet.text) {
    content.push({ type: "paragraph", text: xTweet.text });
  }

  for (const mediaLine of formatMediaList(xTweet.media)) {
    if (mediaLine.startsWith("photo: ")) {
      content.push({
        type: "image",
        url: mediaLine.slice("photo: ".length),
      });
    } else {
      content.push({
        type: "list",
        ordered: false,
        items: [mediaLine],
      });
    }
  }

  if (xTweet.quotedTweet) {
    const quotedLines: string[] = [];
    const quotedAuthor =
      xTweet.quotedTweet.author && xTweet.quotedTweet.authorName
        ? `${xTweet.quotedTweet.authorName} (@${xTweet.quotedTweet.author})`
        : xTweet.quotedTweet.author
          ? `@${xTweet.quotedTweet.author}`
          : xTweet.quotedTweet.authorName;

    if (quotedAuthor) {
      quotedLines.push(quotedAuthor);
    }
    if (xTweet.quotedTweet.text) {
      quotedLines.push(xTweet.quotedTweet.text);
    }
    quotedLines.push(...formatMediaList(xTweet.quotedTweet.media));

    if (quotedLines.length > 0) {
      content.push({ type: "heading", depth: 2, text: "Quoted Tweet" });
      content.push({ type: "quote", text: quotedLines.join("\n\n") });
    }
  }

  return {
    url: pageUrl,
    canonicalUrl: xTweet.url,
    title: normalizeTitle(
      xTweet.author ? `@${xTweet.author}: ${xTweet.text}` : xTweet.text,
      "Tweet",
    ),
    author: formatTweetAuthor(xTweet),
    siteName: "X",
    publishedAt: xTweet.createdAt,
    summary: xTweet.text.slice(0, 200) || undefined,
    adapter: "x",
    metadata: {
      kind: "x/post",
      tweetId: xTweet.id,
      ...getTweetAuthorMetadata(xTweet),
      conversationId:
        typeof tweet.legacy === "object" &&
        tweet.legacy !== null &&
        typeof (tweet.legacy as Record<string, unknown>).conversation_id_str === "string"
          ? (tweet.legacy as Record<string, unknown>).conversation_id_str
          : undefined,
      favoriteCount: xTweet.likes,
      replyCount: xTweet.replies,
      retweetCount: xTweet.retweets,
    },
    content,
  };
}
