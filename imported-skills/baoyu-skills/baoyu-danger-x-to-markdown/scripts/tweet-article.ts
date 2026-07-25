import { fetchXArticle } from "./graphql.js";
import type { ArticleEntity } from "./types.js";

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

function hasArticleContent(article: ArticleEntity): boolean {
  const blocks = article.content_state?.blocks;
  if (Array.isArray(blocks) && blocks.length > 0) {
    return true;
  }
  if (typeof article.plain_text === "string" && article.plain_text.trim()) {
    return true;
  }
  if (typeof article.preview_text === "string" && article.preview_text.trim()) {
    return true;
  }
  return false;
}

function parseArticleIdFromUrl(raw: string | undefined): string | null {
  if (!raw) return null;
  try {
    const parsed = new URL(raw);
    const match = parsed.pathname.match(/\/(?:i\/)?article\/(\d+)/);
    if (match?.[1]) return match[1];
  } catch {
    return null;
  }
  return null;
}

function extractArticleIdFromUrls(urls: any[] | undefined): string | null {
  if (!Array.isArray(urls)) return null;
  for (const url of urls) {
    const candidate =
      url?.expanded_url ?? url?.url ?? (url?.display_url ? `https://${url.display_url}` : undefined);
    const id = parseArticleIdFromUrl(candidate);
    if (id) return id;
  }
  return null;
}

export function extractArticleEntityFromTweet(tweet: any): unknown | null {
  return (
    tweet?.article?.article_results?.result ??
    tweet?.article?.result ??
    tweet?.legacy?.article?.article_results?.result ??
    tweet?.legacy?.article?.result ??
    tweet?.article_results?.result ??
    null
  );
}

export function extractArticleIdFromTweet(tweet: any): string | null {
  const embedded = extractArticleEntityFromTweet(tweet);
  const embeddedArticle = embedded as { rest_id?: string } | null;
  if (embeddedArticle?.rest_id) {
    return embeddedArticle.rest_id;
  }

  const noteUrls = tweet?.note_tweet?.note_tweet_results?.result?.entity_set?.urls;
  const legacyUrls = tweet?.legacy?.entities?.urls;
  return extractArticleIdFromUrls(noteUrls) ?? extractArticleIdFromUrls(legacyUrls);
}

export async function resolveArticleEntityFromTweet(
  tweet: any,
  cookieMap: Record<string, string>
): Promise<unknown | null> {
  if (!tweet) return null;
  const embedded = extractArticleEntityFromTweet(tweet);
  const embeddedArticle = coerceArticleEntity(embedded);
  if (embeddedArticle && hasArticleContent(embeddedArticle)) {
    return embedded;
  }

  const articleId = extractArticleIdFromTweet(tweet);
  if (!articleId) {
    return embedded ?? null;
  }

  const fetched = await fetchXArticle(articleId, cookieMap, false);
  return fetched ?? embedded ?? null;
}
