import {
  DEFAULT_BEARER_TOKEN,
  DEFAULT_USER_AGENT,
  FALLBACK_FEATURE_SWITCHES,
  FALLBACK_FIELD_TOGGLES,
  FALLBACK_QUERY_ID,
  FALLBACK_TWEET_DETAIL_FEATURE_DEFAULTS,
  FALLBACK_TWEET_DETAIL_FEATURE_SWITCHES,
  FALLBACK_TWEET_DETAIL_FIELD_TOGGLES,
  FALLBACK_TWEET_DETAIL_QUERY_ID,
  FALLBACK_TWEET_FEATURE_SWITCHES,
  FALLBACK_TWEET_FIELD_TOGGLES,
  FALLBACK_TWEET_QUERY_ID,
} from "./constants.js";
import {
  buildFeatureMap,
  buildFieldToggleMap,
  buildRequestHeaders,
  buildTweetFieldToggleMap,
  fetchHomeHtml,
  fetchText,
  parseStringList,
} from "./http.js";
import type { ArticleQueryInfo } from "./types.js";

function isNonEmptyObject(value: unknown): value is Record<string, unknown> {
  return Boolean(value && typeof value === "object" && Object.keys(value as Record<string, unknown>).length > 0);
}

function unwrapTweetResult(result: any): any {
  if (!result) return null;
  if (result.__typename === "TweetWithVisibilityResults" && result.tweet) {
    return result.tweet;
  }
  return result;
}

function extractArticleFromTweet(payload: unknown): unknown {
  const root = (payload as { data?: any }).data ?? payload;
  const result = root?.tweetResult?.result ?? root?.tweet_result?.result ?? root?.tweet_result;
  const tweet = unwrapTweetResult(result);
  const legacy = tweet?.legacy ?? {};
  const article = legacy?.article ?? tweet?.article;
  return (
    article?.article_results?.result ??
    legacy?.article_results?.result ??
    tweet?.article_results?.result ??
    null
  );
}

function extractTweetFromPayload(payload: unknown): unknown {
  const root = (payload as { data?: any }).data ?? payload;
  const result = root?.tweetResult?.result ?? root?.tweet_result?.result ?? root?.tweet_result;
  return unwrapTweetResult(result);
}

function extractArticleFromEntity(payload: unknown): unknown {
  const root = (payload as { data?: any }).data ?? payload;
  return (
    root?.article_result_by_rest_id?.result ??
    root?.article_result_by_rest_id ??
    root?.article_entity_result?.result ??
    null
  );
}

async function resolveArticleQueryInfo(userAgent: string): Promise<ArticleQueryInfo> {
  const html = await fetchHomeHtml(userAgent);

  const bundleMatch = html.match(/"bundle\\.TwitterArticles":"([a-z0-9]+)"/);
  if (!bundleMatch) {
    return {
      queryId: FALLBACK_QUERY_ID,
      featureSwitches: FALLBACK_FEATURE_SWITCHES,
      fieldToggles: FALLBACK_FIELD_TOGGLES,
      html,
    };
  }

  const bundleHash = bundleMatch[1];
  const chunkUrl = `https://abs.twimg.com/responsive-web/client-web/bundle.TwitterArticles.${bundleHash}a.js`;
  const chunk = await fetchText(chunkUrl, {
    headers: {
      "user-agent": userAgent,
    },
  });

  const queryIdMatch = chunk.match(/queryId:\"([^\"]+)\",operationName:\"ArticleEntityResultByRestId\"/);
  const featureMatch = chunk.match(
    /operationName:\"ArticleEntityResultByRestId\"[\s\S]*?featureSwitches:\[(.*?)\]/
  );
  const fieldToggleMatch = chunk.match(
    /operationName:\"ArticleEntityResultByRestId\"[\s\S]*?fieldToggles:\[(.*?)\]/
  );

  const featureSwitches = parseStringList(featureMatch?.[1]);
  const fieldToggles = parseStringList(fieldToggleMatch?.[1]);

  return {
    queryId: queryIdMatch?.[1] ?? FALLBACK_QUERY_ID,
    featureSwitches: featureSwitches.length > 0 ? featureSwitches : FALLBACK_FEATURE_SWITCHES,
    fieldToggles: fieldToggles.length > 0 ? fieldToggles : FALLBACK_FIELD_TOGGLES,
    html,
  };
}

function resolveMainChunkHash(html: string): string | null {
  const match = html.match(/main\\.([a-z0-9]+)\\.js/);
  return match?.[1] ?? null;
}

function resolveApiChunkHash(html: string): string | null {
  const match = html.match(/api:\"([a-zA-Z0-9_-]+)\"/);
  return match?.[1] ?? null;
}

async function resolveTweetDetailQueryInfo(userAgent: string): Promise<ArticleQueryInfo> {
  const html = await fetchHomeHtml(userAgent);
  const apiHash = resolveApiChunkHash(html);
  if (!apiHash) {
    return {
      queryId: FALLBACK_TWEET_DETAIL_QUERY_ID,
      featureSwitches: FALLBACK_TWEET_DETAIL_FEATURE_SWITCHES,
      fieldToggles: FALLBACK_TWEET_DETAIL_FIELD_TOGGLES,
      html,
    };
  }

  const chunkUrl = `https://abs.twimg.com/responsive-web/client-web/api.${apiHash}a.js`;
  const chunk = await fetchText(chunkUrl, {
    headers: {
      "user-agent": userAgent,
    },
  });

  const queryIdMatch = chunk.match(/queryId:\"([^\"]+)\",operationName:\"TweetDetail\"/);
  const featureMatch = chunk.match(
    /operationName:\"TweetDetail\"[\s\S]*?featureSwitches:\[(.*?)\]/
  );
  const fieldToggleMatch = chunk.match(
    /operationName:\"TweetDetail\"[\s\S]*?fieldToggles:\[(.*?)\]/
  );

  const featureSwitches = parseStringList(featureMatch?.[1]);
  const fieldToggles = parseStringList(fieldToggleMatch?.[1]);

  return {
    queryId: queryIdMatch?.[1] ?? FALLBACK_TWEET_DETAIL_QUERY_ID,
    featureSwitches: featureSwitches.length > 0 ? featureSwitches : FALLBACK_TWEET_DETAIL_FEATURE_SWITCHES,
    fieldToggles: fieldToggles.length > 0 ? fieldToggles : FALLBACK_TWEET_DETAIL_FIELD_TOGGLES,
    html,
  };
}

function buildTweetDetailFieldToggleMap(keys: string[]): Record<string, boolean> {
  const toggles = buildFieldToggleMap(keys);
  if (Object.prototype.hasOwnProperty.call(toggles, "withArticlePlainText")) {
    toggles.withArticlePlainText = false;
  }
  if (Object.prototype.hasOwnProperty.call(toggles, "withGrokAnalyze")) {
    toggles.withGrokAnalyze = false;
  }
  if (Object.prototype.hasOwnProperty.call(toggles, "withDisallowedReplyControls")) {
    toggles.withDisallowedReplyControls = false;
  }
  return toggles;
}

async function resolveTweetQueryInfo(userAgent: string): Promise<ArticleQueryInfo> {
  const html = await fetchHomeHtml(userAgent);
  const mainHash = resolveMainChunkHash(html);
  if (!mainHash) {
    return {
      queryId: FALLBACK_TWEET_QUERY_ID,
      featureSwitches: FALLBACK_TWEET_FEATURE_SWITCHES,
      fieldToggles: FALLBACK_TWEET_FIELD_TOGGLES,
      html,
    };
  }

  const chunkUrl = `https://abs.twimg.com/responsive-web/client-web/main.${mainHash}.js`;
  const chunk = await fetchText(chunkUrl, {
    headers: {
      "user-agent": userAgent,
    },
  });

  const queryIdMatch = chunk.match(/queryId:\"([^\"]+)\",operationName:\"TweetResultByRestId\"/);
  const featureMatch = chunk.match(
    /operationName:\"TweetResultByRestId\"[\s\S]*?featureSwitches:\[(.*?)\]/
  );
  const fieldToggleMatch = chunk.match(
    /operationName:\"TweetResultByRestId\"[\s\S]*?fieldToggles:\[(.*?)\]/
  );

  const featureSwitches = parseStringList(featureMatch?.[1]);
  const fieldToggles = parseStringList(fieldToggleMatch?.[1]);

  return {
    queryId: queryIdMatch?.[1] ?? FALLBACK_TWEET_QUERY_ID,
    featureSwitches: featureSwitches.length > 0 ? featureSwitches : FALLBACK_TWEET_FEATURE_SWITCHES,
    fieldToggles: fieldToggles.length > 0 ? fieldToggles : FALLBACK_TWEET_FIELD_TOGGLES,
    html,
  };
}

async function fetchTweetResult(
  tweetId: string,
  cookieMap: Record<string, string>,
  userAgent: string,
  bearerToken: string
): Promise<unknown> {
  const queryInfo = await resolveTweetQueryInfo(userAgent);
  const features = buildFeatureMap(queryInfo.html, queryInfo.featureSwitches);
  const fieldToggles = buildTweetFieldToggleMap(queryInfo.fieldToggles);

  const url = new URL(`https://x.com/i/api/graphql/${queryInfo.queryId}/TweetResultByRestId`);
  url.searchParams.set(
    "variables",
    JSON.stringify({
      tweetId,
      withCommunity: false,
      includePromotedContent: false,
      withVoice: true,
    })
  );
  if (Object.keys(features).length > 0) {
    url.searchParams.set("features", JSON.stringify(features));
  }
  if (Object.keys(fieldToggles).length > 0) {
    url.searchParams.set("fieldToggles", JSON.stringify(fieldToggles));
  }

  const response = await fetch(url.toString(), {
    headers: buildRequestHeaders(cookieMap, userAgent, bearerToken),
  });

  const text = await response.text();
  if (!response.ok) {
    throw new Error(`X API error (${response.status}): ${text.slice(0, 400)}`);
  }

  try {
    return JSON.parse(text);
  } catch (error) {
    throw new Error(`Failed to parse response JSON: ${error instanceof Error ? error.message : String(error)}`);
  }
}

export async function fetchTweetDetail(
  tweetId: string,
  cookieMap: Record<string, string>,
  cursor?: string
): Promise<unknown> {
  const userAgent = process.env.X_USER_AGENT?.trim() || DEFAULT_USER_AGENT;
  const bearerToken = process.env.X_BEARER_TOKEN?.trim() || DEFAULT_BEARER_TOKEN;
  const queryInfo = await resolveTweetDetailQueryInfo(userAgent);
  const features = buildFeatureMap(
    queryInfo.html,
    queryInfo.featureSwitches,
    FALLBACK_TWEET_DETAIL_FEATURE_DEFAULTS
  );
  const fieldToggles = buildTweetDetailFieldToggleMap(queryInfo.fieldToggles);

  const url = new URL(`https://x.com/i/api/graphql/${queryInfo.queryId}/TweetDetail`);
  url.searchParams.set(
    "variables",
    JSON.stringify({
      focalTweetId: tweetId,
      cursor,
      referrer: cursor ? "tweet" : undefined,
      with_rux_injections: false,
      includePromotedContent: true,
      withCommunity: true,
      withQuickPromoteEligibilityTweetFields: true,
      withBirdwatchNotes: true,
      withVoice: true,
      withV2Timeline: true,
      withDownvotePerspective: false,
      withReactionsMetadata: false,
      withReactionsPerspective: false,
      withSuperFollowsTweetFields: false,
      withSuperFollowsUserFields: false,
    })
  );
  if (Object.keys(features).length > 0) {
    url.searchParams.set("features", JSON.stringify(features));
  }
  if (Object.keys(fieldToggles).length > 0) {
    url.searchParams.set("fieldToggles", JSON.stringify(fieldToggles));
  }

  const response = await fetch(url.toString(), {
    headers: buildRequestHeaders(cookieMap, userAgent, bearerToken),
  });

  const text = await response.text();
  if (!response.ok) {
    throw new Error(`X API error (${response.status}): ${text.slice(0, 400)}`);
  }

  try {
    return JSON.parse(text);
  } catch (error) {
    throw new Error(`Failed to parse response JSON: ${error instanceof Error ? error.message : String(error)}`);
  }
}

async function fetchArticleEntityById(
  articleEntityId: string,
  cookieMap: Record<string, string>,
  userAgent: string,
  bearerToken: string
): Promise<unknown> {
  const queryInfo = await resolveArticleQueryInfo(userAgent);
  const features = buildFeatureMap(queryInfo.html, queryInfo.featureSwitches);
  const fieldToggles = buildFieldToggleMap(queryInfo.fieldToggles);

  const url = new URL(`https://x.com/i/api/graphql/${queryInfo.queryId}/ArticleEntityResultByRestId`);
  url.searchParams.set("variables", JSON.stringify({ articleEntityId }));
  if (Object.keys(features).length > 0) {
    url.searchParams.set("features", JSON.stringify(features));
  }
  if (Object.keys(fieldToggles).length > 0) {
    url.searchParams.set("fieldToggles", JSON.stringify(fieldToggles));
  }

  const response = await fetch(url.toString(), {
    headers: buildRequestHeaders(cookieMap, userAgent, bearerToken),
  });

  const text = await response.text();
  if (!response.ok) {
    throw new Error(`X API error (${response.status}): ${text.slice(0, 400)}`);
  }

  try {
    return JSON.parse(text);
  } catch (error) {
    throw new Error(`Failed to parse response JSON: ${error instanceof Error ? error.message : String(error)}`);
  }
}

export async function fetchXArticle(
  articleId: string,
  cookieMap: Record<string, string>,
  raw: boolean
): Promise<unknown> {
  const userAgent = process.env.X_USER_AGENT?.trim() || DEFAULT_USER_AGENT;
  const bearerToken = process.env.X_BEARER_TOKEN?.trim() || DEFAULT_BEARER_TOKEN;

  const tweetPayload = await fetchTweetResult(articleId, cookieMap, userAgent, bearerToken);
  if (raw) {
    return tweetPayload;
  }

  const articleFromTweet = extractArticleFromTweet(tweetPayload);
  if (isNonEmptyObject(articleFromTweet)) {
    return articleFromTweet;
  }

  const articlePayload = await fetchArticleEntityById(articleId, cookieMap, userAgent, bearerToken);
  const articleFromEntity = extractArticleFromEntity(articlePayload);
  if (isNonEmptyObject(articleFromEntity)) {
    return articleFromEntity;
  }
  return articleFromEntity ?? articlePayload;
}

export async function fetchXTweet(
  tweetId: string,
  cookieMap: Record<string, string>,
  raw: boolean
): Promise<unknown> {
  const userAgent = process.env.X_USER_AGENT?.trim() || DEFAULT_USER_AGENT;
  const bearerToken = process.env.X_BEARER_TOKEN?.trim() || DEFAULT_BEARER_TOKEN;

  const tweetPayload = await fetchTweetResult(tweetId, cookieMap, userAgent, bearerToken);
  if (raw) {
    return tweetPayload;
  }

  const tweet = extractTweetFromPayload(tweetPayload);
  if (isNonEmptyObject(tweet)) {
    return tweet;
  }
  return tweet ?? tweetPayload;
}
