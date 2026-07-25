import { fetchTweetDetail } from "./graphql.js";

type TweetEntry = {
  tweet: any;
  user?: any;
};

type ParsedEntries = {
  entries: TweetEntry[];
  moreCursor?: string;
  topCursor?: string;
  bottomCursor?: string;
};

type ThreadResult = {
  requestedId: string;
  rootId: string;
  tweets: any[];
  totalTweets: number;
  user?: any;
  responses?: unknown[];
};

function unwrapTweetResult(result: any): any {
  if (!result) return null;
  if (result.__typename === "TweetWithVisibilityResults" && result.tweet) {
    return result.tweet;
  }
  return result;
}

function extractTweetEntry(itemContent: any): TweetEntry | null {
  const result = itemContent?.tweet_results?.result;
  if (!result) return null;
  const resolved = unwrapTweetResult(result?.tweet ?? result);
  if (!resolved) return null;
  const user = resolved?.core?.user_results?.result?.legacy;
  return { tweet: resolved, user };
}

function parseInstruction(instruction?: any): ParsedEntries {
  const { entries: entities, moduleItems } = instruction || {};
  const entries: TweetEntry[] = [];
  let moreCursor: string | undefined;
  let topCursor: string | undefined;
  let bottomCursor: string | undefined;

  const parseItems = (items: any[]) => {
    items?.forEach((item) => {
      const itemContent = item?.item?.itemContent ?? item?.itemContent;
      if (!itemContent) {
        return;
      }

      if (
        itemContent.cursorType &&
        ["ShowMore", "ShowMoreThreads"].includes(itemContent.cursorType) &&
        itemContent.itemType === "TimelineTimelineCursor"
      ) {
        moreCursor = itemContent.value;
        return;
      }

      const entry = extractTweetEntry(itemContent);
      if (entry) {
        entries.push(entry);
      }
    });
  };

  if (moduleItems) {
    parseItems(moduleItems);
  }

  for (const entity of entities ?? []) {
    if (entity?.content?.clientEventInfo?.component === "you_might_also_like") {
      continue;
    }

    const { itemContent, items, cursorType, entryType, value } = entity?.content ?? {};
    if (cursorType === "Bottom" && entryType === "TimelineTimelineCursor") {
      bottomCursor = value;
    }

    if (
      itemContent?.cursorType === "Bottom" &&
      itemContent?.itemType === "TimelineTimelineCursor"
    ) {
      bottomCursor = bottomCursor ?? itemContent?.value;
    }

    if (cursorType === "Top" && entryType === "TimelineTimelineCursor") {
      topCursor = topCursor ?? value;
    }

    if (itemContent) {
      const entry = extractTweetEntry(itemContent);
      if (entry) {
        entries.push(entry);
      }
      if (
        itemContent.cursorType &&
        ["ShowMore", "ShowMoreThreads"].includes(itemContent.cursorType) &&
        itemContent.itemType === "TimelineTimelineCursor"
      ) {
        moreCursor = moreCursor ?? itemContent.value;
      }

      if (itemContent.cursorType === "Top" && itemContent.itemType === "TimelineTimelineCursor") {
        topCursor = topCursor ?? itemContent.value;
      }
    }

    if (items) {
      parseItems(items);
    }
  }

  return { entries, moreCursor, topCursor, bottomCursor };
}

function parseTweetsAndToken(response: any): ParsedEntries {
  const instruction =
    response?.data?.threaded_conversation_with_injections_v2?.instructions?.find(
      (ins: any) => ins?.type === "TimelineAddEntries" || ins?.type === "TimelineAddToModule"
    ) ??
    response?.data?.threaded_conversation_with_injections?.instructions?.find(
      (ins: any) => ins?.type === "TimelineAddEntries" || ins?.type === "TimelineAddToModule"
    );

  return parseInstruction(instruction);
}

function toTimestamp(value: string | undefined): number {
  if (!value) return 0;
  const parsed = Date.parse(value);
  return Number.isNaN(parsed) ? 0 : parsed;
}

export async function fetchTweetThread(
  tweetId: string,
  cookieMap: Record<string, string>,
  includeResponses = false
): Promise<ThreadResult | null> {
  const responses: unknown[] = [];
  const res = await fetchTweetDetail(tweetId, cookieMap);
  if (includeResponses) {
    responses.push(res);
  }

  let { entries, moreCursor, topCursor, bottomCursor } = parseTweetsAndToken(res);
  if (!entries.length) {
    const errorMessage = res?.errors?.[0]?.message;
    if (errorMessage) {
      throw new Error(errorMessage);
    }
    return null;
  }

  let allEntries = entries.slice();
  const root = allEntries.find((entry) => entry.tweet?.legacy?.id_str === tweetId);
  if (!root) {
    throw new Error("Can not fetch the root tweet");
  }

  let rootEntry = root.tweet.legacy;

  const isSameThread = (entry: TweetEntry) => {
    const tweet = entry.tweet?.legacy;
    if (!tweet) return false;
    return (
      tweet.user_id_str === rootEntry.user_id_str &&
      tweet.conversation_id_str === rootEntry.conversation_id_str &&
      (tweet.id_str === rootEntry.id_str ||
        tweet.in_reply_to_user_id_str === rootEntry.user_id_str ||
        tweet.in_reply_to_status_id_str === rootEntry.conversation_id_str ||
        !tweet.in_reply_to_user_id_str)
    );
  };

  const inThread = (items: TweetEntry[]) => items.some(isSameThread);

  let hasThread = inThread(entries);
  let maxRequestCount = 1000;
  let topHasThread = true;

  while (topCursor && topHasThread && maxRequestCount > 0) {
    const newRes = await fetchTweetDetail(tweetId, cookieMap, topCursor);
    if (includeResponses) {
      responses.push(newRes);
    }

    const parsed = parseTweetsAndToken(newRes);
    topHasThread = inThread(parsed.entries);
    topCursor = parsed.topCursor;
    allEntries = parsed.entries.concat(allEntries);
    maxRequestCount--;
  }

  async function checkMoreTweets(focalId: string) {
    while (moreCursor && hasThread && maxRequestCount > 0) {
      const newRes = await fetchTweetDetail(focalId, cookieMap, moreCursor);
      if (includeResponses) {
        responses.push(newRes);
      }

      const parsed = parseTweetsAndToken(newRes);
      moreCursor = parsed.moreCursor;
      bottomCursor = bottomCursor ?? parsed.bottomCursor;

      hasThread = inThread(parsed.entries);
      allEntries = allEntries.concat(parsed.entries);
      maxRequestCount--;
    }

    if (bottomCursor) {
      const newRes = await fetchTweetDetail(focalId, cookieMap, bottomCursor);
      if (includeResponses) {
        responses.push(newRes);
      }

      const parsed = parseTweetsAndToken(newRes);
      allEntries = allEntries.concat(parsed.entries);
      bottomCursor = undefined;
    }
  }

  await checkMoreTweets(tweetId);

  const allThreadEntries = allEntries.filter(
    (entry) => entry.tweet?.legacy?.id_str === tweetId || isSameThread(entry)
  );
  const lastEntity = allThreadEntries[allThreadEntries.length - 1];
  if (lastEntity?.tweet?.legacy?.id_str) {
    const lastRes = await fetchTweetDetail(lastEntity.tweet.legacy.id_str, cookieMap);
    if (includeResponses) {
      responses.push(lastRes);
    }

    const parsed = parseTweetsAndToken(lastRes);
    hasThread = inThread(parsed.entries);
    allEntries = allEntries.concat(parsed.entries);
    moreCursor = parsed.moreCursor;
    bottomCursor = parsed.bottomCursor;
    maxRequestCount--;

    await checkMoreTweets(lastEntity.tweet.legacy.id_str);
  }

  const distinctEntries: TweetEntry[] = [];
  const entriesMap = allEntries.reduce((acc, entry) => {
    const id = entry.tweet?.legacy?.id_str ?? entry.tweet?.rest_id;
    if (id && !acc.has(id)) {
      distinctEntries.push(entry);
      acc.set(id, entry);
    }
    return acc;
  }, new Map<string, TweetEntry>());
  allEntries = distinctEntries;

  while (rootEntry.in_reply_to_status_id_str) {
    const parent = entriesMap.get(rootEntry.in_reply_to_status_id_str)?.tweet?.legacy;
    if (
      parent &&
      parent.user_id_str === rootEntry.user_id_str &&
      parent.conversation_id_str === rootEntry.conversation_id_str &&
      parent.id_str !== rootEntry.id_str
    ) {
      rootEntry = parent;
    } else {
      break;
    }
  }

  allEntries = allEntries.sort((a, b) => {
    const aTime = toTimestamp(a.tweet?.legacy?.created_at);
    const bTime = toTimestamp(b.tweet?.legacy?.created_at);
    return aTime - bTime;
  });

  const rootIndex = allEntries.findIndex(
    (entry) => entry.tweet?.legacy?.id_str === rootEntry.id_str
  );
  if (rootIndex > 0) {
    allEntries = allEntries.slice(rootIndex);
  }

  const threadEntries = allEntries.filter(
    (entry) => entry.tweet?.legacy?.id_str === tweetId || isSameThread(entry)
  );

  if (!threadEntries.length) {
    return null;
  }

  const tweets = threadEntries.map((entry) => entry.tweet);
  const user = threadEntries[0].user ?? threadEntries[0].tweet?.core?.user_results?.result?.legacy;
  const result: ThreadResult = {
    requestedId: tweetId,
    rootId: rootEntry.id_str ?? tweetId,
    tweets,
    totalTweets: tweets.length,
    user,
  };

  if (includeResponses) {
    result.responses = responses;
  }

  return result;
}
