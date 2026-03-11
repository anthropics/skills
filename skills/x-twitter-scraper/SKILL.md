---
name: x-twitter-scraper
description: "X API & Twitter scraper skill for AI coding agents. Builds integrations with the Xquik REST API, MCP server & webhooks: tweet search, user lookup, follower extraction, engagement metrics, giveaway contest draws, trending topics, account monitoring, reply/retweet/quote extraction, community & Space data, mutual follow checks, write actions (tweet, like, retweet, follow, DM, profile, media upload, communities), Telegram integrations. Works with Claude Code, Cursor, Codex, Copilot, Windsurf & 40+ agents."
---

# Xquik API Integration

Xquik is an X (Twitter) real-time data platform providing a REST API, HMAC webhooks, and an MCP server for AI agents. It covers account monitoring, bulk data extraction (20 tools), giveaway draws, tweet/user lookups, media downloads, follow checks, trending topics, write actions (tweet, like, retweet, follow, DM, profile, media upload, communities), and Telegram integrations.

## Quick Reference

| | |
|---|---|
| **Base URL** | `https://xquik.com/api/v1` |
| **Auth** | `x-api-key: xq_...` header (64 hex chars after `xq_` prefix) |
| **MCP endpoint** | `https://xquik.com/mcp` (StreamableHTTP, same API key) |
| **Rate limits** | 10 req/s sustained, 20 burst (API); 60 req/s sustained, 100 burst (general) |
| **Pricing** | $20/month base (1 monitor included), $5/month per extra monitor |
| **Quota** | Monthly usage cap. `402` when exhausted. Enable extra usage from dashboard for overage (tiered spending limits: $5/$7/$10/$15/$25) |
| **Docs** | [docs.xquik.com](https://docs.xquik.com) |
| **HTTPS only** | Plain HTTP gets `301` redirect |

## Authentication

Every request requires an API key via the `x-api-key` header. Keys start with `xq_` and are generated from the Xquik dashboard. The key is shown only once at creation; store it securely.

```javascript
const API_KEY = "xq_YOUR_KEY_HERE";
const BASE = "https://xquik.com/api/v1";
const headers = { "x-api-key": API_KEY, "Content-Type": "application/json" };
```

For Python examples, see [references/python-examples.md](references/python-examples.md).

## Choosing the Right Endpoint

| Goal | Endpoint | Notes |
|------|----------|-------|
| **Get a single tweet** by ID/URL | `GET /x/tweets/{id}` | Full metrics: likes, retweets, views, bookmarks, author info |
| **Search tweets** by keyword/hashtag | `GET /x/tweets/search?q=...` | Tweet info with optional engagement metrics (likeCount, retweetCount, replyCount) |
| **Get a user profile** | `GET /x/users/{username}` | Name, bio, follower/following counts, profile picture, location, created date, statuses count |
| **Check follow relationship** | `GET /x/followers/check?source=A&target=B` | Both directions |
| **Get trending topics** | `GET /trends?woeid=1` | Regional trends by WOEID. Metered |
| **Get radar (trending news)** | `GET /radar?source=hacker_news` | Free, 7 sources: Google Trends, Hacker News, Polymarket, TrustMRR, Wikipedia, GitHub, Reddit |
| **Monitor an X account** | `POST /monitors` | Track tweets, replies, quotes, retweets, follower changes |
| **Update monitor event types** | `PATCH /monitors/{id}` | Change subscribed events or pause/resume |
| **Poll for events** | `GET /events` | Cursor-paginated, filter by monitorId/eventType |
| **Receive events in real time** | `POST /webhooks` | HMAC-signed delivery to your HTTPS endpoint |
| **Update webhook** | `PATCH /webhooks/{id}` | Change URL, event types, or pause/resume |
| **Run a giveaway draw** | `POST /draws` | Pick random winners from tweet replies |
| **Download tweet media** | `POST /x/media/download` | Single (`tweetInput`) or bulk (`tweetIds[]`, up to 50). Returns gallery URL. First download metered, cached free |
| **Extract bulk data** | `POST /extractions` | 20 tool types, always estimate cost first |
| **Check account/usage** | `GET /account` | Plan status, monitors, usage percent |
| **Link your X identity** | `PUT /account/x-identity` | Required for own-account detection in style analysis |
| **Analyze tweet style** | `POST /styles` | Cache recent tweets for style reference |
| **Save custom style** | `PUT /styles/{username}` | Save custom style from tweet texts (free) |
| **Get cached style** | `GET /styles/{username}` | Retrieve previously cached tweet style |
| **Compare styles** | `GET /styles/compare?username1=A&username2=B` | Side-by-side comparison of two cached styles |
| **Get tweet performance** | `GET /styles/{username}/performance` | Live engagement metrics for cached tweets |
| **Save a tweet draft** | `POST /drafts` | Store drafts for later |
| **List/manage drafts** | `GET /drafts`, `DELETE /drafts/{id}` | Retrieve and delete saved drafts |
| **Compose a tweet** | `POST /compose` | 3-step workflow (compose, refine, score). Free, algorithm-backed |
| **Connect an X account** | `POST /x/accounts` | Credentials encrypted at rest. Required for write actions |
| **List connected accounts** | `GET /x/accounts` | Free |
| **Re-authenticate account** | `POST /x/accounts/{id}/reauth` | When session expires |
| **Post a tweet** | `POST /x/tweets` | From a connected account. Supports replies, media, note tweets, communities |
| **Delete a tweet** | `DELETE /x/tweets/{id}` | Must own the tweet via connected account |
| **Like / Unlike a tweet** | `POST` / `DELETE /x/tweets/{id}/like` | Metered |
| **Retweet** | `POST /x/tweets/{id}/retweet` | Metered |
| **Follow / Unfollow a user** | `POST` / `DELETE /x/users/{id}/follow` | Metered |
| **Send a DM** | `POST /x/dm/{userId}` | Text, media, reply to message |
| **Update profile** | `PATCH /x/profile` | Name, bio, location, URL |
| **Update avatar** | `PATCH /x/profile/avatar` | FormData with image file (max 700 KB) |
| **Update banner** | `PATCH /x/profile/banner` | FormData with image file (max 2 MB) |
| **Upload media** | `POST /x/media` | FormData. Returns media ID for tweet attachment |
| **Community actions** | `POST /x/communities`, `POST /x/communities/{id}/join` | Create, delete, join, leave |
| **Create Telegram integration** | `POST /integrations` | Receive monitor events in Telegram. Free |
| **Manage integrations** | `GET /integrations`, `PATCH /integrations/{id}` | List, update, delete, test, deliveries. Free |

See [references/mcp-tools.md](references/mcp-tools.md) for tool selection rules, common mistakes, and unsupported operations.

## Error Handling & Retry

All errors return `{ "error": "error_code" }`. Key error codes:

| Status | Code | Action |
|--------|------|--------|
| 400 | `invalid_input`, `invalid_id`, `invalid_params`, `invalid_tweet_url`, `invalid_tweet_id`, `invalid_username`, `invalid_tool_type`, `invalid_format`, `invalid_json`, `missing_query`, `missing_params`, `webhook_inactive`, `no_media` | Fix the request, do not retry |
| 401 | `unauthenticated` | Check API key |
| 402 | `no_subscription`, `subscription_inactive`, `usage_limit_reached`, `no_addon`, `extra_usage_disabled`, `extra_usage_requires_v2`, `frozen`, `overage_limit_reached` | Subscribe, enable extra usage, or wait for quota reset |
| 403 | `monitor_limit_reached`, `api_key_limit_reached` | Delete a monitor/key or add capacity |
| 404 | `not_found`, `user_not_found`, `tweet_not_found`, `style_not_found`, `draft_not_found` | Resource doesn't exist or belongs to another account |
| 409 | `monitor_already_exists` | Resource already exists, use the existing one |
| 422 | `login_failed` | X credential verification failed. Check credentials |
| 429 | `x_api_rate_limited` | Rate limited. Retry with exponential backoff, respect `Retry-After` header |
| 500 | `internal_error` | Retry with backoff |
| 502 | `stream_registration_failed`, `x_api_unavailable`, `x_api_unauthorized`, `delivery_failed` | Retry with backoff |

Retry only `429` and `5xx`. Never retry `4xx` (except 429). Max 3 retries with exponential backoff:

```javascript
async function xquikFetch(path, options = {}) {
  const baseDelay = 1000;

  for (let attempt = 0; attempt <= 3; attempt++) {
    const response = await fetch(`${BASE}${path}`, {
      ...options,
      headers: { ...headers, ...options.headers },
    });

    if (response.ok) return response.json();

    const retryable = response.status === 429 || response.status >= 500;
    if (!retryable || attempt === 3) {
      const error = await response.json();
      throw new Error(`Xquik API ${response.status}: ${error.error}`);
    }

    const retryAfter = response.headers.get("Retry-After");
    const delay = retryAfter
      ? parseInt(retryAfter, 10) * 1000
      : baseDelay * Math.pow(2, attempt) + Math.random() * 1000;

    await new Promise((resolve) => setTimeout(resolve, delay));
  }
}
```

## Cursor Pagination

Events, draws, extractions, and extraction results use cursor-based pagination. When more results exist, the response includes `hasMore: true` and a `nextCursor` string. Pass `nextCursor` as the `after` query parameter.

```javascript
async function fetchAllPages(path, dataKey) {
  const results = [];
  let cursor;

  while (true) {
    const params = new URLSearchParams({ limit: "100" });
    if (cursor) params.set("after", cursor);

    const data = await xquikFetch(`${path}?${params}`);
    results.push(...data[dataKey]);

    if (!data.hasMore) break;
    cursor = data.nextCursor;
  }

  return results;
}
```

Cursors are opaque strings. Never decode or construct them manually.

## Extraction Tools (20 Types)

Extractions run bulk data collection jobs. The complete workflow: estimate cost, create job, retrieve results, optionally export.

### Tool Types and Required Parameters

| Tool Type | Required Field | Description |
|-----------|---------------|-------------|
| `reply_extractor` | `targetTweetId` | Users who replied to a tweet |
| `repost_extractor` | `targetTweetId` | Users who retweeted a tweet |
| `quote_extractor` | `targetTweetId` | Users who quote-tweeted a tweet |
| `thread_extractor` | `targetTweetId` | All tweets in a thread |
| `article_extractor` | `targetTweetId` | Article content linked in a tweet |
| `follower_explorer` | `targetUsername` | Followers of an account |
| `following_explorer` | `targetUsername` | Accounts followed by a user |
| `verified_follower_explorer` | `targetUsername` | Verified followers of an account |
| `mention_extractor` | `targetUsername` | Tweets mentioning an account |
| `post_extractor` | `targetUsername` | Posts from an account |
| `community_extractor` | `targetCommunityId` | Members of a community |
| `community_moderator_explorer` | `targetCommunityId` | Moderators of a community |
| `community_post_extractor` | `targetCommunityId` | Posts from a community |
| `community_search` | `targetCommunityId` + `searchQuery` | Search posts within a community |
| `list_member_extractor` | `targetListId` | Members of a list |
| `list_post_extractor` | `targetListId` | Posts from a list |
| `list_follower_explorer` | `targetListId` | Followers of a list |
| `space_explorer` | `targetSpaceId` | Participants of a Space |
| `people_search` | `searchQuery` | Search for users by keyword |
| `tweet_search_extractor` | `searchQuery` | Search and extract tweets by keyword or hashtag (bulk, up to 1,000) |

### Complete Extraction Workflow

```javascript
// Step 1: Estimate cost before running (pass resultsLimit if you only need a sample)
const estimate = await xquikFetch("/extractions/estimate", {
  method: "POST",
  body: JSON.stringify({
    toolType: "follower_explorer",
    targetUsername: "elonmusk",
    resultsLimit: 1000, // optional: limit to 1,000 results instead of all
  }),
});
// Response: { allowed: true, estimatedResults: 195000000, usagePercent: 12, projectedPercent: 98 }

if (!estimate.allowed) {
  console.log("Extraction would exceed monthly quota");
  return;
}

// Step 2: Create extraction job (pass same resultsLimit to match estimate)
const job = await xquikFetch("/extractions", {
  method: "POST",
  body: JSON.stringify({
    toolType: "follower_explorer",
    targetUsername: "elonmusk",
    resultsLimit: 1000,
  }),
});
// Response: { id: "77777", toolType: "follower_explorer", status: "completed", totalResults: 195000 }

// Step 3: Poll until complete (large jobs may return status "running")
while (job.status === "pending" || job.status === "running") {
  await new Promise((r) => setTimeout(r, 2000));
  job = await xquikFetch(`/extractions/${job.id}`);
}

// Step 4: Retrieve paginated results (up to 1,000 per page)
let cursor;
const allResults = [];

while (true) {
  const path = `/extractions/${job.id}${cursor ? `?after=${cursor}` : ""}`;
  const page = await xquikFetch(path);
  allResults.push(...page.results);
  // Each result: { xUserId, xUsername, xDisplayName, xFollowersCount, xVerified, xProfileImageUrl }

  if (!page.hasMore) break;
  cursor = page.nextCursor;
}

// Step 5: Export as CSV/XLSX/Markdown (50,000 row limit)
const exportUrl = `${BASE}/extractions/${job.id}/export?format=csv`;
const csvResponse = await fetch(exportUrl, { headers });
const csvData = await csvResponse.text();
```

### Orchestrating Multiple Extractions

When building applications that combine multiple extraction tools (e.g., market research), run them sequentially and respect rate limits:

```javascript
async function marketResearchPipeline(username) {
  // 1. Get user profile
  const user = await xquikFetch(`/x/users/${username}`);

  // 2. Extract their recent posts
  const postsJob = await xquikFetch("/extractions", {
    method: "POST",
    body: JSON.stringify({ toolType: "post_extractor", targetUsername: username }),
  });

  // 3. Search for related conversations
  const tweets = await xquikFetch(`/x/tweets/search?q=from:${username}`);

  // 4. For top tweets, extract replies for sentiment analysis
  for (const tweet of tweets.tweets.slice(0, 5)) {
    const estimate = await xquikFetch("/extractions/estimate", {
      method: "POST",
      body: JSON.stringify({ toolType: "reply_extractor", targetTweetId: tweet.id }),
    });

    if (estimate.allowed) {
      const repliesJob = await xquikFetch("/extractions", {
        method: "POST",
        body: JSON.stringify({ toolType: "reply_extractor", targetTweetId: tweet.id }),
      });
      // Process replies...
    }
  }

  // 5. Get trending topics for context
  const trends = await xquikFetch("/trends?woeid=1");

  return { user, posts: postsJob, tweets, trends };
}
```

## Giveaway Draws

Run transparent, auditable giveaway draws from tweet replies with configurable filters.

### Create Draw Request

`POST /draws` with a `tweetUrl` (required) and optional filters:

| Field | Type | Description |
|-------|------|-------------|
| `tweetUrl` | string | **Required.** Full tweet URL: `https://x.com/user/status/ID` |
| `winnerCount` | number | Winners to select (default 1) |
| `backupCount` | number | Backup winners to select |
| `uniqueAuthorsOnly` | boolean | Count only one entry per author |
| `mustRetweet` | boolean | Require participants to have retweeted |
| `mustFollowUsername` | string | Username participants must follow |
| `filterMinFollowers` | number | Minimum follower count |
| `filterAccountAgeDays` | number | Minimum account age in days |
| `filterLanguage` | string | Language code (e.g., `"en"`) |
| `requiredKeywords` | string[] | Words that must appear in the reply |
| `requiredHashtags` | string[] | Hashtags that must appear (e.g., `["#giveaway"]`) |
| `requiredMentions` | string[] | Usernames that must be mentioned (e.g., `["@xquik"]`) |

### Complete Draw Workflow

```javascript
// Step 1: Create draw with filters
const draw = await xquikFetch("/draws", {
  method: "POST",
  body: JSON.stringify({
    tweetUrl: "https://x.com/burakbayir/status/1893456789012345678",
    winnerCount: 3,
    backupCount: 2,
    uniqueAuthorsOnly: true,
    mustRetweet: true,
    mustFollowUsername: "burakbayir",
    filterMinFollowers: 50,
    filterAccountAgeDays: 30,
    filterLanguage: "en",
    requiredHashtags: ["#giveaway"],
  }),
});
// Response:
// {
//   id: "42",
//   tweetId: "1893456789012345678",
//   tweetUrl: "https://x.com/burakbayir/status/1893456789012345678",
//   tweetText: "Giveaway! RT + Follow to enter...",
//   tweetAuthorUsername: "burakbayir",
//   tweetLikeCount: 5200,
//   tweetRetweetCount: 3100,
//   tweetReplyCount: 890,
//   tweetQuoteCount: 45,
//   status: "completed",
//   totalEntries: 890,
//   validEntries: 312,
//   createdAt: "2026-02-24T10:00:00.000Z",
//   drawnAt: "2026-02-24T10:01:00.000Z"
// }

// Step 2: Get draw details with winners
const details = await xquikFetch(`/draws/${draw.id}`);
// details.winners: [
//   { position: 1, authorUsername: "winner1", tweetId: "...", isBackup: false },
//   { position: 2, authorUsername: "winner2", tweetId: "...", isBackup: false },
//   { position: 3, authorUsername: "winner3", tweetId: "...", isBackup: false },
//   { position: 4, authorUsername: "backup1", tweetId: "...", isBackup: true },
//   { position: 5, authorUsername: "backup2", tweetId: "...", isBackup: true },
// ]

// Step 3: Export results
const exportUrl = `${BASE}/draws/${draw.id}/export?format=csv`;
```

## Webhook Event Handling

Webhooks deliver events to your HTTPS endpoint with HMAC-SHA256 signatures. Each delivery is a POST with `X-Xquik-Signature` header and JSON body containing `eventType`, `username`, and `data`.

### Webhook Handler (Express)

```javascript
import express from "express";
import { createHmac, timingSafeEqual, createHash } from "node:crypto";

const WEBHOOK_SECRET = process.env.XQUIK_WEBHOOK_SECRET;
const processedHashes = new Set(); // Use Redis/DB in production

function verifySignature(payload, signature, secret) {
  const expected = "sha256=" + createHmac("sha256", secret).update(payload).digest("hex");
  return timingSafeEqual(Buffer.from(expected), Buffer.from(signature));
}

const app = express();

app.post("/webhook", express.raw({ type: "application/json" }), (req, res) => {
  const signature = req.headers["x-xquik-signature"];
  const payload = req.body.toString();

  // 1. Verify HMAC signature (constant-time comparison)
  if (!signature || !verifySignature(payload, signature, WEBHOOK_SECRET)) {
    return res.status(401).send("Invalid signature");
  }

  // 2. Deduplicate (retries can deliver the same event twice)
  const payloadHash = createHash("sha256").update(payload).digest("hex");
  if (processedHashes.has(payloadHash)) {
    return res.status(200).send("Already processed");
  }
  processedHashes.add(payloadHash);

  // 3. Parse and route by event type
  const event = JSON.parse(payload);
  // event.eventType: "tweet.new" | "tweet.reply" | "tweet.quote" | "tweet.retweet" | "follower.gained" | "follower.lost"
  // event.username: monitored account username
  // event.data: tweet data ({ tweetId, text, metrics }) or follower data ({ followerId, followerUsername, followerName, followerFollowersCount, followerVerified })

  // 4. Respond within 10 seconds (process async if slow)
  res.status(200).send("OK");
});

app.listen(3000);
```

For Flask (Python) webhook handler, see [references/python-examples.md](references/python-examples.md#webhook-handler-flask).

Webhook security rules:
- Always verify signature before processing (constant-time comparison)
- Compute HMAC over raw body bytes, not re-serialized JSON
- Respond `200` within 10 seconds; queue slow processing for async
- Deduplicate by payload hash (retries can deliver same event twice)
- Store webhook secret in environment variables, never hardcode
- Retry policy: 5 attempts with exponential backoff on failure

Check delivery status via `GET /webhooks/{id}/deliveries` to monitor successful and failed attempts.

## Real-Time Monitoring Setup

Complete end-to-end: create monitor, register webhook, handle events.

```javascript
// 1. Create monitor
const monitor = await xquikFetch("/monitors", {
  method: "POST",
  body: JSON.stringify({
    username: "elonmusk",
    eventTypes: ["tweet.new", "tweet.reply", "tweet.quote", "follower.gained"],
  }),
});
// Response: { id: "7", username: "elonmusk", xUserId: "44196397", eventTypes: [...], createdAt: "..." }

// 2. Register webhook
const webhook = await xquikFetch("/webhooks", {
  method: "POST",
  body: JSON.stringify({
    url: "https://your-server.com/webhook",
    eventTypes: ["tweet.new", "tweet.reply"],
  }),
});
// IMPORTANT: Save webhook.secret. It is shown only once!

// 3. Poll events (alternative to webhooks)
const events = await xquikFetch("/events?monitorId=7&limit=50");
// Response: { events: [...], hasMore: false }
```

Event types: `tweet.new`, `tweet.quote`, `tweet.reply`, `tweet.retweet`, `follower.gained`, `follower.lost`.

## MCP Server (AI Agents)

The MCP server at `https://xquik.com/mcp` uses a code-execution sandbox model with 2 tools (`explore` + `xquik`). The agent writes async JavaScript arrow functions that run in a sandboxed environment with auth injected automatically. StreamableHTTP transport. API key auth (`x-api-key` header) for CLI/IDE clients; OAuth 2.1 for web clients (Claude.ai, ChatGPT Developer Mode). Supported platforms: Claude.ai, Claude Desktop, Claude Code, ChatGPT (Custom GPT, Agents SDK, Developer Mode), Codex CLI, Cursor, VS Code, Windsurf, OpenCode.

**Legacy v1 server** at `https://xquik.com/mcp/v1` exposes 18 discrete tools with traditional input schemas. All new integrations should use the default v2 server at `/mcp`.

The server also registers 5 guided workflow prompts: `compose-tweet`, `compose-trending-tweet`, `compose-radar-tweet`, `analyze-account`, `run-giveaway`. Use `prompts/list` and `prompts/get` in compatible clients.

For setup configs per platform, read [references/mcp-setup.md](references/mcp-setup.md). For the complete v1 tool reference with input/output schemas, annotations, and selection rules, read [references/mcp-tools.md](references/mcp-tools.md).

### MCP vs REST API

| | MCP Server (v2) | REST API |
|---|------------|----------|
| **Best for** | AI agents, IDE integrations | Custom apps, scripts, backend services |
| **Model** | 2 tools (`explore` + `xquik`) with code-execution sandbox | 76 individual endpoints |
| **Categories** | 9: account, composition, extraction, integrations, media, monitoring, twitter, x-accounts, x-write | Same |
| **User profile** | Full (via `xquik` tool calling REST endpoints) | Full profile |
| **Search results** | Full (via `xquik` tool) | Includes optional engagement metrics |
| **Webhook/monitor update** | Full PATCH via `xquik` tool | PATCH endpoints |
| **Write actions** | Full via `xquik` tool (tweet, like, follow, DM, etc.) | POST/DELETE endpoints |
| **File export** | Not available | CSV, XLSX, Markdown |
| **Unique to REST** | - | API key management, file export (CSV/XLSX/MD), account locale update |

Use the REST API `GET /x/users/{username}` for the complete user profile with `verified`, `location`, `createdAt`, and `statusesCount` fields.

### Workflow Patterns

Common multi-step tool sequences:

- **Set up real-time alerts:** `monitors` (action=add) -> `webhooks` (action=add) -> `webhooks` (action=test)
- **Run a giveaway:** `get-account` (check budget) -> `draws` (action=run)
- **Bulk extraction:** `get-account` (check subscription) -> `extractions` (action=estimate) -> `extractions` (action=run) -> `extractions` (action=get, results)
- **Full tweet analysis:** `lookup-tweet` (metrics) -> `extractions` (action=run) with `thread_extractor` (full thread)
- **Find and analyze user:** `get-user-info` (profile) -> `search-tweets from:username` (recent tweets) -> `lookup-tweet` (metrics on specific tweet)
- **Compose algorithm-optimized tweet:** `compose-tweet` (step=compose) -> AI asks follow-ups -> `compose-tweet` (step=refine) -> AI drafts tweet -> `compose-tweet` (step=score) -> iterate
- **Analyze tweet style:** `styles` (action=analyze, fetch & cache tweets) -> `styles` (action=get, reference) -> `compose-tweet` with `styleUsername`
- **Compare styles:** `styles` (action=analyze) for both accounts -> `styles` (action=compare)
- **Track tweet performance:** `styles` (action=analyze, cache tweets) -> `styles` (action=analyze-performance, live metrics)
- **Save & manage drafts:** `compose-tweet` -> `drafts` (action=save) -> `drafts` (action=list) -> `drafts` (action=get/delete)
- **Download & share media:** `download-media` (returns permanent hosted URLs)
- **Get trending news:** `get-radar` (7 sources, free) -> `compose-tweet` with trending topic
- **Subscribe or manage billing:** `subscribe` (returns Stripe URL)
- **Post a tweet:** connect X account -> `POST /x/tweets` with `account` + `text` (optionally attach media via `POST /x/media` first)
- **Engage with tweets:** `POST /x/tweets/{id}/like`, `POST /x/tweets/{id}/retweet`, `POST /x/users/{id}/follow`
- **Set up Telegram alerts:** `POST /integrations` (type=telegram, chatId, eventTypes) -> `POST /integrations/{id}/test`. Integration event types: `tweet.new`, `tweet.quote`, `tweet.reply`, `tweet.retweet`, `draw.completed`, `extraction.completed`, `extraction.failed`
- **Update avatar/banner:** `PATCH /x/profile/avatar` or `PATCH /x/profile/banner` with FormData image file

## Pricing & Quota

- **Base plan**: $20/month (1 monitor, monthly usage quota)
- **Extra monitors**: $5/month each
- **Per-operation costs**: tweet search $0.003, user profile $0.0036, follower fetch $0.003, verified follower fetch $0.006, follow check $0.02, media download $0.003, article extraction $0.02
- **Free**: account info, monitor/webhook management, radar, extraction history, cost estimates, tweet composition (compose, refine, score), style cache management (list, get, save, delete, compare), drafts, X account management (connect, list, disconnect, reauth), integration management (create, list, update, delete, test)
- **Metered**: tweet search, user lookup, tweet lookup, follow check, media download (first download only, cached free), extractions, draws, style analysis, performance analysis, trends, write actions (tweet, like, retweet, follow, DM, profile, avatar, banner, media upload, communities)
- **Extra usage**: enable from dashboard to continue metered calls beyond included allowance. Tiered spending limits: $5 -> $7 -> $10 -> $15 -> $25 (increases with each paid overage invoice)
- **Quota enforcement**: `402 usage_limit_reached` when included allowance exhausted (or `402 overage_limit_reached` if extra usage is active and spending limit reached)
- **Check usage**: `GET /account` returns `usagePercent` (0-100)

## Conventions

- **IDs are strings.** Bigint values; treat as opaque strings, never parse as numbers
- **Timestamps are ISO 8601 UTC.** Example: `2026-02-24T10:30:00.000Z`
- **Errors return JSON.** Format: `{ "error": "error_code" }`
- **Cursors are opaque.** Pass `nextCursor` as the `after` query parameter, never decode
- Export formats: `csv`, `xlsx`, `md` via `GET /extractions/{id}/export?format=csv` or `GET /draws/{id}/export?format=csv&type=winners`

## Reference Files

For additional detail beyond this guide:

- **`references/mcp-tools.md`**: All 18 legacy v1 MCP tools with input/output schemas, annotations, selection rules, workflow patterns, common mistakes, and unsupported operations
- **`references/api-endpoints.md`**: All REST API endpoints with methods, paths, parameters, and response shapes
- **`references/python-examples.md`**: Python equivalents of all JavaScript examples (retry, extraction, draw, webhook)
- **`references/webhooks.md`**: Extended webhook examples, local testing with ngrok, delivery status monitoring
- **`references/mcp-setup.md`**: MCP server configuration for 10 IDEs and AI agent platforms
- **`references/extractions.md`**: Extraction tool details, export columns
- **`references/types.md`**: TypeScript type definitions for all REST API and MCP output objects
