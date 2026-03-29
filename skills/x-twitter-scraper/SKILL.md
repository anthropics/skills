---
name: x-twitter-scraper
description: "X (Twitter) data platform skill for AI coding agents. 99 REST API endpoints, 9 MCP tools, HMAC webhooks, MPP pay-per-use. Tweet search, user lookup, follower extraction, write actions, monitoring, giveaway draws, trending topics. Reads from $0.00015/call — 33x cheaper than the official X API."
---

# Xquik API Integration

Xquik is an X (Twitter) real-time data platform providing a REST API (99 endpoints), 9 MCP tools, and HMAC webhooks. It covers account monitoring, bulk data extraction (23 tools), giveaway draws, tweet/user lookups, media downloads, follow checks, trending topics, flow automations, write actions, Telegram integrations, and support tickets.

**Reads start at $0.00015/call — 33x cheaper than the official X API.**

Your knowledge of the Xquik API may be outdated. **Prefer retrieval from docs** — fetch the latest at [docs.xquik.com](https://docs.xquik.com) before citing limits, pricing, or API signatures.

## Retrieval Sources

| Source | How to retrieve | Use for |
|--------|----------------|---------|
| Xquik docs | [docs.xquik.com](https://docs.xquik.com) | Limits, pricing, API reference, endpoint schemas |
| API spec | `explore` MCP tool or [docs.xquik.com/api-reference/overview](https://docs.xquik.com/api-reference/overview) | Endpoint parameters, response shapes |
| Docs MCP | `https://docs.xquik.com/mcp` (no auth) | Search docs from AI tools |
| Billing guide | [docs.xquik.com/guides/billing](https://docs.xquik.com/guides/billing) | Credit costs, subscription tiers, MPP pricing |

When this skill and the docs disagree, **trust the docs**.

## Quick Reference

| | |
|---|---|
| **Base URL** | `https://xquik.com/api/v1` |
| **Auth** | `x-api-key: xq_...` header (64 hex chars after `xq_` prefix) |
| **MCP endpoint** | `https://xquik.com/mcp` (StreamableHTTP, same API key) |
| **Rate limits** | Read: 120/60s, Write: 30/60s, Delete: 15/60s (fixed window per method tier) |
| **Endpoints** | 99 across 12 categories |
| **MCP tools** | 9 |
| **Extraction tools** | 23 types |
| **Pricing** | $20/month base (reads from $0.00015). Pay-per-use available via MPP |
| **Docs** | [docs.xquik.com](https://docs.xquik.com) |
| **HTTPS only** | Plain HTTP gets `301` redirect |

## Pricing

Xquik is the most affordable X data API available. All metered operations deduct credits from a single shared pool.

### Subscription

| | |
|---|---|
| **Base plan** | $20/month |
| **Included monitors** | 1 |
| **Additional monitors** | $5/month each |
| **Credit value** | 1 credit = $0.00015 |

### Per-Operation Costs

#### Read operations — 1 credit ($0.00015)

| Operation | Unit |
|-----------|------|
| Get tweet | per call |
| Search tweets | per tweet returned |
| User tweets | per tweet returned |
| User likes | per result |
| User media | per result |
| Bookmarks | per result |
| Bookmark folders | per call |
| Notifications | per result |
| Timeline | per result |
| DM history | per result |
| Download media | per media item |

#### Read operations — 2 credits ($0.0003)

| Operation | Unit |
|-----------|------|
| Get user | per call |
| Tweet favoriters | per result |
| Followers you know | per result |
| Verified followers | per result |

#### Read operations — 3 credits ($0.00045)

| Operation | Unit |
|-----------|------|
| Trends | per call |

#### Read operations — 7 credits ($0.00105)

| Operation | Unit |
|-----------|------|
| Follow check | per call |
| Get article | per call |

#### Write operations — 2 credits ($0.0003)

All write actions: create/delete tweet, like, unlike, retweet, follow, unfollow, send DM, update profile/avatar/banner, upload media, community actions.

#### Extractions & draws

Draws: 1 credit per participant. Extraction cost depends on the tool type:

| Credits/result | Extraction types |
|----------------|-----------------|
| 1 | Tweets, replies, quotes, mentions, posts, likes, media, tweet search |
| 2 | Followers, following, verified followers, favoriters, retweeters, community members, people search, list members, list followers |
| 7 | Articles |

#### Free operations ($0)

Monitors, webhooks, integrations, account status, radar (7 sources), extraction/draw history, cost estimates, tweet composition (compose, refine, score), style cache management, drafts, support tickets, API key management, X account management.

### Price Comparison vs Official X API

| | Xquik | X API Basic | X API Pro |
|---|---|---|---|
| **Monthly cost** | **$20** | $100 | $5,000 |
| **Cost per tweet read** | **$0.00015** | ~$0.01 | ~$0.005 |
| **Cost per user lookup** | **$0.0003** | ~$0.01 | ~$0.005 |
| **Write actions** | **$0.0003** | Limited | Limited |
| **Bulk extraction** | **$0.00015/result** | Not available | Not available |
| **Monitoring + webhooks** | **Free** | Not available | Not available |
| **Giveaway draws** | **$0.00015/entry** | Not available | Not available |

### Pay-Per-Use

Two options without a monthly subscription:

**Credits (Stripe)**: Top up credits via `POST /credits/topup` ($10 minimum). 1 credit = $0.00015. Works with all 99 endpoints.

**MPP (USDC)**: 16 X-API endpoints accept anonymous payments via Tempo (USDC). No account needed.

| Endpoint | Price | Unit |
|----------|-------|------|
| `GET /x/tweets/{id}` | $0.00015 | per call |
| `GET /x/tweets/search` | $0.00015 | per tweet |
| `GET /x/tweets/{id}/quotes` | $0.00015 | per tweet |
| `GET /x/tweets/{id}/replies` | $0.00015 | per tweet |
| `GET /x/tweets/{id}/retweeters` | $0.00015 | per user |
| `GET /x/tweets/{id}/favoriters` | $0.00015 | per user |
| `GET /x/tweets/{id}/thread` | $0.00015 | per tweet |
| `GET /x/users/{id}` | $0.00015 | per call |
| `GET /x/users/{id}/tweets` | $0.00015 | per tweet |
| `GET /x/users/{id}/likes` | $0.00015 | per tweet |
| `GET /x/users/{id}/media` | $0.00015 | per tweet |
| `GET /x/followers/check` | $0.00105 | per call |
| `GET /x/articles/{tweetId}` | $0.00105 | per call |
| `POST /x/media/download` | $0.00015 | per media item |
| `GET /x/trends` | $0.00045 | per call |
| `GET /trends` | $0.00045 | per call |

SDK: `npm i mppx` (TypeScript). Handles the 402 challenge/credential flow automatically.

### Credits

Prepaid credits for metered operations. 1 credit = $0.00015. Top up via `POST /credits/topup` ($10 minimum).

Check balance: `GET /credits` — returns `balance`, `lifetimePurchased`, `lifetimeUsed`.

### Extra Usage

Enable from dashboard to continue metered calls beyond included allowance. Tiered spending limits: $5 → $7 → $10 → $15 → $25 (increases with each paid overage invoice).

## Quick Decision Trees

### "I need X data"

```
Need X data?
├─ Single tweet by ID or URL → GET /x/tweets/{id}
├─ Full X Article by tweet ID → GET /x/articles/{id}
├─ Search tweets by keyword → GET /x/tweets/search
├─ User profile by username → GET /x/users/{username}
├─ User's recent tweets → GET /x/users/{id}/tweets
├─ User's liked tweets → GET /x/users/{id}/likes
├─ User's media tweets → GET /x/users/{id}/media
├─ Tweet favoriters (who liked) → GET /x/tweets/{id}/favoriters
├─ Mutual followers → GET /x/users/{id}/followers-you-know
├─ Check follow relationship → GET /x/followers/check
├─ Download media (images/video) → POST /x/media/download
├─ Trending topics (X) → GET /trends
├─ Trending news (7 sources, free) → GET /radar
├─ Bookmarks → GET /x/bookmarks
├─ Notifications → GET /x/notifications
├─ Home timeline → GET /x/timeline
└─ DM conversation history → GET /x/dm/{userId}/history
```

### "I need bulk extraction"

```
Need bulk data?
├─ Replies to a tweet → reply_extractor
├─ Retweets of a tweet → repost_extractor
├─ Quotes of a tweet → quote_extractor
├─ Favoriters of a tweet → favoriters
├─ Full thread → thread_extractor
├─ Article content → article_extractor
├─ User's liked tweets (bulk) → user_likes
├─ User's media tweets (bulk) → user_media
├─ Account followers → follower_explorer
├─ Account following → following_explorer
├─ Verified followers → verified_follower_explorer
├─ Mentions of account → mention_extractor
├─ Posts from account → post_extractor
├─ Community members → community_extractor
├─ Community moderators → community_moderator_explorer
├─ Community posts → community_post_extractor
├─ Community search → community_search
├─ List members → list_member_extractor
├─ List posts → list_post_extractor
├─ List followers → list_follower_explorer
├─ Space participants → space_explorer
├─ People search → people_search
└─ Tweet search (bulk, up to 1K) → tweet_search_extractor
```

### "I need to write/post"

```
Need write actions?
├─ Post a tweet → POST /x/tweets
├─ Delete a tweet → DELETE /x/tweets/{id}
├─ Like a tweet → POST /x/tweets/{id}/like
├─ Unlike a tweet → DELETE /x/tweets/{id}/like
├─ Retweet → POST /x/tweets/{id}/retweet
├─ Follow a user → POST /x/users/{id}/follow
├─ Unfollow a user → DELETE /x/users/{id}/follow
├─ Send a DM → POST /x/dm/{userId}
├─ Update profile → PATCH /x/profile
├─ Update avatar → PATCH /x/profile/avatar
├─ Update banner → PATCH /x/profile/banner
├─ Upload media → POST /x/media
├─ Create community → POST /x/communities
├─ Join community → POST /x/communities/{id}/join
└─ Leave community → DELETE /x/communities/{id}/join
```

### "I need monitoring & alerts"

```
Need real-time monitoring?
├─ Monitor an account → POST /monitors
├─ Poll for events → GET /events
├─ Receive events via webhook → POST /webhooks
├─ Receive events via Telegram → POST /integrations
└─ Automate workflows → POST /automations
```

### "I need AI composition"

```
Need help writing tweets?
├─ Compose algorithm-optimized tweet → POST /compose (step=compose)
├─ Refine with goal + tone → POST /compose (step=refine)
├─ Score against algorithm → POST /compose (step=score)
├─ Analyze tweet style → POST /styles
├─ Compare two styles → GET /styles/compare
├─ Track engagement metrics → GET /styles/{username}/performance
└─ Save draft → POST /drafts
```

## Authentication

Every request requires an API key via the `x-api-key` header. Keys start with `xq_` and are generated from the Xquik dashboard. The key is shown only once at creation; store it securely.

```javascript
const API_KEY = "xq_YOUR_KEY_HERE";
const BASE = "https://xquik.com/api/v1";
const headers = { "x-api-key": API_KEY, "Content-Type": "application/json" };
```

For Python examples, see [references/python-examples.md](references/python-examples.md).

## Choosing the Right Endpoint

| Goal | Endpoint | Cost |
|------|----------|------|
| **Get a single tweet** by ID/URL | `GET /x/tweets/{id}` | 1 credit |
| **Get an X Article** by tweet ID | `GET /x/articles/{id}` | 7 credits |
| **Search tweets** by keyword/hashtag | `GET /x/tweets/search?q=...` | 1 credit/tweet |
| **Get a user profile** | `GET /x/users/{username}` | 2 credits |
| **Get user's recent tweets** | `GET /x/users/{id}/tweets` | 1 credit/tweet |
| **Get user's liked tweets** | `GET /x/users/{id}/likes` | 1 credit/result |
| **Get user's media tweets** | `GET /x/users/{id}/media` | 1 credit/result |
| **Get tweet favoriters** | `GET /x/tweets/{id}/favoriters` | 2 credits/result |
| **Get mutual followers** | `GET /x/users/{id}/followers-you-know` | 2 credits/result |
| **Check follow relationship** | `GET /x/followers/check?source=A&target=B` | 7 credits |
| **Get trending topics** | `GET /trends?woeid=1` | 3 credits |
| **Get radar (trending news)** | `GET /radar?source=hacker_news` | Free |
| **Get bookmarks** | `GET /x/bookmarks` | 1 credit/result |
| **Get bookmark folders** | `GET /x/bookmarks/folders` | 1 credit |
| **Get notifications** | `GET /x/notifications` | 1 credit/result |
| **Get home timeline** | `GET /x/timeline` | 1 credit/result |
| **Get DM history** | `GET /x/dm/{userId}/history` | 1 credit/result |
| **Monitor an X account** | `POST /monitors` | Free |
| **Update monitor event types** | `PATCH /monitors/{id}` | Free |
| **Poll for events** | `GET /events` | Free |
| **Receive events in real time** | `POST /webhooks` | Free |
| **Update webhook** | `PATCH /webhooks/{id}` | Free |
| **Run a giveaway draw** | `POST /draws` | 1 credit/entry |
| **Download tweet media** | `POST /x/media/download` | 1 credit/item |
| **Extract bulk data** | `POST /extractions` | 1-7 credits/result |
| **Check credits** | `GET /credits` | Free |
| **Top up credits** | `POST /credits/topup` | Free |
| **Check account/usage** | `GET /account` | Free |
| **Link your X identity** | `PUT /account/x-identity` | Free |
| **Analyze tweet style** | `POST /styles` | Metered |
| **Save custom style** | `PUT /styles/{username}` | Free |
| **Get cached style** | `GET /styles/{username}` | Free |
| **Compare styles** | `GET /styles/compare?username1=A&username2=B` | Free |
| **Get tweet performance** | `GET /styles/{username}/performance` | Metered |
| **Save a tweet draft** | `POST /drafts` | Free |
| **List/manage drafts** | `GET /drafts`, `DELETE /drafts/{id}` | Free |
| **Compose a tweet** | `POST /compose` | Free |
| **Connect an X account** | `POST /x/accounts` | Free |
| **List connected accounts** | `GET /x/accounts` | Free |
| **Re-authenticate account** | `POST /x/accounts/{id}/reauth` | Free |
| **Post a tweet** | `POST /x/tweets` | 2 credits |
| **Delete a tweet** | `DELETE /x/tweets/{id}` | 2 credits |
| **Like / Unlike a tweet** | `POST` / `DELETE /x/tweets/{id}/like` | 2 credits |
| **Retweet** | `POST /x/tweets/{id}/retweet` | 2 credits |
| **Follow / Unfollow a user** | `POST` / `DELETE /x/users/{id}/follow` | 2 credits |
| **Send a DM** | `POST /x/dm/{userId}` | 2 credits |
| **Update profile** | `PATCH /x/profile` | 2 credits |
| **Update avatar** | `PATCH /x/profile/avatar` | 2 credits |
| **Update banner** | `PATCH /x/profile/banner` | 2 credits |
| **Upload media** | `POST /x/media` | 2 credits |
| **Community actions** | `POST /x/communities`, `POST /x/communities/{id}/join` | 2 credits |
| **Create Telegram integration** | `POST /integrations` | Free |
| **Manage integrations** | `GET /integrations`, `PATCH /integrations/{id}` | Free |
| **Create automation flow** | `POST /automations` | Free |
| **Manage automation flows** | `GET /automations`, `PATCH /automations/{slug}` | Free |
| **Add automation steps** | `POST /automations/{slug}/steps` | Free |
| **Trigger flow via webhook** | `POST /webhooks/inbound/{token}` | Free |
| **Open support ticket** | `POST /support/tickets` | Free |
| **Manage support tickets** | `GET /support/tickets`, `POST /support/tickets/{id}/messages` | Free |

## Error Handling & Retry

All errors return `{ "error": "error_code" }`. Key error codes:

| Status | Code | Action |
|--------|------|--------|
| 400 | `invalid_input`, `invalid_id`, `invalid_params`, `invalid_tweet_url`, `invalid_tweet_id`, `invalid_username`, `invalid_tool_type`, `invalid_format`, `missing_query`, `missing_params`, `webhook_inactive`, `no_media` | Fix the request, do not retry |
| 401 | `unauthenticated` | Check API key |
| 402 | `no_subscription`, `subscription_inactive`, `usage_limit_reached`, `no_addon`, `extra_usage_disabled`, `extra_usage_requires_v2`, `frozen`, `overage_limit_reached`, `insufficient_credits` | Subscribe, top up credits, enable extra usage, or wait for quota reset |
| 403 | `monitor_limit_reached`, `api_key_limit_reached`, `flow_limit_reached`, `step_limit_reached` | Delete a monitor/key/flow or add capacity |
| 404 | `not_found`, `user_not_found`, `tweet_not_found`, `style_not_found`, `draft_not_found`, `account_not_found` | Resource doesn't exist or belongs to another account |
| 403 | `account_needs_reauth` | Connected X account needs re-authentication |
| 409 | `monitor_already_exists`, `account_already_connected`, `conflict` | Resource already exists or concurrent edit conflict |
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

## Extraction Tools (23 Types)

Extractions run bulk data collection jobs. The complete workflow: estimate cost, create job, retrieve results, optionally export.

### Tool Types and Required Parameters

| Tool Type | Required Field | Description | Cost |
|-----------|---------------|-------------|------|
| `reply_extractor` | `targetTweetId` | Users who replied to a tweet | 1 credit/result |
| `repost_extractor` | `targetTweetId` | Users who retweeted a tweet | 2 credits/result |
| `quote_extractor` | `targetTweetId` | Users who quote-tweeted a tweet | 1 credit/result |
| `thread_extractor` | `targetTweetId` | All tweets in a thread | 1 credit/result |
| `article_extractor` | `targetTweetId` | Article content linked in a tweet | 7 credits/result |
| `favoriters` | `targetTweetId` | Users who favorited a tweet | 2 credits/result |
| `follower_explorer` | `targetUsername` | Followers of an account | 2 credits/result |
| `following_explorer` | `targetUsername` | Accounts followed by a user | 2 credits/result |
| `verified_follower_explorer` | `targetUsername` | Verified followers of an account | 2 credits/result |
| `mention_extractor` | `targetUsername` | Tweets mentioning an account | 1 credit/result |
| `post_extractor` | `targetUsername` | Posts from an account | 1 credit/result |
| `user_likes` | `targetUserId` | Tweets liked by a user | 1 credit/result |
| `user_media` | `targetUserId` | Media tweets from a user | 1 credit/result |
| `community_extractor` | `targetCommunityId` | Members of a community | 2 credits/result |
| `community_moderator_explorer` | `targetCommunityId` | Moderators of a community | 2 credits/result |
| `community_post_extractor` | `targetCommunityId` | Posts from a community | 1 credit/result |
| `community_search` | `targetCommunityId` + `searchQuery` | Search posts within a community | 1 credit/result |
| `list_member_extractor` | `targetListId` | Members of a list | 2 credits/result |
| `list_post_extractor` | `targetListId` | Posts from a list | 1 credit/result |
| `list_follower_explorer` | `targetListId` | Followers of a list | 2 credits/result |
| `space_explorer` | `targetSpaceId` | Participants of a Space | 2 credits/result |
| `people_search` | `searchQuery` | Search for users by keyword | 2 credits/result |
| `tweet_search_extractor` | `searchQuery` | Search and extract tweets by keyword or hashtag (bulk, up to 1,000) | 1 credit/result |

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

// Step 2: Get draw details with winners
const details = await xquikFetch(`/draws/${draw.id}`);
// details.winners: [
//   { position: 1, authorUsername: "winner1", tweetId: "...", isBackup: false },
//   ...
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
// 1. Create monitor (free)
const monitor = await xquikFetch("/monitors", {
  method: "POST",
  body: JSON.stringify({
    username: "elonmusk",
    eventTypes: ["tweet.new", "tweet.reply", "tweet.quote", "follower.gained"],
  }),
});

// 2. Register webhook (free)
const webhook = await xquikFetch("/webhooks", {
  method: "POST",
  body: JSON.stringify({
    url: "https://your-server.com/webhook",
    eventTypes: ["tweet.new", "tweet.reply"],
  }),
});
// IMPORTANT: Save webhook.secret. It is shown only once!

// 3. Poll events (alternative to webhooks, free)
const events = await xquikFetch("/events?monitorId=7&limit=50");
```

Event types: `tweet.new`, `tweet.quote`, `tweet.reply`, `tweet.retweet`, `follower.gained`, `follower.lost`.

## MCP Server (AI Agents)

The MCP server at `https://xquik.com/mcp` provides 9 tools. StreamableHTTP transport. API key auth (`x-api-key` header) for CLI/IDE clients; OAuth 2.1 for web clients (Claude.ai, ChatGPT Developer Mode).

### Tools

| Tool | Description | Cost |
|------|-------------|------|
| `explore` | Search the API endpoint catalog (read-only, no network calls) | Free |
| `xquik` | Execute API calls against your account (99 endpoints, 12 categories) | Varies |

Supported platforms: Claude.ai, Claude Desktop, Claude Code, ChatGPT (Custom GPT, Agents SDK, Developer Mode), Codex CLI, Cursor, VS Code, Windsurf, OpenCode.

For setup configs per platform, read [references/mcp-setup.md](references/mcp-setup.md). For tool details with selection rules, common mistakes, and unsupported operations, read [references/mcp-tools.md](references/mcp-tools.md).

### MCP vs REST API

| | MCP Server | REST API |
|---|------------|----------|
| **Best for** | AI agents, IDE integrations | Custom apps, scripts, backend services |
| **Model** | 9 tools | 99 individual endpoints |
| **Categories** | 12: account, automations, bot, composition, credits, extraction, integrations, media, monitoring, support, twitter, x-accounts, x-write | Same |
| **Coverage** | Full — `xquik` tool calls any REST endpoint | Direct HTTP calls |
| **File export** | Not available | CSV, XLSX, Markdown |
| **Unique to REST** | - | API key management, file export (CSV/XLSX/MD), account locale update |

### Workflow Patterns

Common multi-step sequences (all via `xquik` tool calling REST endpoints):

- **Set up real-time alerts:** `POST /monitors` → `POST /webhooks` → `POST /webhooks/{id}/test`
- **Run a giveaway:** `GET /account` (check budget) → `POST /draws`
- **Bulk extraction:** `POST /extractions/estimate` → `POST /extractions` → `GET /extractions/{id}`
- **Full tweet analysis:** `GET /x/tweets/{id}` (metrics) → `POST /extractions` with `thread_extractor`
- **Find and analyze user:** `GET /x/users/{username}` → `GET /x/users/{id}/tweets` → `GET /x/tweets/{id}`
- **Compose algorithm-optimized tweet:** `POST /compose` (step=compose) → AI asks follow-ups → (step=refine) → AI drafts → (step=score) → iterate
- **Analyze tweet style:** `POST /styles` (fetch & cache) → `GET /styles/{username}` (reference) → `POST /compose` with `styleUsername`
- **Compare styles:** `POST /styles` for both accounts → `GET /styles/compare`
- **Track tweet performance:** `POST /styles` (cache tweets) → `GET /styles/{username}/performance` (live metrics)
- **Save & manage drafts:** `POST /compose` → `POST /drafts` → `GET /drafts` → `DELETE /drafts/{id}`
- **Download & share media:** `POST /x/media/download` (returns permanent hosted URLs)
- **Get trending news:** `GET /radar` (7 sources, free) → `POST /compose` with trending topic
- **Subscribe or manage billing:** `POST /subscribe` (returns Stripe URL)
- **Post a tweet:** `POST /x/accounts` (connect) → `POST /x/tweets` with `account` + `text` (optionally `POST /x/media` first)
- **Engage with tweets:** `POST /x/tweets/{id}/like`, `POST /x/tweets/{id}/retweet`, `POST /x/users/{id}/follow`
- **Set up Telegram alerts:** `POST /integrations` (type=telegram, chatId, eventTypes) → `POST /integrations/{id}/test`
- **Create automation flow:** `POST /automations` (name, triggerType, triggerConfig) → `POST /automations/{slug}/steps` (add actions) → `PATCH /automations/{slug}` (activate)
- **Check & top up credits:** `GET /credits` → `POST /credits/topup`
- **Open support ticket:** `POST /support/tickets` (subject, body) → `GET /support/tickets/{id}` (check status) → `POST /support/tickets/{id}/messages` (reply)

## Conventions

- **IDs are strings.** Bigint values; treat as opaque strings, never parse as numbers
- **Timestamps are ISO 8601 UTC.** Example: `2026-02-24T10:30:00.000Z`
- **Errors return JSON.** Format: `{ "error": "error_code" }`
- **Cursors are opaque.** Pass `nextCursor` as the `after` query parameter, never decode
- Export formats: `csv`, `xlsx`, `md` via `GET /extractions/{id}/export?format=csv` or `GET /draws/{id}/export?format=csv&type=winners`

## Reference Files

For additional detail beyond this guide:

- **`references/mcp-tools.md`**: MCP tool selection rules, workflow patterns, common mistakes, and unsupported operations
- **`references/api-endpoints.md`**: All REST API endpoints with methods, paths, parameters, and response shapes
- **`references/python-examples.md`**: Python equivalents of all JavaScript examples (retry, extraction, draw, webhook)
- **`references/webhooks.md`**: Extended webhook examples, local testing with ngrok, delivery status monitoring
- **`references/mcp-setup.md`**: MCP server configuration for 10 IDEs and AI agent platforms
- **`references/extractions.md`**: Extraction tool details, export columns
- **`references/types.md`**: TypeScript type definitions for all REST API and MCP output objects
