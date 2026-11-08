---
name: buffer-api
description: "Use the Buffer GraphQL API to schedule and manage social media posts. Use when the user wants to create, schedule, edit, delete, or retrieve posts or drafts in a Buffer queue; distribute content across multiple social platforms (Instagram, Threads, LinkedIn, X/Twitter, Facebook, Google Business, Mastodon, YouTube, Pinterest, Bluesky); add public-URL media (images/video) to scheduled posts; build threads or first-comments for networks that support them; list connected Buffer channels; or check a queued post's status. Do NOT trigger for platform-native posting APIs (e.g. TikTok Direct Post) when Buffer is the intended scheduler; Buffer holds approved integration for auto-posting owned accounts."
license: Complete terms in LICENSE.txt
---

# Buffer API — Schedule, Manage & Analyze Social Posts

Use Buffer's GraphQL API to schedule, manage, and analyze social posts across
many platforms from any AI agent.

## When to Use
- Create/schedule/edit/delete/retrieve posts or drafts in a Buffer queue.
- Distribute content across platforms (Instagram, Threads, LinkedIn, X, Facebook,
  Google Business, Mastodon, YouTube, Pinterest, Bluesky).
- Add public-URL media (image/video) to scheduled posts; threads; first comments.
- List connected Buffer channels; poll a post to `sent`.
- The single approved route for automated owned-account posting (e.g. TikTok).

## Prerequisites
- Buffer account with ≥1 connected channel and an API key
  (https://publish.buffer.com/settings/api). The key acts on your own account.
- Auth: `Authorization: Bearer <API_KEY>` on every POST to `https://api.buffer.com`
  (GraphQL, `Content-Type: application/json`).
- Media on a post must be a PUBLIC url. See `references/media-and-metadata.md`.

## Endpoint & Auth
```
POST https://api.buffer.com
Authorization: Bearer <API_KEY>
Content-Type: application/json
{ "query": "<graphql>", "variables": {} }
```
GraphQL only. Explore at https://developers.buffer.com/explorer.html. `DateTime` is ISO 8601 UTC.

## 1. Account & Organization
```
query { account { id email organizations { id name } } }
```
## 2. Channels
```
query { channels(input: { organizationId: "ORG_ID" }) { id name service type } }
```
`service` = platform (instagram/tiktok/linkedin/twitter/mastodon/youtube/pinterest/bluesky/facebook/gbp). `type` = Page/Profile/Business/Group/Account.

## 3. Create a Post
```
mutation {
  createPost(input: {
    text: "...", channelId: "CHANNEL_ID", schedulingType: automatic,
    mode: addToQueue            # addToQueue | customScheduled
    # dueAt: "2026-03-10T15:00:00.000Z"   # required when mode=customScheduled
  }) {
    ... on PostActionSuccess { post { id text dueAt } }
    ... on MutationError { message }
  }
}
```
Required: `text`, `channelId`, `schedulingType: automatic`. Always spread both
success and error members (unions).

## 4. Media / Assets (public URL only)
```
createPost(input: { text:"...", channelId:"...", schedulingType: automatic,
  mode: addToQueue,
  assets: [ { image: { url: "https://cdn.example.com/img.jpg" } } ] })
  { ... on PostActionSuccess { post { id assets { id mimeType } } } ... on MutationError { message } }
```
`url` MUST be public (Buffer fetches it). Verify with `curl -sI <url>` returns 200.

## 5. Retrieve / Manage
- One post (status poll): `query { post(input: { id: "ID" }) { id status dueAt } }`
  — there is NO `getPost`; status `scheduled` → `sent` → `error`. Check `== "sent"`.
- List (cursor): `posts(first: N, after: CUR, input:{organizationId, filter:{status:[], channelIds:[]}})`
- Edit `editPost`, Delete `deletePost(input:{...})`, reorder `movePostInQueue`.

## 6. Ideas & Metrics
- `createIdea(input:{organizationId, ideaGroupId, text, media})`, `ideas(input:)`, `ideaGroups(input:)`.
- Once sent: `post(input:{id}){ metrics }`, `aggregatedPostMetrics`, `dailyPostingLimits`.

## Per-Network Metadata (selected)
- Threads/X/Bluesky/Mastodon: `metadata.<net>.thread` for threaded posts.
- LinkedIn/Facebook/Instagram: first comment; Instagram `postType` (post/story/reel)
  and per-image `userTags`; Pinterest `boardId`.
You only provide metadata for the network the channel belongs to. Details in `references/media-and-metadata.md`.

## Pitfalls (hard-won)
1. GraphQL only — legacy REST retired (401 "Public API tokens are not accepted for REST API access").
2. Poll via `post(input:{id})`, not `getPost` (no such field).
3. `status == "sent"` (string `sent`, not `published`).
4. Asset URL must be public; no blob upload mutation.
5. Non-ASCII JSON bodies: use `requests`/JSON-safe client, not `urllib` (latin-1 crash).
6. Close repeat = already queued; treat `ok=false` as queued, don't re-submit.
7. Queue limits → read message, don't blind-retry.
8. Custom scalars (`OrganizationId!/ChannelId!/PostId!`) differ from generic `ID!` — type vars correctly or inline literals (verified live).

## References
- `references/api-reference.md` — full schema (queries/mutations/types/unions).
- `references/media-and-metadata.md` — media hosting + per-network metadata.
- `scripts/buffer_graphql.py` — dependency-light GraphQL helper (stdlib, utf-8 safe).

## Verification
- `python3 scripts/buffer_graphql.py --query "{ account { id organizations { id } } }"`
  (set BUFFER_API_KEY) → returns account.
- After createPost, poll `post(input:{id})` until `status == "sent"`.
