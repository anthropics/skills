# Buffer — Media & Per-Network Metadata Reference

Load this when the task involves images/video per-network configuration, threads,
first comments, or post-type selection. Progressive-disclosure detail that stays
out of the main SKILL.md.

## Public media URLs (required for assets)

Buffer fetches post assets from a **public URL** — there is no blob upload mutation.

- Host the image/video where it is publicly reachable (a CDN, S3/Cloudflare R2 with
  a public URL, or a CMS media library that returns a public URL — e.g. a WordPress
  `wp-json/wp/v2/media` upload's `source_url`).
- **Verify before creating the post:**
  ```
  curl -sI <public_url> | head -1
  ```
  Expect `HTTP/1.1 200 OK` (or `204 No Content`). If it 403s/404s to an anonymous
  client (or your agent fetch), Buffer will fail to fetch it too. Also make sure the
  URL is not signed with an expiring query param if the post is scheduled far out.
- Video: `assets: [ { video: { url: "https://.../clip.mp4" , thumbnailUrl: "https://.../thumb.jpg" } } ]`
  `thumbnailUrl` is strongly suggested so preview cards render.

## `assets` union
```
assets: [ {
  image:    { url, alt }
} | {
  video:    { url, thumbnailUrl }
} | {
  document: { url, name }
} | {
  link:     { url, title }
} ]
```
Each `assets` entry is a union member: exactly ONE of image/video/document/link.
`alt` (alternative text) is a first-class accessibility field on image media.

## Per-network `metadata` on createPost

You only provide the metadata object for the network the channel belongs to. The
top-level `metadata` key wraps per-network objects.

### Instagram  (`metadata: { instagram: {...} }`)
- **postType:** `post` | `story` | `reel` (post is default).
- **firstComment:** text posted as the first comment (also used by some networks).
- **userTags (per image):** tag users on a specific image:
  ```
  metadata: { instagram: {
    postType: "post",
    images: [ { url: "https://...", userTags: [ { username: "handle" } ] } ]
  } }
  ```
  User tags are positioned per image via `image.metadata.userTags` (not network metadata).

### LinkedIn
- `metadata.linkedin.firstComment` — a first comment under the scheduled post.

### Facebook
- `metadata.facebook.firstComment` — like LinkedIn, a first comment on the post.

### Threads / X (Twitter) / Bluesky / Mastodon — threaded posts
- `metadata.threads.thread`, `metadata.twitter.thread`, `metadata.bluesky.thread`,
  `metadata.mastodon.thread` — build a thread of N tweets/posts.
  Thread shape (example per net):
  ```
  createPost(input: {
    text: "Post 1 of the thread"
    channelId: "X_CHANNEL"
    schedulingType: automatic mode: addToQueue
    metadata: { twitter: { thread: [
      { text: "Post 1" }, { text: "Post 2" }, { text: "Post 3" }
    ] } }
  })
  ```
  Threads schedule as one logical item in the queue.

### Pinterest
- **boardId** — attach the pin to a board:
  `metadata: { pinterest: { boardId: "BOARD_ID" } }`
  Boards come from `channels(...){ pinterest { boards { id name } } }` or the
  Pinterest metadata on the channel.

### LinkedIn / Google Business (first-comment like)
- `metadata.linkedin.firstComment` (as above).
- Google Business Profiles: `metadata.googleBusinessPost` variants differ — see the
  union `GoogleBusinessPostDetails` (WhatsNew / Offer / Event).

## Scheduling (recap)
- `mode` values: `addToQueue` (next open slot) | `customScheduled` (with `dueAt` ISO 8601 UTC).
- `schedulingType` is always `automatic` (there is no manual).
- A **paused** channel/posting schedule won't publish queued items — check
  `channel.isQueuePaused` (it's a field on Channel).

## Ideas (save content for later)
- Create: `createIdea(input: { organizationId, ideaGroupId, text, media: [ { url, alt } ] })`
- List: `ideas(input: { organizationId } )`, `ideaGroups(input: { organizationId })`
- `media` on an idea is the IdeaMediaInput: `url` (required), `alt`, `thumbnailUrl`,
  `type` (image|gif|video|document|link|unsupported), `size`, `source`.
- Video is NOT exposed/supported on public API ideas (even though type hints video).

## Post template (preview 🧪)
- `postTemplates` / `createPostTemplate` / `editPostTemplate` / `deletePostTemplate`
  are preview-phase. `{{placeholders}}` in body; taxonomy fields are Buffer-curated
  and setting them by third-parties is ignored. Unless you need templates, skip.

## Metrics
- Once sent, per-network engagement is normalized under `Post.metrics`:
  `impressions`, `reach`, `reactions`, `comments`, `shares`, `clicks` (fields vary
  per network; Buffer maps the standard set).
- `aggregatedPostMetrics(input: { organizationId, since, until })` and
  `dailyPostingLimits` (per-channel caps) give a dashboard view.

## Practical pitfalls (repeat of SKILL.md, more detail)
- image/video URL must be PUBLIC and reachable by Buffer. No signed S3 links that
  expire before the scheduled time. Host on a3 / your CDN / WordPress media.
- Do NOT pass binary media as a data URI in `url` — Buffer expects a real public web URL.
- Keep `alt` + `thumbnailUrl` where offered; accessibility and card previews.
- For a batch of different network metadata, you must create ONE post PER channel (they
  are per-channel records) — the API is channel-scoped, not cross-poster. If you need
  multi-network from one command, loop per channel, each with its own metadata + assets.
