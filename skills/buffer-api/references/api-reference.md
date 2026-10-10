# Buffer GraphQL API — Full Reference

Complete operation + type catalogue distilled from https://developers.buffer.com/reference.html
(endpoint `https://api.buffer.com`, Bearer auth). Use for anything beyond the quick
operations in SKILL.md.

## Operations (queries & mutations)

### Queries
| Query | Input | Returns | Notes |
|---|---|---|---|
| `account` | — | `Account` | authenticated user + profile |
| `channel` | `input:{id}` | `Channel` | single channel by ID |
| `channels` | `input:{organizationId, filter}` | `[Channel]` | all channels for org, current-user permissions |
| `post` | `input:{id}` | `Post` | **single post by id — there is NO `getPost`** |
| `posts` | `first, after, input:{organizationId, filter}` | `PostsResults` | cursor-paginated posts; filter `status`,`channelIds` |
| `aggregatedPostMetrics` | `input:{...}` | `AggregatedPostMetrics` | aggregate metrics across posts/channels |
| `dailyPostingLimits` | `input:{...}` | `[DailyPostingLimitStatus]` | per-channel daily caps |
| `ideas` | `first, after, input:{organizationId}` | `IdeasConnection` | list ideas (cursor) |
| `ideaGroups` | `input:{...}` | `[IdeaGroup]` | idea board groups |
| `postTemplate` 🧪 | `input:{id}` | `PostTemplate` | single template |
| `postTemplates` 🧪 | `first, after, input:{...}` | `PostTemplatesConnection` | list templates |

### Mutations
| Mutation | Input | Union/Return | Notes |
|---|---|---|---|
| `createPost` | `CreatePostInput` | `PostActionPayload` | create/schedule a post |
| `editPost` | `EditPostInput` | `PostActionPayload` | edit a post |
| `deletePost` | `DeletePostInput` | `DeletePostPayload` | delete a post |
| `movePostInQueue` ⚠️ | `MovePostInQueueInput` | `MovePostInQueuePayload` | reorder queued (experimental) |
| `createIdea` | `CreateIdeaInput` | `CreateIdeaPayload` | save an idea |
| `createPostTemplate` 🧪 | `CreatePostTemplateInput` | `CreatePostTemplatePayload` | create a template |
| `updatePostTemplate` 🧪 | `UpdatePostTemplateInput` | `UpdatePostTemplatePayload` | update a template |
| `deletePostTemplate` 🧪 | `DeletePostTemplateInput` | `DeletePostTemplatePayload` | delete a template |

## Key types & union shapes

### PostActionPayload (createPost/editPost result) — UNION of:
- `PostActionSuccess` { `post: Post` }
- `NotFoundError`, `UnauthorizedError`, `UnexpectedError`, `RestProxyError`,
  `LimitReachedError`, `InvalidInputError`
Spread: `{ ... on PostActionSuccess { post { id text dueAt } } ... on MutationError { message } }`

### DeletePostPayload — UNION of `DeletePostSuccess` | `VoidMutationError`
### MovePostInQueuePayload — `PostActionSuccess` | `VoidMutationError`
### PostMetadata — UNION per network:
`InstagramPostMetadata | FacebookPostMetadata | LinkedInPostMetadata |
TwitterPostMetadata | PinterestPostMetadata | GoogleBusinessPostMetadata |
YoutubePostMetadata | MastodonPostMetadata | TiktokPostMetadata |
ThreadsPostMetadata | BlueskyPostMetadata`

### Post (core fields)
`id`, `text`, `channelId`, `dueAt` (DateTime ISO 8601), `status`
(`scheduled`→`sent`→`error`), `assets` (`[PostAsset]`: id, mimeType, url, alt),
`metrics` (`PostMetrics` when sent), `metadata` (per-network `PostMetadata`).

### Channel (core fields)
`id`, `name`, `service` (platform), `type` (Page/Profile/Business/Group/Account),
`organizationId`, `descriptor`, `avatar`, `externalLink`, `isDisconnected`,
`isLocked` (locked = cannot post), `isQueuePaused`, `linkShortening`,
`postingSchedule`, `weeklyPostingLimit`, `metadata` (per-network:
BlueskyMetadata.serverUrl, MastodonMetadata.{maxCharacters, serverUrl},
PinterestMetadata.boards, FacebookMetadata.locationData, TiktokMetadata,
TwitterMetadata.subscriptionType, LinkedInMetadata…), `timezone`.

### Account (core fields)
`id`, `email`, `backupEmail`, `avatar`, `createdAt`, `organizations`, `timezone`,
`name`, `preferences`, `connectedApps`.

### PostAsset
`id`, `mimeType`, `url`, `size`, `alt`, `source`. (Attached via `assets` input by
public URL — see media reference.)

### Ideas
`Idea` (idea, media: List[IdeaMedia(id, url, thumbnailUrl, type, size, alt, source)]),
`IdeaGroup` { id, name, isLocked }. `IdeaMediaSource` (Unsplash/Giphy source: name,
id, trigger, author, authorUrl).

### Scalars
`AccountId`, `ChannelId`, `OrganizationId`, `PostId`, `DraftId`, `IdeaId`,
`InvitationId`, `NoteId`, `PostGroupId`, `PostTemplateId`, `TagId`, `Uuid`,
`DateTime` (ISO 8601), `Email` (normalized-lowercase).

**GOTCHA — custom scalars are NOT interchangeable with generic `ID` (verified live).**
If a query declares a variable as `ID!` but the field expects `OrganizationId!` /
`ChannelId!` / `PostId!`, GraphQL validation FAILS:
`Variable "$oid" of type "ID!" used in position expecting type "OrganizationId!"`.
Fix: either inline the value as a string literal, or type the variable with the
correct custom scalar, e.g. `query Q($oid: OrganizationId!){...}`.

### Enums
`ScheduleOption` (account prefs), `ConnectedAppCategory`, `MediaType`,
`ChannelAction`, `Product`, `Service`, `ChannelType`, `DayOfWeek`,
`PostTemplateVisibility`, `ChannelLinkShortening` statuses.

## Shared input shapes
- `CreatePostInput`: `text`, `channelId`, `schedulingType: automatic`,
  `mode: addToQueue | customScheduled`, `dueAt` (custom), `assets:[]`,
  `metadata: PostInputMetaData` (per-network).
- `EditPostInput`: `id` (postId), plus `text`, `mode`, `dueAt`, `assets` you change.
- `DeletePostInput`: `postId` (or `input:{ id }` equivalent).
- `IdeasInput` / `IdeaMediaInput`: see media reference (url required on media).

## Pagination
- `posts`, `ideas`, `postTemplates` use **cursor-based**: top-level `first: Int`
  (+ `after: String` cursor from `pageInfo.endCursor`).
- Page through until `hasNextPage == false`.

## Polling a post to "sent"
Poll `post(input: { id: "ID" }) { id status }` until `status == "sent"`.
The string is `sent`, NOT `published`. There is no `getPost` query field.

## Auth / endpoint recap
- `POST https://api.buffer.com`, header `Authorization: Bearer <key>`.
- Key is account-scoped (your own Buffer account). Get at
  https://publish.buffer.com/settings/api.
- Buffer also publishes an MCP server: `https://mcp.buffer.com/mcp` with the same
  Bearer header (see SKILL.md "MCP alternative").
- Legacy REST `api.bufferapp.com/1/` is RETIRED (2027-02-01). Ignore any doc that
  shows `/1/`.

---
Sourced 2026-08-21 from https://developers.buffer.com (reference.html). Re-verify
against that page for schema drift.
