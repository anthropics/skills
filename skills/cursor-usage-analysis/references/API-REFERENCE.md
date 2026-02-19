# Cursor Enterprise API Reference

Base URL: `https://api.cursor.com`
Auth: **Basic Auth** with `Authorization: Basic {base64(API_KEY + ':')}`

Two separate API keys may be required: Admin API key and Analytics API key (generated from team settings).

## Rate Limits (per team, per minute)

| API | Endpoint Type | Limit |
|-----|---------------|-------|
| Admin API | Most endpoints | 20 req/min |
| Admin API | `/teams/user-spend-limit` | 250 req/min |
| Analytics API | Team-level (`/analytics/team/*`) | 100 req/min |
| Analytics API | By-user (`/analytics/by-user/*`) | 50 req/min |

304 responses from ETag caching do NOT count against rate limits.

## Admin API Endpoints

### GET /teams/members
Returns `{ teamMembers: [{ name, email, id, role, isRemoved }] }`

### POST /teams/daily-usage-data
Body: `{ page, pageSize, startDate?: number (ms), endDate?: number (ms) }`
Returns paginated daily usage per user. Poll at most once per hour.

### POST /teams/spend
Body: `{ page, pageSize }`
Returns `{ teamMemberSpend: [...], subscriptionCycleStart, totalPages, totalMembers }`

### POST /teams/filtered-usage-events
Body: `{ email?, startDate?, endDate?, page, pageSize }`
Returns per-request events with model, tokens, cost. Max 30 days per request.

### POST /teams/user-spend-limit
Body: `{ email, hardLimitDollars }`

### GET /teams/groups
Returns billing groups with member lists, spend, and daily spend breakdown.

## Analytics API Endpoints

All use `startDate`/`endDate` query params. Formats: `YYYY-MM-DD`, `7d`, `30d`, `today`, `yesterday`. Max 30 days.
Optional `users` param: comma-separated emails.

### Team-Level
- `GET /analytics/team/dau` - daily active users
- `GET /analytics/team/models` - model usage with breakdown per day
- `GET /analytics/team/agent-edits` - suggested/accepted/rejected diffs and lines
- `GET /analytics/team/tabs` - tab autocomplete usage
- `GET /analytics/team/mcp` - MCP tool adoption
- `GET /analytics/team/commands` - command usage
- `GET /analytics/team/plans` - plan mode adoption
- `GET /analytics/team/client-versions` - version distribution
- `GET /analytics/team/top-file-extensions` - most edited file types
- `GET /analytics/team/leaderboard` - ranked by AI usage
- `GET /analytics/team/ask-mode` - ask mode adoption

### By-User (paginated)
Pattern: `GET /analytics/by-user/{metric}?page&pageSize` (max 500)
Available: agent-edits, tabs, models, mcp, commands, plans, ask-mode, client-versions, top-file-extensions

## Caching

Analytics APIs support ETags. Use `If-None-Match` header for 304 responses (15-minute cache).
