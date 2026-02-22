# Multi-Calendar Operations

Temporal Cortex supports simultaneous connections to Google Calendar, Microsoft Outlook, and CalDAV (iCloud, Fastmail). All calendars are merged into a unified view.

## Provider-Prefixed Calendar IDs

When multiple providers are connected, use prefixed IDs to route to the correct provider:

| Format | Example | Routes to |
|--------|---------|-----------|
| `google/<id>` | `"google/primary"` | Google Calendar |
| `outlook/<id>` | `"outlook/work"` | Microsoft Outlook |
| `caldav/<id>` | `"caldav/personal"` | CalDAV (iCloud, Fastmail) |
| `<id>` (bare) | `"primary"` | Default provider |

Bare IDs (without prefix) route to the default provider configured during setup.

CalDAV calendar IDs can contain slashes (e.g., path-style IDs). The router splits on the first `/` only — everything after the prefix slash is the calendar ID.

## Cross-Calendar Availability

Use `get_availability` with multiple calendar IDs to get a merged view:

```json
{
  "start": "2026-03-16T00:00:00-04:00",
  "end": "2026-03-17T00:00:00-04:00",
  "calendar_ids": ["google/primary", "outlook/work", "caldav/personal"],
  "min_free_slot_minutes": 30,
  "privacy": "full"
}
```

The server fetches events from all providers in parallel and merges them into unified busy/free blocks.

## Privacy Modes

| Mode | `source_count` | Use case |
|------|---------------|----------|
| `"opaque"` (default) | Always `0` | Sharing availability externally — hides which calendars are busy |
| `"full"` | Actual count | Internal use — shows how many calendars contribute to each busy block |

## Provider Authentication

Each provider requires a one-time authentication:

```bash
# Google Calendar (OAuth2, browser-based consent)
npx @temporal-cortex/cortex-mcp auth google

# Microsoft Outlook (Azure AD OAuth2 with PKCE)
npx @temporal-cortex/cortex-mcp auth outlook

# CalDAV (app-specific password, presets for iCloud/Fastmail)
npx @temporal-cortex/cortex-mcp auth caldav
```

Credentials are stored locally at `~/.config/temporal-cortex/credentials.json`. Provider registrations are saved in `~/.config/temporal-cortex/config.json`.

## Environment Variables

| Variable | Required | Description |
|----------|----------|-------------|
| `GOOGLE_CLIENT_ID` | For Google | Google OAuth Client ID |
| `GOOGLE_CLIENT_SECRET` | For Google | Google OAuth Client Secret |
| `MICROSOFT_CLIENT_ID` | For Outlook | Azure AD application ID |
| `TIMEZONE` | No | IANA timezone override |
| `WEEK_START` | No | `"monday"` (default) or `"sunday"` |

CalDAV providers need no environment variables — authentication is interactive.

## Single-Provider Shortcuts

If only one provider is configured, you can use bare calendar IDs:

```json
{ "calendar_id": "primary" }
```

This routes to whichever provider is configured. No prefix needed.

## Booking Across Providers

`book_slot` works with any provider. Use the provider prefix to specify where to create the event:

```json
{
  "calendar_id": "google/primary",
  "start": "2026-03-16T14:00:00-04:00",
  "end": "2026-03-16T15:00:00-04:00",
  "summary": "Team Sync"
}
```

The conflict check queries the specified calendar. For cross-calendar conflict detection, use `get_availability` first.
