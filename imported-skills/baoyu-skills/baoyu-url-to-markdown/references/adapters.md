# Adapters & Media

Read when choosing an adapter, handling media, or answering adapter-specific questions.

## Built-in Adapters

| Adapter | URLs | Key Features |
|---------|------|-------------|
| `x` | x.com, twitter.com | Tweets, threads, X Articles, media, login detection |
| `youtube` | youtube.com, youtu.be | Transcript/captions, chapters, cover image, metadata |
| `hn` | news.ycombinator.com | Threaded comments, story metadata, nested replies |
| `generic` | Any URL (fallback) | Defuddle extraction, Readability fallback, auto-scroll, network idle detection |

Adapter is auto-selected based on URL. Override with `--adapter <name>`.

### YouTube

- Extracts transcripts/captions when available
- Transcript format: `[MM:SS] Text segment` with chapter headings
- Availability depends on YouTube exposing a caption track; videos with captions disabled or restricted playback may produce description-only output
- Use `--wait-for force` if the page needs time to finish loading player metadata

### X/Twitter

- Extracts single tweets, threads, and X Articles
- Auto-detects login state; if logged out and content requires auth, JSON output shows `"status": "needs_interaction"`
- Use `--wait-for interaction` for login-protected content

### Hacker News

- Parses threaded comments with proper nesting and reply hierarchy
- Includes story metadata (title, URL, author, score, comment count)
- Shows comment deletion/dead status

## Media Download Workflow

Driven by `download_media` in EXTEND.md:

| Setting | Behavior |
|---------|----------|
| `1` (always) | Run CLI with `--download-media --output <path>` |
| `0` (never) | Run CLI with `--output <path>` (no media download) |
| `ask` (default) | Follow the ask-each-time flow below |

### Ask-Each-Time Flow

1. Run the CLI **without** `--download-media` with `--output <path>` → markdown saved
2. Check the saved markdown for remote media URLs (`https://` in image/video links)
3. **If no remote media found** → done, no prompt needed
4. **If remote media found** → ask via `AskUserQuestion`:
   - header: "Media", question: "Download N images/videos to local files?"
   - "Yes" — Download to local directories
   - "No" — Keep remote URLs
5. If the user confirms → run the CLI **again** with `--download-media --output <same-path>` (overwrites markdown with localized links)

### Media Layout

When `--download-media` is enabled:

- Images → `imgs/` next to the output file (or `--media-dir`)
- Videos → `videos/` next to the output file (or `--media-dir`)
- Markdown media links are rewritten to local relative paths

## Output Format

Markdown to stdout (or file with `--output`).

JSON output (`--format json`) returns structured data:

- `adapter` — which adapter handled the URL
- `status` — `"ok"` or `"needs_interaction"`
- `login` — login state detection (`logged_in`, `logged_out`, `unknown`)
- `interaction` — interaction gate details (kind, provider, prompt)
- `document` — structured content (url, title, author, publishedAt, content blocks, metadata)
- `media` — collected media assets with url, kind, role
- `markdown` — converted markdown text
- `downloads` — media download results (when `--download-media` used)
