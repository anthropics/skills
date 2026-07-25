---
name: baoyu-post-to-weibo
description: Posts content to Weibo (微博). Supports regular posts with text, images, and videos, and headline articles (头条文章) with Markdown input via Chrome CDP. Use when user asks to "post to Weibo", "发微博", "发布微博", "publish to Weibo", "share on Weibo", "写微博", or "微博头条文章".
version: 1.117.3
metadata:
  openclaw:
    homepage: https://github.com/JimLiu/baoyu-skills#baoyu-post-to-weibo
    requires:
      anyBins:
        - bun
        - npx
---

# Post to Weibo

Posts text, images, videos, and long-form articles to Weibo via real Chrome browser (bypasses anti-bot detection).

## Script Directory

**Important**: All scripts are located in the `scripts/` subdirectory of this skill.

**Agent Execution Instructions**:
1. Determine this SKILL.md file's directory path as `{baseDir}`
2. Script path = `{baseDir}/scripts/<script-name>.ts`
3. Replace all `{baseDir}` in this document with the actual path
4. Resolve `${BUN_X}` runtime: if `bun` installed → `bun`; if `npx` available → `npx -y bun`; else suggest installing bun

**Script Reference**:
| Script | Purpose |
|--------|---------|
| `scripts/weibo-post.ts` | Regular posts (text + images) |
| `scripts/weibo-article.ts` | Headline article publishing (Markdown) |
| `scripts/copy-to-clipboard.ts` | Copy content to clipboard |
| `scripts/paste-from-clipboard.ts` | Send real paste keystroke |

## Preferences (EXTEND.md)

Check EXTEND.md in priority order — the first one found wins:

| Priority | Path | Scope |
|----------|------|-------|
| 1 | `.baoyu-skills/baoyu-post-to-weibo/EXTEND.md` | Project |
| 2 | `${XDG_CONFIG_HOME:-$HOME/.config}/baoyu-skills/baoyu-post-to-weibo/EXTEND.md` | XDG |
| 3 | `$HOME/.baoyu-skills/baoyu-post-to-weibo/EXTEND.md` | User home |

If none found, use defaults.

**EXTEND.md supports**: Default Chrome profile

## Prerequisites

- Google Chrome or Chromium
- `bun` runtime
- First run: log in to Weibo manually (session saved)

---

## Regular Posts

Text + images/videos (max 18 files total). Posted on Weibo homepage.

```bash
${BUN_X} {baseDir}/scripts/weibo-post.ts "Hello Weibo!" --image ./photo.png
${BUN_X} {baseDir}/scripts/weibo-post.ts "Watch this" --video ./clip.mp4
```

**Parameters**:
| Parameter | Description |
|-----------|-------------|
| `<text>` | Post content (positional) |
| `--image <path>` | Image file (repeatable) |
| `--video <path>` | Video file (repeatable) |
| `--profile <dir>` | Custom Chrome profile |

**Note**: Script opens browser with content filled in. User reviews and publishes manually.

---

## Headline Articles (头条文章)

Long-form Markdown articles published at `https://card.weibo.com/article/v3/editor`.

```bash
${BUN_X} {baseDir}/scripts/weibo-article.ts article.md
${BUN_X} {baseDir}/scripts/weibo-article.ts article.md --cover ./cover.jpg
```

**Parameters**:
| Parameter | Description |
|-----------|-------------|
| `<markdown>` | Markdown file (positional) |
| `--cover <path>` | Cover image |
| `--title <text>` | Override title (max 32 chars, truncated if longer) |
| `--summary <text>` | Override summary (max 44 chars, auto-regenerated if longer) |
| `--profile <dir>` | Custom Chrome profile |

**Frontmatter**: `title`, `summary`, `cover_image` supported in YAML front matter.

**Character Limits**:
- Title: 32 characters max (truncated with warning if longer)
- Summary/导语: 44 characters max (auto-regenerated from content if longer)

**Markdown-to-HTML**: Do NOT pass any `--theme` parameter when converting markdown to HTML. Use the default theme (no theme argument).

**Article Workflow**:
1. Opens `https://card.weibo.com/article/v3/editor`
2. Clicks "写文章" button, waits for editor to become editable
3. Fills title (validated for 32-char limit)
4. Fills summary/导语 (validated for 44-char limit)
5. Inserts HTML content into ProseMirror editor via paste
6. Replaces image placeholders one by one (copy image → select placeholder → paste)

**Post-Composition Check**: The script automatically verifies after all images are inserted:
- Remaining `WBIMGPH_` placeholders in editor content
- Expected vs actual image count

If the check fails (warnings in output), alert the user with the specific issues before they publish.

---

## Post Type Selection

Unless the user explicitly specifies the post type:
- **Markdown file** (`.md`) → **Headline Article** (头条文章)
- **Plain text** / text with images → **Regular Post**

## Troubleshooting

### Chrome debug port not ready

If a script fails with `Chrome debug port not ready` or `Unable to connect`, kill only the CDP Chrome instances (those with `--remote-debugging-port` AND the baoyu-skills profile), then retry:

```bash
pkill -f "remote-debugging-port.*baoyu-skills/chrome-profile" 2>/dev/null; sleep 2
```

**CRITICAL**: Never kill all Chrome processes (`pkill -f "Google Chrome"`). Only kill Chrome instances launched by CDP with the baoyu-skills profile directory. The user may have regular Chrome windows open.

**Important**: This should be done automatically -- when encountering this error, kill the CDP Chrome instances and retry the command without asking the user.

## Notes

- First run: manual login required (session persists)
- All scripts only fill content into the browser, user must review and publish manually
- Cross-platform: macOS, Linux, Windows

## Extension Support

Custom configurations via EXTEND.md. See **Preferences** section for paths and supported options.
