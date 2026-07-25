---
name: baoyu-url-to-markdown
description: Fetch any URL and convert to markdown using baoyu-fetch CLI (Chrome CDP with site-specific adapters). Built-in adapters for X/Twitter, YouTube transcripts, Hacker News threads, and generic pages via Defuddle. Handles login/CAPTCHA via interaction wait modes. Use when user wants to save a webpage as markdown.
version: 1.61.0
metadata:
  openclaw:
    homepage: https://github.com/JimLiu/baoyu-skills#baoyu-url-to-markdown
    requires:
      anyBins:
        - bun
---

# URL to Markdown

Fetches any URL via `baoyu-fetch` CLI (Chrome CDP + site-specific adapters) and converts it to clean markdown.

## User Input Tools

When this skill prompts the user, follow this tool-selection rule (priority order):

1. **Prefer built-in user-input tools** exposed by the current agent runtime — e.g., `AskUserQuestion`, `request_user_input`, `clarify`, `ask_user`, or any equivalent.
2. **Fallback**: if no such tool exists, emit a numbered plain-text message and ask the user to reply with the chosen number/answer for each question.
3. **Batching**: if the tool supports multiple questions per call, combine all applicable questions into a single call; if only single-question, ask them one at a time in priority order.

Concrete `AskUserQuestion` references below are examples — substitute the local equivalent in other runtimes.

## CLI Setup

**Important**: The CLI source is vendored in `{baseDir}/scripts/lib`. `scripts/package.json` installs only third-party runtime dependencies.

**Agent Execution Instructions**:
1. Determine this SKILL.md file's directory path as `{baseDir}`
2. Resolve `${BUN}` runtime: if `bun` installed → `bun`; else suggest installing Bun
3. If `{baseDir}/scripts/node_modules` does not exist, run `${BUN} install --cwd {baseDir}/scripts`
4. `${READER}` = `{baseDir}/scripts/baoyu-fetch`
5. Replace all `${READER}` in this document with the resolved value

## Preferences (EXTEND.md)

Check EXTEND.md in priority order — the first one found wins:

| Priority | Path | Scope |
|----------|------|-------|
| 1 | `.baoyu-skills/baoyu-url-to-markdown/EXTEND.md` | Project |
| 2 | `${XDG_CONFIG_HOME:-$HOME/.config}/baoyu-skills/baoyu-url-to-markdown/EXTEND.md` | XDG |
| 3 | `$HOME/.baoyu-skills/baoyu-url-to-markdown/EXTEND.md` | User home |

| Result | Action |
|--------|--------|
| Found | Read, parse, apply settings |
| Not found | **MUST** run first-time setup (see below) — do NOT silently create defaults |

**EXTEND.md supports**: download media by default, default output directory.

### First-Time Setup ⛔ BLOCKING

When EXTEND.md is not found, you **MUST** use `AskUserQuestion` to gather preferences before creating EXTEND.md. **NEVER** create EXTEND.md with silent defaults. Generation is BLOCKED until setup completes. Batch all three questions into a single call:

- **Q1 — Media** (header "Media"): "How to handle images and videos in pages?"
  - "Ask each time (Recommended)" — Prompt after each save
  - "Always download" — Download to local `imgs/` and `videos/`
  - "Never download" — Keep remote URLs
- **Q2 — Output** (header "Output"): "Default output directory?"
  - "url-to-markdown (Recommended)" — Save to `./url-to-markdown/{domain}/{slug}.md`
  - User may pick "Other" and type a custom path
- **Q3 — Save** (header "Save"): "Where to save preferences?"
  - "User (Recommended)" — `~/.baoyu-skills/` (all projects)
  - "Project" — `.baoyu-skills/` (this project only)

After answers, write EXTEND.md, confirm "Preferences saved to [path]", then continue.

Full template: [references/config/first-time-setup.md](references/config/first-time-setup.md).

### Supported Keys

| Key | Default | Values | Description |
|-----|---------|--------|-------------|
| `download_media` | `ask` | `ask` / `1` / `0` | `ask` = prompt each time, `1` = always, `0` = never |
| `default_output_dir` | empty | path or empty | Default output directory (empty = `./url-to-markdown/`) |

**EXTEND.md → CLI mapping**:

| EXTEND.md key | CLI argument | Notes |
|---------------|-------------|-------|
| `download_media: 1` | `--download-media` | Requires `--output` to be set |
| `default_output_dir: ./posts/` | Agent constructs `--output ./posts/{domain}/{slug}.md` | Agent generates path, not a direct flag |

**Value priority**: CLI arguments → EXTEND.md → skill defaults.

## Usage

```bash
# Default: headless capture, markdown to stdout
${READER} <url>

# Save to file
${READER} <url> --output article.md

# Save with media download
${READER} <url> --output article.md --download-media

# Wait for interaction (login/CAPTCHA) — auto-detect and continue
${READER} <url> --wait-for interaction --output article.md

# Wait for interaction — manual control (Enter to continue)
${READER} <url> --wait-for force --output article.md

# JSON output
${READER} <url> --format json --output article.json

# Force specific adapter
${READER} <url> --adapter youtube --output transcript.md
```

## Options

| Option | Description |
|--------|-------------|
| `<url>` | URL to fetch |
| `--output <path>` | Output file path (default: stdout) |
| `--format <type>` | Output format: `markdown` (default) or `json` |
| `--json` | Shorthand for `--format json` |
| `--adapter <name>` | Force adapter: `x`, `youtube`, `hn`, or `generic` (default: auto-detect) |
| `--headless` | Force headless Chrome (no visible window) |
| `--wait-for <mode>` | Interaction wait mode: `none` (default), `interaction`, or `force` |
| `--wait-for-interaction` | Alias for `--wait-for interaction` |
| `--wait-for-login` | Alias for `--wait-for interaction` |
| `--timeout <ms>` | Page load timeout (default: 30000) |
| `--interaction-timeout <ms>` | Login/CAPTCHA wait timeout (default: 600000 = 10 min) |
| `--interaction-poll-interval <ms>` | Poll interval for interaction checks (default: 1500) |
| `--download-media` | Download images/videos to local `imgs/` and `videos/`, rewrite markdown links. Requires `--output` |
| `--media-dir <dir>` | Base directory for downloaded media (default: same as `--output` directory) |
| `--cdp-url <url>` | Reuse existing Chrome DevTools Protocol endpoint |
| `--browser-path <path>` | Custom Chrome/Chromium binary path |
| `--chrome-profile-dir <path>` | Chrome user data directory (default: `BAOYU_CHROME_PROFILE_DIR` env or `./baoyu-skills/chrome-profile`) |
| `--debug-dir <dir>` | Write debug artifacts (document.json, markdown.md, page.html, network.json) |

## Agent Quality Gate

**CRITICAL**: treat default headless capture as provisional. Some sites render differently in headless mode and can silently return low-quality content without failing the CLI.

After every headless run, inspect the saved markdown. See [references/quality-gate.md](references/quality-gate.md) for the full checklist, recovery workflow, and capture-mode table. Read it whenever a run looks suspicious or the user asks about login/CAPTCHA handling.

## Output Path Generation

The agent must construct the output file path — `baoyu-fetch` does not auto-generate paths.

**Algorithm**:
1. Determine base directory from EXTEND.md `default_output_dir` or default `./url-to-markdown/`
2. Extract domain from URL (e.g., `example.com`)
3. Generate slug from URL path or page title (kebab-case, 2-6 words)
4. Construct: `{base_dir}/{domain}/{slug}/{slug}.md` — each URL gets its own directory so media files stay isolated
5. Conflict resolution: append timestamp `{slug}-YYYYMMDD-HHMMSS/{slug}-YYYYMMDD-HHMMSS.md`

Pass the constructed path to `--output`. Media files (`--download-media`) are saved into subdirectories next to the markdown file, keeping each URL's assets self-contained.

## Adapters & Media

See [references/adapters.md](references/adapters.md) for the adapter catalog (X, YouTube, Hacker News, generic), per-adapter notes, the media download flow (`ask` / always / never), and the JSON output schema. Read it before answering adapter-specific questions or handling media prompts.

## Environment Variables

| Variable | Description |
|----------|-------------|
| `BAOYU_CHROME_PROFILE_DIR` | Chrome user data directory (can also use `--chrome-profile-dir`) |

**Troubleshooting**: Chrome not found → use `--browser-path`. Timeout → increase `--timeout`. Login/CAPTCHA → `--wait-for interaction`. Debug → `--debug-dir` to inspect captured HTML and network logs.

## Extension Support

Custom configurations via EXTEND.md. See **Preferences** section above for paths and supported keys.
