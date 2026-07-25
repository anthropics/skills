---
name: baoyu-markdown-to-html
description: Converts Markdown to styled HTML with WeChat-compatible themes. Supports code highlighting, math, Mermaid (rendered to PNG via headless Chrome), PlantUML, footnotes, alerts, infographics, and optional bottom citations for external links. Use when user asks for "markdown to html", "convert md to html", "md 转 html", "微信外链转底部引用", or needs styled HTML output from markdown.
version: 1.117.3
metadata:
  openclaw:
    homepage: https://github.com/JimLiu/baoyu-skills#baoyu-markdown-to-html
    requires:
      anyBins:
        - bun
        - npx
---

# Markdown to HTML Converter

Converts Markdown files to beautifully styled HTML with inline CSS, optimized for WeChat Official Account and other platforms.

## User Input Tools

When this skill prompts the user, follow this tool-selection rule (priority order):

1. **Prefer built-in user-input tools** exposed by the current agent runtime — e.g., `AskUserQuestion`, `request_user_input`, `clarify`, `ask_user`, or any equivalent.
2. **Fallback**: if no such tool exists, emit a numbered plain-text message and ask the user to reply with the chosen number/answer for each question.
3. **Batching**: if the tool supports multiple questions per call, combine all applicable questions into a single call; if only single-question, ask them one at a time in priority order.

Concrete `AskUserQuestion` references below are examples — substitute the local equivalent in other runtimes.

## Script Directory

**Agent Execution**: Determine this SKILL.md directory as `{baseDir}`. Resolve `${BUN_X}` runtime: if `bun` installed → `bun`; if `npx` available → `npx -y bun`; else suggest installing bun. Replace `{baseDir}` and `${BUN_X}` with actual values.

| Script | Purpose |
|--------|---------|
| `scripts/main.ts` | Main entry point |

## Preferences (EXTEND.md)

Check EXTEND.md in priority order — the first one found wins:

| Priority | Path | Scope |
|----------|------|-------|
| 1 | `.baoyu-skills/baoyu-markdown-to-html/EXTEND.md` | Project |
| 2 | `${XDG_CONFIG_HOME:-$HOME/.config}/baoyu-skills/baoyu-markdown-to-html/EXTEND.md` | XDG |
| 3 | `$HOME/.baoyu-skills/baoyu-markdown-to-html/EXTEND.md` | User home |

If none found, use defaults.

**EXTEND.md supports**: default theme, custom CSS variables, code block style, mermaid defaults (`mermaid_theme`, `mermaid_scale`, `mermaid_background`).

## Workflow

### Step 0: Pre-check (Chinese Content)

**Condition**: Only execute if input file contains Chinese text.

**Detection**:
1. Read input markdown file
2. Check if content contains CJK characters (Chinese/Japanese/Korean)
3. If no CJK content → skip to Step 1

**Format Suggestion**:

If CJK content detected AND `baoyu-format-markdown` skill is available:

Use `AskUserQuestion` to ask whether to format first. Formatting can fix:
- Bold markers with punctuation inside causing `**` parse failures
- CJK/English spacing issues

**If user agrees**: Invoke `baoyu-format-markdown` skill to format the file, then use formatted file as input.

**If user declines**: Continue with original file.

### Step 1: Determine Theme

**Theme resolution order** (first match wins):
1. User explicitly specified theme (CLI `--theme` or conversation)
2. EXTEND.md `default_theme` (this skill's own EXTEND.md, checked in Step 0)
3. `baoyu-post-to-wechat` EXTEND.md `default_theme` (cross-skill fallback)
4. If none found → use AskUserQuestion to confirm

**Cross-skill EXTEND.md check** (only if this skill's EXTEND.md has no `default_theme`):

Read `$HOME/.baoyu-skills/baoyu-post-to-wechat/EXTEND.md` if it exists and look for a `default_theme:` line. Use the value if present; otherwise fall through.

**If theme is resolved from EXTEND.md**: Use it directly, do NOT ask the user.

**If no default found**: use `AskUserQuestion` to confirm a theme from the [Themes](#themes) table below.

### Step 1.5: Determine Citation Mode

**Default**: Off. Do not ask by default.

**Enable only if the user explicitly asks** for "微信外链转底部引用", "底部引用", "文末引用", or passes `--cite`.

**Behavior when enabled**:
- Ordinary external links are rendered with numbered superscripts and collected under a final `引用链接` section.
- `https://mp.weixin.qq.com/...` links stay as direct links and are not moved to the bottom.
- Bare links where link text equals URL stay inline.

### Step 2: Convert

```bash
${BUN_X} {baseDir}/scripts/main.ts <markdown_file> --theme <theme> [--cite]
```

### Step 3: Report Result

Display the output path from JSON result. If backup was created, mention it.

## Usage

```bash
${BUN_X} {baseDir}/scripts/main.ts <markdown_file> [options]
```

**Options:**

| Option | Description | Default |
|--------|-------------|---------|
| `--theme <name>` | Theme name (default, grace, simple, modern) | default |
| `--color <name\|hex>` | Primary color: preset name or hex value | theme default |
| `--font-family <name>` | Font: sans, serif, serif-cjk, mono, or CSS value | theme default |
| `--font-size <N>` | Font size: 14px, 15px, 16px, 17px, 18px | 16px |
| `--title <title>` | Override title from frontmatter | |
| `--cite` | Convert external links to bottom citations, append `引用链接` section | false (off) |
| `--keep-title` | Keep the first heading in content | false (removed) |
| `--mermaid-theme <name>` | Mermaid theme: `default`, `forest`, `dark`, `neutral`, `base` | default |
| `--mermaid-scale <N>` | Mermaid render scale (positive number ≤ 4) | 2 |
| `--mermaid-width <N>` | Mermaid target display width in CSS px; PNG is rendered at `width × scale` pixels when the diagram is narrower than this | 860 |
| `--mermaid-bg <value>` | Mermaid background: `white`, `transparent`, or `#hex` | white |
| `--no-mermaid` | Skip Mermaid PNG rendering; emit `<pre class="mermaid">` fallback | false |
| `--help` | Show help | |

**Color Presets:**

| Name | Hex | Label |
|------|-----|-------|
| blue | #0F4C81 | Classic Blue |
| green | #009874 | Emerald Green |
| vermilion | #FA5151 | Vibrant Vermilion |
| yellow | #FECE00 | Lemon Yellow |
| purple | #92617E | Lavender Purple |
| sky | #55C9EA | Sky Blue |
| rose | #B76E79 | Rose Gold |
| olive | #556B2F | Olive Green |
| black | #333333 | Graphite Black |
| gray | #A9A9A9 | Smoke Gray |
| pink | #FFB7C5 | Sakura Pink |
| red | #A93226 | China Red |
| orange | #D97757 | Warm Orange (modern default) |

**Examples:**

```bash
# Basic conversion (uses default theme, removes first heading)
${BUN_X} {baseDir}/scripts/main.ts article.md

# With specific theme
${BUN_X} {baseDir}/scripts/main.ts article.md --theme grace

# Theme with custom color
${BUN_X} {baseDir}/scripts/main.ts article.md --theme modern --color red

# Enable bottom citations for ordinary external links
${BUN_X} {baseDir}/scripts/main.ts article.md --cite

# Keep the first heading in content
${BUN_X} {baseDir}/scripts/main.ts article.md --keep-title

# Override title
${BUN_X} {baseDir}/scripts/main.ts article.md --title "My Article"
```

## Output

**File location**: Same directory as input markdown file.
- Input: `/path/to/article.md`
- Output: `/path/to/article.html`

**Conflict handling**: If HTML file already exists, it will be backed up first:
- Backup: `/path/to/article.html.bak-YYYYMMDDHHMMSS`

**JSON output to stdout:**

```json
{
  "title": "Article Title",
  "author": "Author Name",
  "summary": "Article summary...",
  "htmlPath": "/path/to/article.html",
  "backupPath": "/path/to/article.html.bak-20260128180000",
  "contentImages": [
    {
      "placeholder": "MDTOHTMLIMGPH_1",
      "localPath": "/path/to/img.png",
      "originalPath": "imgs/image.png"
    }
  ],
  "mermaidImages": [
    {
      "hash": "a1b2c3d4e5f6",
      "localPath": "/path/to/imgs/.mermaid-cache/mermaid-a1b2c3d4e5f6.png",
      "cached": false
    }
  ]
}
```

**Mermaid rendering**: Code blocks fenced as ` ```mermaid ` are rendered to PNGs via headless Chrome (CDP) and cached at `imgs/.mermaid-cache/mermaid-<hash>.png`. The cache key includes the code, theme, scale, target width, background, and mermaid version. Add `imgs/.mermaid-cache/` to `.gitignore` if you do not want generated diagrams checked in. Requires Chrome/Chromium/Edge on the system; otherwise the block falls back to `<pre class="mermaid">…</pre>` and conversion still succeeds.

## Themes

| Theme | Description |
|-------|-------------|
| `default` | Classic - traditional layout, centered title with bottom border, H2 with white text on colored background |
| `grace` | Elegant - text shadow, rounded cards, refined blockquotes (by @brzhang) |
| `simple` | Minimal - modern minimalist, asymmetric rounded corners, clean whitespace (by @okooo5km) |
| `modern` | Modern - large radius, pill-shaped titles, relaxed line height (pair with `--color red` for traditional red-gold style) |

## Supported Markdown Features

| Feature | Syntax |
|---------|--------|
| Headings | `# H1` to `###### H6` |
| Bold/Italic | `**bold**`, `*italic*` |
| Code blocks | ` ```lang ` with syntax highlighting |
| Inline code | `` `code` `` |
| Tables | GitHub-flavored markdown tables |
| Images | `![alt](src)` |
| Links | `[text](url)`; add `--cite` to move ordinary external links into bottom references |
| Blockquotes | `> quote` |
| Lists | `-` unordered, `1.` ordered |
| Alerts | `> [!NOTE]`, `> [!WARNING]`, etc. |
| Footnotes | `[^1]` references |
| Ruby text | `{base|annotation}` |
| Mermaid | ` ```mermaid ` blocks rendered to local PNG via headless Chrome (cached under `imgs/.mermaid-cache/`); falls back to `<pre class="mermaid">` if Chrome is unavailable or rendering fails |
| PlantUML | ` ```plantuml ` diagrams |

## Frontmatter

Supports YAML frontmatter for metadata:

```yaml
---
title: Article Title
author: Author Name
description: Article summary
---
```

If no title is found, extracts from first H1/H2 heading or uses filename.

## Extension Support

Custom configurations via EXTEND.md. See **Preferences** section for paths and supported options.
