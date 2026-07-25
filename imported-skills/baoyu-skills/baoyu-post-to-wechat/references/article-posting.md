# Article Posting (文章发表)

Post markdown articles to WeChat Official Account with full formatting support.

## Usage

```bash
# Post markdown article
${BUN_X} ./scripts/wechat-article.ts --markdown article.md

# With theme
${BUN_X} ./scripts/wechat-article.ts --markdown article.md --theme grace

# Disable bottom citations for ordinary external links
${BUN_X} ./scripts/wechat-article.ts --markdown article.md --no-cite

# With explicit options
${BUN_X} ./scripts/wechat-article.ts --markdown article.md --author "作者名" --summary "摘要"
```

## Parameters

| Parameter | Description |
|-----------|-------------|
| `--markdown <path>` | Markdown file to convert and post |
| `--theme <name>` | Theme: default, grace, simple, modern |
| `--no-cite` | Keep ordinary external links inline instead of converting them to bottom citations |
| `--title <text>` | Override title (auto-extracted from markdown) |
| `--author <name>` | Author name |
| `--summary <text>` | Article summary |
| `--html <path>` | Pre-rendered HTML file (alternative to markdown) |
| `--profile <dir>` | Chrome profile directory |

## Markdown Format

```markdown
---
title: Article Title
author: Author Name
---

# Title (becomes article title)

Regular paragraph with **bold** and *italic*.

## Section Header

![Image description](./image.png)

- List item 1
- List item 2

> Blockquote text

[Link text](https://example.com)
```

Markdown mode converts ordinary external links into bottom citations by default for WeChat-friendly output. Use `--no-cite` to disable that behavior.

## Image Handling

1. **Parse**: Images in markdown are replaced with `WECHATIMGPH_N`
2. **Render**: HTML is generated with placeholders in text
3. **Paste**: HTML content is pasted into WeChat editor
4. **Replace**: For each placeholder:
   - Find and select the placeholder text
   - Scroll into view
   - Press Backspace to delete the placeholder
   - Paste the image from clipboard

## Scripts

| Script | Purpose |
|--------|---------|
| `wechat-article.ts` | Main article publishing script |
| `md-to-wechat.ts` | Markdown to HTML with placeholders |
| `md/render.ts` | Markdown rendering with themes |

## Example Session

```
User: /post-to-wechat --markdown ./article.md

Claude:
1. Parses markdown, finds 5 images
2. Generates HTML with placeholders
3. Opens Chrome, navigates to WeChat editor
4. Pastes HTML content
5. For each image:
   - Selects WECHATIMGPH_1
   - Scrolls into view
   - Presses Backspace to delete
   - Pastes image
6. Reports: "Article composed with 5 images."
```
