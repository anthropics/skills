# Image-Text Posting (贴图发表, formerly 图文)

Post image-text messages with multiple images to WeChat Official Account.

> **Note**: WeChat has renamed "图文" to "贴图" in the Official Account menu (as of 2026).

## Usage

```bash
# Post with images and markdown file (title/content extracted automatically)
${BUN_X} ./scripts/wechat-browser.ts --markdown source.md --images ./images/

# Post with explicit title and content
${BUN_X} ./scripts/wechat-browser.ts --title "标题" --content "内容" --image img1.png --image img2.png

# Save as draft
${BUN_X} ./scripts/wechat-browser.ts --markdown source.md --images ./images/ --submit
```

## Parameters

| Parameter | Description |
|-----------|-------------|
| `--markdown <path>` | Markdown file for title/content extraction |
| `--images <dir>` | Directory containing images (sorted by name) |
| `--title <text>` | Article title (max 20 chars, auto-compressed if too long) |
| `--content <text>` | Article content (max 1000 chars, auto-compressed if too long) |
| `--image <path>` | Single image file (can be repeated) |
| `--submit` | Save as draft (default: preview only) |
| `--profile <dir>` | Chrome profile directory |

## Auto Title/Content from Markdown

When using `--markdown`, the script:

1. **Parses frontmatter** for title and author:
   ```yaml
   ---
   title: 文章标题
   author: 作者名
   ---
   ```

2. **Falls back to H1** if no frontmatter title:
   ```markdown
   # 这将成为标题
   ```

3. **Compresses title** to 20 characters if too long:
   - Original: "如何在一天内彻底重塑你的人生"
   - Compressed: "一天彻底重塑你的人生"

4. **Extracts first paragraphs** as content (max 1000 chars)

## Image Directory Mode

When using `--images <dir>`:

- All PNG/JPG files in directory are uploaded
- Files are sorted alphabetically by name
- Naming convention: `01-cover.png`, `02-content.png`, etc.

## Constraints

| Field | Max Length | Notes |
|-------|------------|-------|
| Title | 20 chars | Auto-compressed if longer |
| Content | 1000 chars | Auto-compressed if longer |
| Images | 9 max | WeChat limit |

## Example Session

```
User: /post-to-wechat --markdown ./article.md --images ./xhs-images/

Claude:
1. Parses markdown meta:
   - Title: "如何在一天内彻底重塑你的人生" → "一天内重塑你的人生"
   - Author: from frontmatter or default
2. Extracts content from first paragraphs
3. Finds 7 images in xhs-images/
4. Opens Chrome, navigates to WeChat "图文" editor
5. Uploads all images
6. Fills title and content
7. Reports: "Image-text posted with 7 images."
```

## Scripts

| Script | Purpose |
|--------|---------|
| `wechat-browser.ts` | Main image-text posting script |
| `cdp.ts` | Chrome DevTools Protocol utilities |
| `copy-to-clipboard.ts` | Clipboard operations |
