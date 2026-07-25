# Workflow Mechanics

Details for source materialization, output directory creation, and conflict resolution.

## Materialize Source

| Input Type | Action |
|------------|--------|
| File | Use as-is (no copy needed) |
| Inline text | Save to `translate/{slug}.md` |
| URL | Fetch content, save to `translate/{slug}.md` |

`{slug}`: 2-4 word kebab-case slug derived from content topic.

## Create Output Directory

Create a subdirectory next to the source file: `{source-dir}/{source-basename}-{target-lang}/`

Examples:
- `posts/article.md` → `posts/article-zh/`
- `translate/ai-future.md` → `translate/ai-future-zh/`

## Conflict Resolution

If the output directory already exists, rename the existing one to `{name}.backup-YYYYMMDD-HHMMSS/` before creating the new one. Never overwrite existing results.
