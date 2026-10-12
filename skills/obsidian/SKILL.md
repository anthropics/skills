---
name: obsidian
description: >
  Activate when the user mentions their Obsidian vault, notes, tags,
  frontmatter, or daily notes. Teaches sharp edges and error recovery
  for the MCP-Obsidian server that tool descriptions alone don't cover.
metadata:
  version: "2.0"
  author: bitbonsai
---

# Obsidian Skill

## Gotchas

1. **patch_note rejects multi-match by default.** With `replaceAll: false`, if `oldString` appears more than once the call fails and returns `matchCount`. Set `replaceAll: true` only when you mean it, or add surrounding context to make the match unique.

2. **patch_note matches inside frontmatter.** The replacement runs against the full file including the YAML block. A generic string like `title:` will match frontmatter fields. Include enough context to target the right occurrence.

3. **patch_note forbids empty strings.** Both `oldString` and `newString` must be non-empty and non-whitespace. To delete text, use `newString` with a single space or restructure the note with `write_note`.

4. **search_notes returns minified JSON.** Fields are abbreviated: `p` (path), `t` (title), `ex` (excerpt), `mc` (matchCount), `ln` (lineNumber), `uri` (obsidianUri). Hard cap of 20 results regardless of `limit`.

5. **search_notes multi-word queries score terms individually AND as a phrase.** Each term is OR-matched, so a document matching any term appears in results. The full phrase gets an additional scoring boost.

6. **write_note auto-creates directories.** Parent folders are created recursively. In `append`/`prepend` mode, if the note doesn't exist it's created. Frontmatter is merged (new keys override) in append/prepend; replaced entirely in overwrite.

7. **delete_note requires exact path confirmation.** `confirmPath` must be character-identical to `path`. No normalization, no trailing-slash tolerance. Mismatch silently fails with `success: false`.

8. **move_file needs double confirmation.** Both `confirmOldPath` and `confirmNewPath` must exactly match their counterparts. Use `move_note` for markdown renames (text-aware, no confirmation needed); use `move_file` only for binary files or when you need binary-safe moves.

9. **manage_tags reads from two sources but writes to one.** `list` merges frontmatter tags + inline `#hashtags`. `add`/`remove` only modify the frontmatter `tags` array. Inline tags are never touched.

10. **read_multiple_notes never rejects.** Uses `allSettled` internally. Failed files appear in the `err` array; successful ones in `ok`. Always check both. Hard limit of 10 paths per call.

## Error Recovery

| Error | Next step |
|-------|-----------|
| patch_note "Found N occurrences" | Add surrounding lines to `oldString` to make it unique, or set `replaceAll: true` |
| delete_note / move_file confirmation mismatch | Re-read the note path with `read_note` or `list_directory`, then retry with the exact string |
| search_notes returns 0 results | Try single keywords instead of phrases, toggle `searchFrontmatter`, or broaden with partial terms |
| read_multiple_notes partial `err` | Verify failed paths with `list_directory`, fix typos or missing extensions, retry only failed ones |

## Resources

Load these only when needed, not on every invocation.

- [Tool Patterns](resources/tool-patterns.md) - read when you need a tool's response shape, mode details, or the move_note vs move_file decision
- [Obsidian Conventions](resources/obsidian-conventions.md) - read when creating/writing note content (link syntax, frontmatter fields, daily note format, template variables)
