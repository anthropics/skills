# Tool Patterns

Per-tool behavioral knowledge beyond what tool descriptions provide.

## read_note

Response includes `content` (full markdown body) and `frontmatter` (parsed YAML object). `prettyPrint: true` indents the JSON response for readability but costs extra tokens.

## write_note

**Modes:**
- `overwrite` (default): replaces entire file; frontmatter is set to exactly what you pass (or omitted if null)
- `append`: adds content after existing body; merges frontmatter (new keys override existing)
- `prepend`: adds content before existing body; same frontmatter merge as append

Auto-creates parent directories recursively. In append/prepend, creates the file if it doesn't exist.

**Frontmatter validation** runs before writing. Functions, symbols, and non-string keys are rejected. Invalid dates produce warnings but don't block the write.

## patch_note

**Response shape:**
```json
{ "success": bool, "path": str, "message": str, "matchCount": int }
```

- Rejects if `oldString === newString`

**Recipe, safe single replacement:** Include the line before and after your target text in `oldString` to guarantee uniqueness.

## search_notes

**Response fields (minified):**
- `p`: path
- `t`: title (filename without `.md`)
- `ex`: excerpt (context around first match, truncated with `...`)
- `mc`: matchCount (total occurrences across all terms + filename)
- `ln`: lineNumber (1-based, position of first match)
- `uri`: Obsidian URI

**Scoring:** BM25 with k1=1.2, b=0.75. Multi-word queries score each term individually plus the full phrase as a bonus term.

**Limits:** Default 5, hard cap 20. `caseSensitive: false` by default (both query and corpus lowercased).

**Frontmatter/content toggle:**
- `searchContent: true` + `searchFrontmatter: false` (default): strips frontmatter before searching
- `searchFrontmatter: true`: includes YAML block in searchable text
- Both false: no results

## delete_note

**Response:** `{ "success": bool, "path": str, "message": str }`

`confirmPath` must be character-identical to `path`. No undo. Files only; directories return "Cannot delete: path is not a file."

## move_note

Text-aware move for markdown files. Reads source as UTF-8, writes to destination with `wx` flag (fails if target exists unless `overwrite: true`), then deletes source. No confirmation parameters needed.

**Response:** `{ "success": bool, "oldPath": str, "newPath": str, "message": str }`

## move_file

Binary-safe move. Requires double confirmation: `confirmOldPath === oldPath` AND `confirmNewPath === newPath`. Rejects directories. Falls back to copy+unlink for cross-filesystem moves.

**When to use which:**
- Renaming/moving `.md` files → `move_note`
- Moving images, PDFs, attachments → `move_file`

## read_multiple_notes

**Response:** `{ "ok": [...], "err": [...] }`

Hard limit: 10 paths. Uses `Promise.allSettled`, so it never throws on individual failures. Each `ok` entry has `path`, `obsidianUri`, and optionally `frontmatter`/`content` based on include flags. Each `err` entry has `path` and `error` message.

## manage_tags

**Operations:**
- `list`: returns merged set of frontmatter `tags` array + inline `#hashtags` (deduplicated)
- `add`: appends to frontmatter `tags` array only
- `remove`: removes from frontmatter `tags` array only; if no tags remain, deletes the `tags` field

Inline `#hashtag` occurrences in the note body are never modified.

**Response:** `{ "path": str, "operation": str, "tags": [str], "success": bool }`

## update_frontmatter

- `merge: true` (default): spreads existing frontmatter first, new values override: `{...existing, ...new}`
- `merge: false`: complete replacement of frontmatter

Content body is always preserved. Validates resulting frontmatter before writing. File must already exist.

## get_vault_stats

Metadata-only. Returns total notes, folders, vault size, and recently modified files. No file content read. Use this for vault overview before batch operations.

## get_notes_info

Metadata-only alternative to reading notes. Returns `path`, `size` (bytes), `modified` (ms timestamp), `hasFrontmatter` (heuristic: checks if file starts with `---\n`), and `obsidianUri`. Failed reads are silently omitted from results.

## list_directory

Returns files and directories. Non-note filenames (images, PDFs) are included. Hidden directories (`.obsidian/`, `.git/`) are filtered out.

## get_frontmatter

Extracts parsed frontmatter without reading body content. Lighter than `read_note` when you only need YAML fields.
