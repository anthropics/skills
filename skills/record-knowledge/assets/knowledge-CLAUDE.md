# Knowledge Base

Aggregated tacit knowledge from Claude Code work sessions.
One entry per file with YAML frontmatter.

## Structure

```
.claude/knowledge/
├── CLAUDE.md          # This index
└── entries/           # One entry per file (YAML frontmatter)
    ├── YYYYMMDD-HHMMSS-author-slug.md   # New format
    ├── <slug>.md                         # Legacy (no rename needed)
    └── ...
```

## Search

```bash
# Fuzzy search by filename
fd -e md . .claude/knowledge/entries/ | fzf

# Search by tag
rg '#pitfall' .claude/knowledge/entries/
rg '#docker.*#pitfall' .claude/knowledge/entries/

# List all titles
rg '^title:' .claude/knowledge/entries/

# Active entries only
rg '^status: active' .claude/knowledge/entries/
```

## Tag Registry

Add new tags here. Reuse existing tags when possible.

`#pitfall`

## Rules

- Entries are mutable — edit in place, rely on git for history
- Use `deprecated` only when knowledge is genuinely obsolete
- New entries use `YYYYMMDD-HHMMSS-author-slug.md` naming (timestamp + author for collision avoidance)
- Do NOT add links to subdirectory CLAUDE.md files — use tag search to find entries
- Existing entries without timestamp prefix remain as-is (no rename)
- See `/record-knowledge` skill for full details
