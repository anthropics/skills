# Obsidian Conventions

Knowledge about Obsidian's data model and conventions that the MCP server doesn't enforce but agents should follow.

## Vault Structure

A vault is a plain directory of markdown files. No database, no proprietary format.

```
my-vault/
  .obsidian/          # App config (plugins, themes, hotkeys), not accessible via MCP
  Daily Notes/        # Common convention, configurable in app
  Templates/          # Template files, also configurable
  Attachments/        # Images, PDFs, often set in app settings
  Projects/
    project-a.md
  README.md
```

`.obsidian/` is blocked by the MCP server's path sandbox. You cannot read or write app config files.

## Internal Links

Obsidian uses `[[wikilinks]]`, not standard markdown links. When writing or patching note content, prefer wikilink syntax.

| Syntax | Result |
|--------|--------|
| `[[Note Name]]` | Link to note |
| `[[Note Name|Display Text]]` | Link with alias (pipe separates name from display text) |
| `[[Note Name#Heading]]` | Link to heading |
| `[[Note Name#^block-id]]` | Link to block |
| `![[Note Name]]` | Embed (transclude) entire note |
| `![[image.png]]` | Embed image |
| `![[Note Name#Heading]]` | Embed specific section |

Standard `[markdown](links)` work but won't participate in Obsidian's graph view, backlinks, or rename refactoring.

## Daily Notes

Common convention: one note per day in a `Daily Notes/` folder. Default filename format: `YYYY-MM-DD` (e.g., `2024-03-15.md`). The folder name and date format are configurable per-vault in `.obsidian/daily-notes.json`.

When creating daily notes via MCP, use the `YYYY-MM-DD.md` format unless the user specifies otherwise.

## Frontmatter

YAML block delimited by `---` at the top of the file. Common standard fields:

```yaml
---
title: Note Title
tags:
  - project
  - status/active
aliases:
  - alternate name
date: 2024-03-15
cssclasses:
  - custom-class
---
```

- `tags`: array of strings, supports nested tags (`parent/child`)
- `aliases`: alternative names for wikilink resolution
- `cssclasses`: Obsidian-specific styling
- `date`, `created`, `modified`: no enforced format, but ISO 8601 is conventional

The MCP server validates frontmatter before writing (no functions, no symbols, string keys only).

## Tags

Two sources, both valid in Obsidian:

1. **Frontmatter tags**: `tags: [foo, bar]` in YAML block
2. **Inline tags**: `#foo` anywhere in the body text

Nested tags use `/`: `#project/active`, `#status/done`. The MCP `manage_tags` tool merges both sources for `list` but only modifies frontmatter for `add`/`remove`.

## Templates

Obsidian's core Templates plugin uses these variables:

| Variable | Expands to |
|----------|-----------|
| `{{title}}` | Note title (filename without extension) |
| `{{date}}` | Current date (format configurable in settings) |
| `{{time}}` | Current time (format configurable in settings) |
| `{{date:FORMAT}}` | Date with custom Moment.js format, e.g. `{{date:YYYY-MM-DD}}` |
| `{{time:FORMAT}}` | Time with custom format |

**The MCP server does not expand template variables.** If you write `{{date}}` via `write_note`, it stays as literal text. Template expansion only happens when inserting templates through the Obsidian app.

## Obsidian URIs

Format: `obsidian://open?vault=VaultName&file=path/to/note`

The MCP server includes `obsidianUri` in search results and read responses. These URIs only work when the Obsidian desktop app is running. They open the note in the app's editor.

URL encoding rules apply: spaces become `%20`, special characters are percent-encoded.

## Common Folder Patterns

| Pattern | Usage |
|---------|-------|
| `Daily Notes/` | One note per day |
| `Templates/` | Template files for new notes |
| `Attachments/` or `assets/` | Images, PDFs, other media |
| `Archive/` | Completed or inactive notes |
| `Inbox/` | Quick capture, unsorted notes |

These are conventions, not requirements. Every vault is different. Use `list_directory` to discover the actual structure before assuming folder names.
