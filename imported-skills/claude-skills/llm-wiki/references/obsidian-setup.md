# Obsidian Setup

Recommended Obsidian configuration for an LLM Wiki vault. None of this is strictly required — the wiki is just markdown files — but these settings remove friction.

## Open the vault

1. Obsidian → "Open folder as vault" → pick your initialized vault
2. The vault already has `wiki/`, `raw/`, `CLAUDE.md`, `AGENTS.md`

## Settings → Files and Links

- **Default location for new notes:** `wiki/`
- **New link format:** `Shortest path when possible` (keeps wikilinks clean)
- **Use `[[Wikilinks]]`:** ON
- **Attachment folder path:** `raw/assets/` (so clipped images land in `raw/`, not `wiki/`)
- **Automatically update internal links:** ON

## Settings → Hotkeys

Search for and bind:
- **"Download attachments for current file"** → `Ctrl/Cmd + Shift + D`
- **"Open graph view"** → `Ctrl/Cmd + G`

## Core plugins to enable

- **Graph view** — see the shape of your wiki. Hubs, orphans, clusters.
- **Backlinks** — pane showing who links to the current page. Critical for browsing.
- **Outgoing links** — complementary pane.
- **Templates** — enable and set the template folder to `wiki/.templates`
- **Tag pane** — tag-driven navigation
- **Search** — obviously
- **Page preview** — hover a wikilink to preview
- **Canvas** — visual exploration, useful for synthesis work

## Recommended community plugins

- **Obsidian Web Clipper** (browser extension, not a plugin) — clip articles to `raw/articles/` as markdown
- **Dataview** — query over frontmatter. Dynamic tables of "all concept pages touched by 3+ sources".
- **Marp for Obsidian** — render any markdown with `marp: true` frontmatter as a slide deck inside Obsidian. Pairs with `scripts/export_marp.py`.
- **Templater** — dynamic templates (optional, you can use the LLM for this)
- **Advanced Tables** — easier markdown table editing
- **Git** — commit on save, or hook into system git

## Dataview examples

Pages with 3+ sources:
```dataview
table updated, sources
from "wiki/concepts"
where sources >= 3
sort updated desc
```

Recently updated synthesis pages:
```dataview
list
from "wiki/synthesis"
sort updated desc
limit 10
```

Orphans (Dataview can't see inbound links — use the lint script for this).

## Git workflow

```bash
cd <vault>
git init
git add .
git commit -m "init wiki"

# After every session:
git add wiki/ log.md index.md
git commit -m "ingest: <source>"
```

The vault is a plain markdown repo. Version history, branching, collaboration — free.

## Tips

- **Use the graph view daily** — it's the fastest way to see structural drift
- **Pin `index.md`, `log.md`, and the active `synthesis/` page** to the sidebar tabs
- **Split view** — wiki on the left, chat/CLI on the right. You browse while the LLM edits.
- **Enable "strict line breaks"** so your LLM's markdown renders the way the LLM expects
- **Use images aggressively** — download them locally, reference from pages. The LLM can read them with its vision tool when needed.
