---
name: llm-wiki
description: Use when building or maintaining a persistent personal knowledge base (second brain) in Obsidian where an LLM incrementally ingests sources, updates entity/concept pages, maintains cross-references, and keeps a synthesis current. Triggers include "second brain", "Obsidian wiki", "personal knowledge management", "ingest this paper/article/book", "build a research wiki", "compound knowledge", "Memex", or whenever the user wants knowledge to accumulate across sessions instead of being re-derived by RAG on every query.
context: fork
version: 2.9.0
author: claude-code-skills
license: MIT
tags: [knowledge-management, obsidian, second-brain, pkm, rag-alternative, wiki, karpathy, memex]
compatible_tools: [claude-code, codex-cli, cursor, antigravity, opencode, gemini-cli]
---

# LLM Wiki — Second Brain for Claude Code + Obsidian

Inspired by Andrej Karpathy's LLM Wiki pattern ([gist](https://gist.github.com/karpathy/442a6bf555914893e9891c11519de94f)). This skill turns Claude Code (or any agent CLI) into a disciplined wiki maintainer that **incrementally builds and maintains** a persistent, interlinked Obsidian vault as you feed it sources. The knowledge compounds — cross-references, contradictions, and synthesis are already there when you query.

## Core principle

Most LLM+docs workflows are **RAG**: retrieve fragments at query time, synthesize from scratch, forget. The wiki is **compounding**: sources are read once, integrated into a persistent markdown knowledge base, and kept current. You curate and ask; the LLM reads, files, cross-references, and maintains.

> Obsidian is the IDE. The LLM is the programmer. The wiki is the codebase.

## When to use

- **Personal**: track goals, health, psychology, journaling, self-improvement
- **Research**: deep dives over weeks on a topic — papers, articles, reports, evolving thesis
- **Book companion**: file chapters as you read; build a fan-wiki-style companion for characters, themes, plot threads
- **Business/team**: internal wiki fed by Slack, meeting notes, calls — LLM does maintenance nobody else wants to do
- **Competitive analysis, due diligence, trip planning, course notes, hobby deep-dives**

**Do NOT use when:** you need one-shot Q&A over a fixed document (use RAG), you don't plan to add sources over time, or you don't want Obsidian in the loop.

## Architecture (three layers)

```
vault/
├── raw/                    # Layer 1 — IMMUTABLE source of truth
│   ├── <source files>      # Articles, papers, PDFs, images, data
│   └── assets/             # Downloaded images from clipped articles
├── wiki/                   # Layer 2 — LLM-owned knowledge base
│   ├── index.md            # Content catalog (LLM updates every ingest)
│   ├── log.md              # Append-only timeline (## [YYYY-MM-DD] <op> | <title>)
│   ├── entities/           # Person/Org/Place pages
│   ├── concepts/           # Ideas, theories, frameworks
│   ├── sources/            # One summary page per ingested source
│   ├── comparisons/        # Cross-source analysis pages
│   └── synthesis/          # High-level syntheses, theses, overviews
├── CLAUDE.md               # Schema + conventions (Claude Code)
└── AGENTS.md               # Same content, for Codex/Cursor/Antigravity
```

- **Layer 1 (raw/)** — you own. LLM only reads; never writes.
- **Layer 2 (wiki/)** — LLM owns. It creates, updates, and cross-references pages. You read it.
- **Layer 3 (CLAUDE.md / AGENTS.md)** — the *schema*. Conventions, workflows, frontmatter rules. Co-evolved by you and the LLM.

## Three core operations

1. **Ingest** — LLM reads a source, discusses takeaways with you, writes a source summary, updates 10-15 relevant pages, updates index, appends to log. See `references/ingest-workflow.md`.
2. **Query** — LLM reads `index.md` first, drills into relevant pages, synthesizes with citations. Good answers get **filed back into the wiki** so explorations compound. See `references/query-workflow.md`.
3. **Lint** — Health check: contradictions, stale claims, orphan pages, missing cross-refs, concepts mentioned but lacking their own page, data gaps to fill with web search. See `references/lint-workflow.md`.

## Quick start

```bash
# 1. Initialize a vault (in Obsidian's vault directory)
python scripts/init_vault.py --path ~/vaults/research --topic "LLM interpretability"

# 2. Drop a source into raw/, then ingest
/wiki-ingest ~/vaults/research/raw/anthropic-monosemanticity.pdf

# 3. Ask questions (answers can be re-filed into the wiki)
/wiki-query "how does monosemanticity compare to mechanistic interpretability?"

# 4. Periodic health check
/wiki-lint

# 5. See the timeline
/wiki-log --last 10
```

## Slash commands (this plugin ships)

| Command | Purpose |
|---|---|
| `/wiki-init` | Bootstrap a fresh vault with schema files + starter structure |
| `/wiki-ingest <path>` | Read a source, discuss, update wiki, log it |
| `/wiki-query <question>` | Search wiki, synthesize answer, offer to file back |
| `/wiki-lint` | Run health check — contradictions, orphans, stale claims, gaps |
| `/wiki-log` | Show recent log entries (uses unix tools on `log.md`) |

## Sub-agents (this plugin ships)

| Agent | When dispatched |
|---|---|
| `wiki-ingestor` | Delegated ingest flow — reads source, proposes updates, applies after your approval |
| `wiki-linter` | Runs the health-check workflow independently, reports findings |
| `wiki-librarian` | Answers queries using index-first search, synthesizes with citations |

## Python tools (`scripts/`)

All tools are **standard library only** (no pip installs). Run with `python scripts/<tool>.py --help`.

| Script | Purpose |
|---|---|
| `init_vault.py` | Create folder structure + seed CLAUDE.md, AGENTS.md, index.md, log.md |
| `ingest_source.py` | Helper: extract text/frontmatter from a source file, ready for LLM review |
| `update_index.py` | Regenerate `index.md` from wiki page frontmatter (category, date, source count) |
| `append_log.py` | Append a standardized log entry `## [YYYY-MM-DD] <op> \| <title>` |
| `wiki_search.py` | BM25 search over wiki pages (standalone fallback when index.md isn't enough) |
| `lint_wiki.py` | Find orphans (no inbound links), stale pages, missing cross-refs, broken links |
| `graph_analyzer.py` | Compute link graph stats — hubs, orphans, clusters, disconnected components |
| `export_marp.py` | Render a wiki page (or subtree) to a Marp slide deck |

## Cross-tool compatibility

The vault's **schema** lives in CLAUDE.md (Claude Code) or AGENTS.md (Codex/Cursor/Antigravity/OpenCode). The same content works in both. This plugin ships both templates. For per-tool setup instructions see `references/cross-tool-setup.md`.

```
CLAUDE.md       → Claude Code
AGENTS.md       → Codex CLI, Cursor, Antigravity, OpenCode, Gemini CLI
.cursorrules    → legacy Cursor (pre-AGENTS.md)
```

The scripts are pure Python stdlib → run identically everywhere. Only the loader file changes per tool.

## Obsidian setup (recommended)

- **Obsidian Web Clipper** — browser extension; converts web articles to markdown and drops them in `raw/`
- **Download images locally** — Settings → Files and links → Attachment folder path = `raw/assets/`. Settings → Hotkeys → bind "Download attachments for current file" to `Ctrl+Shift+D`
- **Graph view** — see hubs/orphans; essential for spotting structural problems
- **Marp plugin** — Markdown-based slide decks directly from wiki pages
- **Dataview plugin** — dynamic tables/lists over page frontmatter (tags, dates, source counts)
- **Git** — the vault is a plain markdown repo; version it

Full setup walkthrough: `references/obsidian-setup.md`

## Why this works (vs plain RAG)

| Plain RAG | LLM Wiki |
|---|---|
| Rediscover knowledge each query | Knowledge accumulates |
| Cross-references re-computed every time | Cross-references pre-written and maintained |
| Contradictions surface only if you ask | Contradictions flagged during ingest |
| Exploration disappears into chat history | Good answers re-filed as new pages |
| Scales by embeddings infrastructure | Scales by markdown + `index.md` + optional local search |

At ~100 sources / hundreds of pages, `index.md` + filesystem search is enough. Past that, layer in a local search tool like [qmd](https://github.com/tobi/qmd) or use `scripts/wiki_search.py`.

## Related skills (chains via `context: fork`)

This skill is marked `context: fork` so other skills can chain into it:

- **`para-memory-files`** — PARA-method memory; complementary as long-term personal memory that feeds sources into the wiki
- **`obsidian-vault`** (mattpocock) — lightweight Obsidian note helper; this skill is the maintained-wiki layer on top
- **`rag-design`** — when wiki outgrows ~500 pages, use rag-design to bolt on a retrieval layer
- **`mcp-design`** — expose the wiki as an MCP tool
- **`agent-communication`** — for multi-agent wiki maintenance (ingestor + linter + librarian)

## Reference docs

- `references/wiki-schema.md` — full vault layout, page frontmatter, naming conventions
- `references/page-formats.md` — entity, concept, source, comparison, synthesis templates
- `references/ingest-workflow.md` — the detailed ingest flow the wiki-ingestor agent follows
- `references/query-workflow.md` — query patterns, citation format, re-filing answers
- `references/lint-workflow.md` — health-check heuristics
- `references/obsidian-setup.md` — Obsidian plugins, hotkeys, vault config
- `references/cross-tool-setup.md` — per-tool setup (Codex, Cursor, Antigravity, etc.)
- `references/memex-principles.md` — Bush's Memex, why the LLM changes the maintenance math

## Templates (`assets/`)

- `CLAUDE.md.template`, `AGENTS.md.template`, `.cursorrules.template` — schema loaders per tool
- `index.md.template`, `log.md.template` — starter index and log
- `page-templates/` — entity, concept, source-summary, comparison, synthesis
- `example-vault/` — small worked example you can study or copy

## Iron rule

**The LLM never edits files in `raw/`.** Ever. Sources are immutable. All LLM writes go to `wiki/`. If you need to correct a source, do it in `raw/` yourself — then re-ingest.
