# Query Workflow

The flow the LLM follows when the user runs `/wiki-query <question>` or dispatches the `wiki-librarian` sub-agent.

## Core principle

**Read `index.md` first, then drill in.** Do NOT grep the entire wiki on every query — the index is there precisely so you don't have to.

## Step-by-step

### 1. Read `index.md`

The index is the catalog. Scan it and pick the 3-10 pages most likely to contain the answer. Pick across categories: a good query usually pulls from `synthesis/` for the big picture, `concepts/` for definitions, `sources/` for evidence, and `entities/` for context.

### 2. Read the picked pages

Read them in full. These are short, curated, and already cross-referenced. The wiki has done the hard work for you.

### 3. Follow wikilinks opportunistically

If a read page points to another page that's clearly relevant, follow it. Don't follow blindly — stop when you have enough.

### 4. Fall back to search if needed

If the index doesn't surface the right page, use:

```bash
python scripts/wiki_search.py --vault . --query "<terms>" --limit 5
```

BM25 search over wiki pages. Standard library only. Use when:
- The index is stale (flag this to the user — it means lint time)
- The user asks about something niche that doesn't have its own page yet
- You're doing a sweeping search across many pages

### 5. Synthesize the answer

Compose the answer as:
- A direct answer in 1-3 sentences
- Supporting detail, organized thematically
- **Inline citations** using wikilinks to source pages: `[[sources/monosemanticity]]`
- **A "Related pages" section** at the end with 3-5 wikilinks

### 6. Offer to re-file

**Every good answer is a candidate wiki page.** At the end of the answer, ask:

> _Should I file this as a new page in the wiki? Suggested location:
> `wiki/comparisons/sae-vs-probing.md` — or I can append it to an existing page._

If the user says yes:
- Pick the right category (most often `comparisons/` or `synthesis/`)
- Use the appropriate template
- Add frontmatter with `category`, `summary`, `sources` (count of cited sources), `updated`
- Update `index.md`
- Append to `log.md` with `op: create` and the question as the title

This is how the wiki compounds — explorations don't disappear into chat history.

## Output formats

Not every query wants a markdown answer. Offer the user:

- **Markdown page** (default) — filed back as a wiki page
- **Comparison table** — for "A vs B" questions
- **Marp slide deck** — via `python scripts/export_marp.py` on the synthesis page
- **Chart (matplotlib)** — for data-driven questions; save to `wiki/assets/charts/`
- **Obsidian Canvas** — for visual exploration (JSON format, stored at `wiki/canvases/`)

## Anti-patterns

- ❌ Read every page in the wiki on every query → use the index
- ❌ Answer without citations → every claim must link to a page
- ❌ Create a new page for a one-off trivial question → only file back answers worth keeping
- ❌ Invent content not in the wiki → if you don't know, say so and suggest a new source to ingest
- ❌ Skip the `log.md` entry when filing an answer back
