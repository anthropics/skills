# Ingest Workflow

The detailed flow the LLM follows when the user runs `/wiki-ingest <path>` or dispatches the `wiki-ingestor` sub-agent.

## Inputs

- Path to a source file (inside `raw/` — if not, prompt the user to move it first)
- The current state of `wiki/` (especially `index.md`)

## Step-by-step

### 1. Prepare the brief

Run `python scripts/ingest_source.py --vault . --source <path> --json` to get:
- title guess
- word count
- preview (first 1200 chars)
- suggested summary-page path
- whether a summary page already exists (→ **merge mode**)

### 2. Read the source

Use the Read tool on the source directly. For PDFs, use the Read tool's PDF support. For images clipped locally to `raw/assets/`, inspect them if the LLM has vision.

### 3. Discuss with the user

Before writing anything, tell the user:
- Title and author(s)
- 2-3 sentence TL;DR
- Key claims (bulleted, 3-7 items)
- Which existing wiki pages this source will touch
- Any **contradictions** with existing pages

**Wait for user to confirm or redirect.** This is the "LLM makes edits, you browse" loop — the user is in the loop.

### 4. Create / merge the source summary page

Path: `wiki/sources/<slug>.md`. Use the **source summary** template from `references/page-formats.md`. Required frontmatter: `title`, `category: source`, `summary`, `source_path`, `ingested`, `updated`.

**Merge mode** (summary page already exists): append a new "## Re-ingest <date>" section at the bottom with what changed. Do not overwrite.

### 5. Identify entities and concepts

For each entity and concept mentioned in the source:
- Check if a page exists in `wiki/entities/` or `wiki/concepts/`
- **If yes:** update it. Add a new bullet under "Appears in" / "Used in" pointing to this source. Update "Key claims" if this source adds or contradicts a claim. Update `sources:` count in frontmatter. Update `updated:` to today.
- **If no:** create a new page from the entity/concept template. Start with the minimum: title, summary, one key fact sourced from this reading, link back to this source.

Typical ingest touches **5-15 pages** across `entities/`, `concepts/`, and sometimes `comparisons/`.

### 6. Flag contradictions explicitly

If the new source contradicts an existing page, add a callout to BOTH pages:

```markdown
> ⚠️ **Contradiction** — [[sources/new]] claims X but [[sources/old]] claims ~X.
> Unresolved as of 2026-04-10.
```

Log contradictions in `log.md` with `op: note`.

### 7. Update synthesis (optional)

If the source meaningfully shifts a `synthesis/` page's thesis, revise the "Thesis" paragraph and append a dated entry under "How this synthesis has changed". Don't rewrite history; append.

### 8. Update `index.md`

Either:
- Run `python scripts/update_index.py --vault .` to regenerate the entire index from frontmatter, OR
- Edit the relevant category sections inline (faster for small ingests).

### 9. Append to `log.md`

Run `python scripts/append_log.py --vault . --op ingest --title "<title>" --detail "<detail>"`.

The detail line should list which pages were touched:

```
## [2026-04-10] ingest | Anthropic Monosemanticity
Added sources/monosemanticity.md. Updated concepts/sparse-autoencoder,
concepts/polysemanticity, entities/anthropic-interpretability-team. Flagged
contradiction with sources/distributed-representations.
```

### 10. Report back to the user

Summary the user sees in chat:
- Source summary page created/updated
- Pages touched (bulleted wikilinks so the user can click through)
- Contradictions flagged (if any)
- Suggested next sources to pursue

## After-ingest tips

- **Big ingest?** Run `python scripts/lint_wiki.py --vault .` to check for new orphans or broken links.
- **Graph check?** Run `python scripts/graph_analyzer.py --vault .` to see if the new page is well-connected.
- **Open Obsidian graph view** — the user should see the new page attached to the existing cluster.
