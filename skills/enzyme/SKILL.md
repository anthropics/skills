---
name: enzyme
description: >
  Explore an Obsidian vault using Enzyme — surface connections between ideas,
  find latent patterns across notes. Use when the user wants to explore their
  thinking, draw connections, or search their vault by concept rather than keyword.
license: MIT
compatibility: Requires the enzyme CLI (brew install jshph/tap/enzyme). Designed for agents with shell access.
allowed-tools: Bash Read Glob Grep
metadata:
  author: jshph
  version: "0.3.2"
  homepage: https://enzyme.garden
---

# Enzyme — Vault Exploration Skill

## What Enzyme Is

Enzyme turns your Obsidian vault into something you can converse with. It works through three concepts:

**Entities** are the tags (`#travel`), wikilinks (`[[open questions]]`), and folders (`/people`) in your vault. Each one is a semantic cluster — a gathering of content you've already organized by how you think. Hierarchical tags like `#travel/pyrenees` create nested clusters.

**Catalysts** are AI-generated questions anchored to each entity. They probe what's latent in that cluster. A catalyst for `#travel` might be: *"What kept pulling you forward when something was asking you to stay?"* — and content surfaces because it **speaks to the question**, not because it contains matching words. The same entity explored through different catalysts reveals different material.

**Petri** is the live readout of what's growing in your vault — which entities are active, what catalysts have formed around them, where the thinking is heading. Each entity carries temporal metadata: when you last engaged it, how frequently, whether it's active or dormant. Dormant entities are often the most interesting — they surface threads you've stopped noticing.

Content retrieval works by **resonance with catalyst questions**, not keyword matching. The catalysts encode the vault's own vocabulary for its themes — they're handles the vault has grown. Reaching for them connects you to content that generic search terms won't find.

## Prerequisites

Install the `enzyme` CLI:

```bash
brew install jshph/tap/enzyme
```

Or download from [GitHub releases](https://github.com/jshph/enzyme/releases). For a self-contained version with bundled binary and model, see [enzyme-skill](https://github.com/jshph/enzyme-skill).

Enzyme resolves the vault path in this order: `-p` flag > `ENZYME_VAULT_ROOT` env var > current directory. If `ENZYME_VAULT_ROOT` is set (check with `echo $ENZYME_VAULT_ROOT`), all commands automatically target the right vault.

### Check vault initialization

```bash
ls ${ENZYME_VAULT_ROOT:-.}/.enzyme/enzyme.db
```

- If `.enzyme/enzyme.db` exists: vault is ready. Run `enzyme petri` to begin.
- If it doesn't exist: run `enzyme init` to initialize the vault.

## Commands

### `enzyme petri` — See what's growing

Returns JSON with trending entities and their catalysts.

```bash
enzyme petri                  # Default: top 10 entities
enzyme petri -n 5             # Top 5 entities
```

### `enzyme catalyze "query"` — Search by concept

Activates the vault's catalysts to surface resonant content. Returns JSON with matched excerpts, file paths, and contributing catalysts.

```bash
enzyme catalyze "feeling stuck"
enzyme catalyze "tension between efficiency and presence" -n 20
```

### `enzyme init` — Initialize a vault

```bash
enzyme init                           # Initialize current directory
enzyme init -p /path/to/vault
enzyme init --guide "vault guide content"
```

### `enzyme refresh` — Update the index

Lightweight update that only re-runs if content has changed. Use `--full` to force a complete re-index if results seem off.

```bash
enzyme refresh                        # Incremental update
enzyme refresh --full                 # Force full re-index
```

### `--quiet` mode (agent/headless use)

Both `enzyme init --quiet` and `enzyme refresh --quiet` output compact JSON to stdout that includes full petri data. **Do not follow up with a separate `enzyme petri` call** — it's already in the response under the `petri` key.

When `refresh --quiet` detects the vault is fresh (nothing to do), the output is `{ "fresh": true, "petri": ... }`. When stale, the full output includes indexing stats, capabilities, warnings, entity changes, and petri.

### `enzyme apply <target>` — Project catalysts onto external content

Indexes an external directory using the current vault's catalysts. After applying, search the target with `enzyme catalyze "query" --vault <target>`.

```bash
enzyme apply ./research-papers           # Apply current vault's catalysts
enzyme apply ./papers --source ~/vault   # Explicit source vault
```

### When to use `catalyze` vs text search

**Use text search (grep) when you have a concrete anchor** — something that exists verbatim in the vault:
- People: "Sarah", `[[Dr. Chen]]`
- Tags: `#productivity`, `#enzyme/pmf`
- Links/titles: `[[On Writing Well]]`, `[[meeting notes]]`
- Files: `Readwise/Articles/...`, book titles, paper names
- Proper nouns: places, companies, projects

**Use `catalyze` when you only have a theme/concept** — no anchor to grep:
- "What have I written about feeling stuck?" (no name, no tag, no title)
- "cost of care in algorithmic interfaces" (academic framing — vault won't use these words)
- "tension between efficiency and presence" (conceptual, not anchored)

The test: would these exact words appear in their notes? Names and tags always do. Abstract/academic language rarely does — vaults use personal, concrete phrasing.

### Reading JSON output

Enzyme commands return JSON. Read the output directly — do not pipe through Python or jq.

**`enzyme petri`** — each entity object has:
- `name`, `type`, `frequency`, `activity_trend`, `days_since_last_seen`
- `catalysts`: array of `{ text, context }`

**`enzyme catalyze`** — response has:
- `results`: array of `{ file_path, content, similarity }`
- `top_contributing_catalysts`: array of `{ text, entity, contribution_count }`

## Workflow

1. **Discover vault context.** Scan for structural files that reveal the vault's shape:
   - Look for `**/MOC.md`, `**/Index.md`, `**/agents.md`, `**/guide.md`, `**/ENZYME_GUIDE.md`, and `**/_index.md`
   - Read any discovered files to understand vault structure, conventions, and user preferences
   - If the vault is **not initialized** (no `.enzyme/enzyme.db`), build a guide by stacking the files with context headers describing what each one is, then pipe to `enzyme init --guide`. Example:
     ```bash
     enzyme init --guide "$(printf '=== guide.md (entity weights) ===\n'; cat guide.md; printf '\n\n=== CLAUDE.md (vault workflow instructions) ===\n'; cat CLAUDE.md)"
     ```
   - If the vault **is initialized**, use this context to orient your petri reading

2. **Start with petri.** Run `enzyme petri` to see the landscape — what's active, what's dormant, what catalysts have formed. (If you just ran `init --quiet` or `refresh --quiet`, petri is already in the JSON output — skip this step.)

3. **Ground in evidence.** Before making observations, use catalysts from the petri to run `enzyme catalyze` searches. Look across entities for patterns — what the user keeps returning to, avoiding, or circling.

4. **Open with a question.** Synthesize a single 10-20 word question that names something the user is *doing* across their vault — then ground it with their words. Follow [petri-guide.md](references/petri-guide.md).

5. **Follow threads.** Use catalysts from petri results to drive searches based on what the user responds to. A catalyst for one entity often surfaces content connecting to another.

6. **Present search results** following [search-guide.md](references/search-guide.md). Lead with their words from matched excerpts, notice tensions across results, suggest specific next searches using catalyst language.
