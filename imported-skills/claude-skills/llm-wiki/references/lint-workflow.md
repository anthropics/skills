# Lint Workflow

Periodic health-check the LLM runs when the user runs `/wiki-lint` or dispatches the `wiki-linter` sub-agent. Run this at least weekly, and always after a batch ingest.

## Goal

Keep the wiki healthy as it grows. Surface problems for the user to review.

## Pass 1 — mechanical checks (script)

Run `python scripts/lint_wiki.py --vault .` to get a report on:

- **Orphans** — pages with zero inbound `[[wikilinks]]`
- **Broken links** — wikilinks pointing to non-existent pages
- **Stale pages** — pages whose `updated:` frontmatter is older than 90 days (tune via `--stale-days`)
- **Missing frontmatter** — pages lacking `title`, `category`, or `summary`
- **Duplicate titles** — two or more pages sharing the same title
- **Log gap** — no log entry in the last 14 days (tune via `--log-gap-days`)

Run `python scripts/graph_analyzer.py --vault .` for structural stats:

- Hubs (inbound/outbound) — likely well-placed
- Sinks — pages that don't link out; may need cross-referencing
- Connected components — if > 1, parts of the wiki are disconnected islands

## Pass 2 — semantic checks (LLM)

The script can't catch these. The LLM must read and think.

### A. Contradictions

Scan pages whose `updated:` is recent. For each, check whether it contradicts any existing page. If so:
- Add a `> ⚠️ Contradiction:` callout to both pages
- Log with `op: note`
- Surface to user: "I found a potential contradiction between X and Y. Want me to investigate?"

### B. Stale claims

For each flagged stale page, ask:
- Does a newer source now contradict this?
- Is a "Key facts" bullet likely to be outdated (person changed role, company pivoted, etc.)?
- If yes, suggest to user: "Page X says Y. This may be outdated — do you want me to search for newer sources?"

### C. Concepts mentioned but without their own page

Grep for common patterns: `[[concept:xxx]]`, phrases like "see also", concept-shaped nouns mentioned across 3+ pages but with no dedicated page.

Suggest new pages to create.

### D. Cross-reference gaps

For each page, check: do all entities and concepts mentioned have wikilinks? If a concept is referenced as plain text in 3+ places, promote it to a wikilink (and create a stub page if needed).

### E. Index drift

Compare `index.md` against actual `wiki/` contents. If out of sync, either regenerate (`update_index.py`) or patch inline.

## Pass 3 — report

Present findings to the user as a single markdown report:

```markdown
# Wiki lint — 2026-04-10

**Total pages:** 87  **Components:** 1  **Last log:** 2026-04-09

## Found
- ⚠️ 3 contradictions (wiki/concepts/x, wiki/sources/y, wiki/sources/z)
- 12 orphan pages (mostly new entities)
- 2 broken links (wiki/concepts/x → [[foo-bar]] no such page)
- 4 stale pages (>90 days, no re-ingest)
- 5 concepts mentioned across 3+ pages without their own page

## Suggested actions
1. Investigate contradiction between [[sources/a]] and [[sources/b]]
2. Create concept page for "attention masking" (mentioned in 4 sources)
3. Re-ingest [[sources/c]] — stale and contradicted by newer sources
4. Fix broken link in [[concepts/x]]
5. Cross-reference the 12 orphans (most belong under [[synthesis/overview]])

Want me to run these in order, or pick specific ones?
```

Append a `lint` entry to `log.md` summarizing what was found and what was fixed.

## Frequency

- **Weekly** — light pass, script-only (`lint_wiki.py` + quick review)
- **After batch ingests** — always
- **Monthly** — full pass including semantic checks
- **Before sharing the wiki** — full pass plus an extra review
