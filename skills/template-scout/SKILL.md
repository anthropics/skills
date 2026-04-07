---
name: template-scout
description: Search GitHub for open-source project templates/boilerplates, score and rank them, and maintain a persistent URL registry for cross-session reuse.
triggers:
  - scout
  - template
  - boilerplate
  - scaffold
  - starter
  - find template
  - search github template
---

# Template Scout

Search GitHub and skill registries for open-source project templates, score them, and build a persistent registry that improves determinism across sessions.

## Commands

- **`/scout "description"`** — Search and display ranked results
- **`/scout save "category"`** — Search, rank, and persist to registry
- **`/scout list`** — List all saved registry categories
- **`/scout refresh "category"`** — Re-search and update a stale category
- **`/scout use "repo-url-or-name"`** — Clone a template into current directory

## Core Workflow

### Step 1: Check Registry First

Before any search, check if `~/.claude/template-registry/index.json` has a matching category. If found and `lastUpdated` is within 7 days, return cached results instead of re-searching.

```bash
cat ~/.claude/template-registry/index.json 2>/dev/null
cat ~/.claude/template-registry/<category>.json 2>/dev/null
```

### Step 2: Build Search Queries

Convert the user's description into 2-3 GitHub search queries. Apply the **iterative refinement** pattern — start broad, then narrow based on initial results.

Query construction rules:
- Extract **tech stack** keywords (e.g., "flutter", "nextjs", "fastapi")
- Extract **domain** keywords (e.g., "expense tracker", "saas", "dashboard")
- Extract **type** keywords (e.g., "template", "boilerplate", "starter", "scaffold")
- Combine into `gh search repos` queries

Example for "Flutter expense tracker app":
```bash
# Query 1: Direct match
gh search repos "expense tracker" --language=Dart --topic=flutter --stars=">10" --sort=stars --json fullName,description,stargazersCount,url,license,updatedAt,language -L 15

# Query 2: Broader
gh search repos "finance app flutter template" --stars=">5" --sort=stars --json fullName,description,stargazersCount,url,license,updatedAt,language -L 15

# Query 3: Category-based
gh search repos "flutter starter" --topic=finance --sort=stars --json fullName,description,stargazersCount,url,license,updatedAt,language -L 10
```

### Step 3: Score and Rank

For each result, compute a score (0-100) using these weighted signals:

| Signal | Weight | Scoring |
|--------|--------|---------|
| Stars | 30% | log10(stars) * 15, capped at 30 |
| Recent activity | 25% | 25 if updated in last 3 months, 15 if last 6 months, 5 if last year, 0 otherwise |
| License | 15% | MIT/Apache/BSD = 15, LGPL = 10, GPL/AGPL = 7, none = 0 |
| Has README | 10% | 10 if description length > 50 chars (proxy for docs quality) |
| Topic relevance | 20% | 4 points per matching topic keyword, capped at 20 |

Deduplicate results across queries by `fullName`. Sort by score descending.

### Step 4: Present Results

Display top 10 results in this format:

```
## Template Scout Results: "<query>"

| # | Repo | Stars | Score | License | Last Updated | Description |
|---|------|-------|-------|---------|-------------|-------------|
| 1 | owner/repo | 1.2k | 92 | MIT | 2026-03 | Short description... |
| ... |

### Quick Actions
- To save: `/scout save "category-name"`
- To clone #1: `/scout use owner/repo`
```

### Step 5: Persist to Registry

When saving, write two files:

**Category file** at `~/.claude/template-registry/<category>.json`:
```json
{
  "category": "flutter-expense-tracker",
  "description": "Flutter expense tracker app templates",
  "lastUpdated": "2026-04-02T00:00:00Z",
  "searchQueries": ["expense tracker flutter", "finance app flutter template"],
  "templates": [
    {
      "repo": "owner/repo-name",
      "url": "https://github.com/owner/repo-name",
      "stars": 1234,
      "description": "A Flutter expense tracking app with charts",
      "license": "MIT",
      "language": "Dart",
      "topics": ["flutter", "expense-tracker", "finance"],
      "lastUpdated": "2026-03-15",
      "score": 92
    }
  ]
}
```

**Update index** at `~/.claude/template-registry/index.json`:
```json
{
  "categories": {
    "flutter-expense-tracker": {
      "file": "flutter-expense-tracker.json",
      "description": "Flutter expense tracker app templates",
      "count": 10,
      "lastUpdated": "2026-04-02T00:00:00Z"
    }
  }
}
```

### Step 6: Clone Template (`/scout use`)

When the user wants to use a template:
```bash
# Clone into current directory
gh repo clone <owner/repo> ./<repo-name> -- --depth 1

# Remove .git to start fresh
rm -rf ./<repo-name>/.git

# Report what was cloned
echo "Cloned <repo> into ./<repo-name>"
echo "Tech stack: <language>"
echo "License: <license>"
```

## Registry Management

### Staleness Check
- Entries older than 7 days are considered stale
- On stale access, suggest: "Registry entry is X days old. Run `/scout refresh <category>` to update."

### Merge Logic
When refreshing, merge new results with existing:
- Keep entries that still exist on GitHub
- Add new entries not previously seen
- Update star counts and dates for existing entries
- Re-score all entries

## Search Fallbacks

If `gh` returns few results (<3), try these fallback sources in order:

1. **WebSearch**: `"<keywords> template" site:github.com`
2. **GitHub Topics API**: `gh api /search/repositories?q=topic:<keyword>+topic:template`
3. **Awesome lists**: Search for `awesome-<keyword>` repos that curate templates

## Tips for Best Results

- Be specific about tech stack: "Next.js SaaS dashboard" > "web app"
- Include the purpose: "React Native expense tracker" > "React Native app"
- Mention key features: "FastAPI with auth and Stripe" > "FastAPI template"

## What This Skill Does NOT Do

- Does not evaluate code quality inside repos (use code review skills for that)
- Does not automatically install dependencies
- Does not modify cloned templates (that's your job after cloning)
- Does not search private repositories
