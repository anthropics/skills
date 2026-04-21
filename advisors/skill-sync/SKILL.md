---
name: skill-sync
description: Track upstream repository changes and identify which SEAL security skills need updating. Use when checking if skills are stale, reviewing recent commits to source documentation, or planning skill maintenance. Triggers on questions about "updating skills," "sync with repo," "what changed in frameworks," or "which skills need refresh."
---

# Skill Sync Utility

Keep SEAL security skills synchronized with the upstream frameworks repository.

## Skill-to-Source Mapping

Each skill derives content from specific documentation paths:

| Skill | Source Paths in `docs/pages/` |
|-------|-------------------------------|
| wallet-security-advisor | `wallet-security/` |
| incident-response-advisor | `incident-management/` |
| insider-threat-advisor | `dprk-it-workers/` |
| infrastructure-security-advisor | `infrastructure/` |
| web3-security-awareness | `awareness/` |
| smart-contract-testing-advisor | `security-testing/` |
| audit-preparation-advisor | `external-security-reviews/` |
| community-security-advisor | `community-management/` |
| opsec-advisor | `opsec/` |
| safe-harbor-advisor | `safe-harbor/` |

## Sync Workflow

### 1. Check Recent Changes

Run from the frameworks repository root:

```bash
# Changes in last 30 days
git log --oneline --since="30 days ago" -- docs/pages/

# Changes since specific date
git log --oneline --since="2024-01-01" -- docs/pages/

# Changes since last skill update (use commit hash)
git log --oneline <last-sync-commit>..HEAD -- docs/pages/
```

### 2. Identify Affected Skills

```bash
# See which directories changed
git diff --stat <last-sync-commit>..HEAD -- docs/pages/ | grep -E "^\s*docs/pages/[^/]+/"

# Or use this one-liner to extract unique directories
git diff --name-only <last-sync-commit>..HEAD -- docs/pages/ | cut -d'/' -f3 | sort -u
```

### 3. Review Specific Changes

```bash
# Detailed changes for a specific area
git log -p --since="30 days ago" -- docs/pages/wallet-security/

# Just file names that changed
git diff --name-only <commit>..HEAD -- docs/pages/opsec/
```

### 4. Check Merged PRs (GitHub CLI)

```bash
# Recent merged PRs
gh pr list --state merged --limit 20

# PRs merged since date
gh pr list --state merged --search "merged:>2024-01-01"

# PRs touching specific path
gh pr list --state merged --search "path:docs/pages/wallet-security"
```

## Sync Status File

Maintain a sync status file at `~/.claude/skills/advisors/.sync-status.json`:

```json
{
  "last_sync": "2024-12-18",
  "last_commit": "abc123def",
  "repo": "security-alliance/frameworks",
  "skills": {
    "wallet-security-advisor": {
      "last_updated": "2024-12-18",
      "source_commit": "abc123def",
      "source_paths": ["docs/pages/wallet-security/"]
    }
  }
}
```

## Quick Sync Check Script

Save as `check-sync.sh` in the skill directory:

```bash
#!/bin/bash
# Run from frameworks repo root

SINCE="${1:-30 days ago}"
echo "=== Changes since: $SINCE ==="
echo ""

declare -A SKILL_MAP=(
  ["wallet-security"]="wallet-security-advisor"
  ["incident-management"]="incident-response-advisor"
  ["dprk-it-workers"]="insider-threat-advisor"
  ["infrastructure"]="infrastructure-security-advisor"
  ["awareness"]="web3-security-awareness"
  ["security-testing"]="smart-contract-testing-advisor"
  ["external-security-reviews"]="audit-preparation-advisor"
  ["community-management"]="community-security-advisor"
  ["opsec"]="opsec-advisor"
  ["safe-harbor"]="safe-harbor-advisor"
)

changed_dirs=$(git diff --name-only HEAD~50..HEAD -- docs/pages/ 2>/dev/null | cut -d'/' -f3 | sort -u)

echo "Skills that may need updating:"
echo "------------------------------"
for dir in $changed_dirs; do
  skill="${SKILL_MAP[$dir]}"
  if [ -n "$skill" ]; then
    count=$(git log --oneline --since="$SINCE" -- "docs/pages/$dir/" | wc -l)
    if [ "$count" -gt 0 ]; then
      echo "  $skill ($count commits in $dir/)"
    fi
  fi
done

echo ""
echo "Recent commits by area:"
echo "-----------------------"
for dir in "${!SKILL_MAP[@]}"; do
  count=$(git log --oneline --since="$SINCE" -- "docs/pages/$dir/" 2>/dev/null | wc -l)
  if [ "$count" -gt 0 ]; then
    echo ""
    echo "[$dir] -> ${SKILL_MAP[$dir]}"
    git log --oneline --since="$SINCE" -- "docs/pages/$dir/" | head -5
  fi
done
```

## Update Priority Matrix

When changes are detected, prioritize updates:

| Change Type | Priority | Action |
|-------------|----------|--------|
| New major section added | High | Add to skill or create new skill |
| Existing content significantly revised | High | Review and update skill |
| New subsection or details added | Medium | Consider adding to references |
| Minor edits, typos, formatting | Low | Usually no skill update needed |
| New FAQ added | Medium | May warrant skill FAQ update |

## Manual Sync Process

1. **Pull latest changes**
   ```bash
   cd ~/repo/frameworks
   git pull origin develop
   ```

2. **Run sync check**
   ```bash
   ./check-sync.sh "30 days ago"
   ```

3. **Review changed files**
   ```bash
   git diff --stat <last-sync>..HEAD -- docs/pages/<area>/
   ```

4. **Update affected skills**
   - Read changed source files
   - Update SKILL.md if core guidance changed
   - Update reference files if details changed

5. **Update sync status**
   ```bash
   # Record new sync point
   echo "Last sync: $(date +%Y-%m-%d) at $(git rev-parse --short HEAD)"
   ```

6. **Validate updated skills**
   ```bash
   python3 ~/.claude/skills/skill-creator/scripts/quick_validate.py <skill-path>
   ```

## GitHub Actions Integration (Optional)

For automated notifications, add to `.github/workflows/`:

```yaml
name: Skill Sync Check
on:
  push:
    branches: [main, develop]
    paths:
      - 'docs/pages/**'

jobs:
  check-skills:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 50

      - name: Check affected skills
        run: |
          echo "Changed documentation areas:"
          git diff --name-only HEAD~1..HEAD -- docs/pages/ | cut -d'/' -f3 | sort -u
```

## Reference Files

- See `references/source-mapping.md` for detailed path-to-skill mapping
