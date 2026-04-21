# Dynamic Skill-to-Source Discovery

Rather than hardcoding paths (which get stale), use these dynamic approaches to discover what needs syncing.

## Directory Mapping Convention

Skills follow a naming convention that maps to source directories:

```
Skill Name Pattern         → Source Directory Pattern
*-security-advisor         → related security topic
*-advisor                  → related topic
```

The mapping is maintained in the skill's SKILL.md description, which references what it covers.

## Dynamic Discovery Script

Save as `discover-mapping.sh`:

```bash
#!/bin/bash
# Discover skill-to-source mapping dynamically

SKILLS_DIR="${1:-$HOME/.claude/skills/advisors}"
DOCS_DIR="${2:-docs/pages}"

echo "=== Dynamic Skill-Source Mapping ==="
echo ""

# For each skill, extract topics from its description
for skill_dir in "$SKILLS_DIR"/*/; do
    skill_name=$(basename "$skill_dir")
    skill_file="$skill_dir/SKILL.md"

    if [ -f "$skill_file" ]; then
        # Extract description line from frontmatter
        desc=$(grep -A1 "^description:" "$skill_file" | tail -1)
        echo "Skill: $skill_name"
        echo "  Description excerpt: ${desc:0:80}..."
        echo ""
    fi
done
```

## Keyword-Based Change Detection

Instead of hardcoded paths, search for changes by keyword relevance:

```bash
#!/bin/bash
# Find changes relevant to a skill by keywords

SKILL="$1"
SINCE="${2:-30 days ago}"

# Define keywords per skill (more maintainable than paths)
case "$SKILL" in
    wallet-security-advisor)
        KEYWORDS="wallet|seed|multisig|hardware.*wallet|ledger|trezor"
        ;;
    incident-response-advisor)
        KEYWORDS="incident|response|seal.?911|hack|breach|playbook"
        ;;
    insider-threat-advisor)
        KEYWORDS="dprk|insider|worker|hiring|vetting"
        ;;
    infrastructure-security-advisor)
        KEYWORDS="infrastructure|dns|ddos|cloud|server"
        ;;
    web3-security-awareness)
        KEYWORDS="awareness|phishing|scam|social.?engineering"
        ;;
    smart-contract-testing-advisor)
        KEYWORDS="testing|fuzz|invariant|foundry|slither|audit"
        ;;
    audit-preparation-advisor)
        KEYWORDS="audit|auditor|review|pre-audit|remediation"
        ;;
    community-security-advisor)
        KEYWORDS="discord|telegram|twitter|community|raid"
        ;;
    opsec-advisor)
        KEYWORDS="opsec|operational.?security|travel|threat.?model"
        ;;
    safe-harbor-advisor)
        KEYWORDS="safe.?harbor|whitehat|rescue|bounty"
        ;;
    *)
        echo "Unknown skill: $SKILL"
        exit 1
        ;;
esac

echo "Checking changes for: $SKILL"
echo "Keywords: $KEYWORDS"
echo "Since: $SINCE"
echo "---"

# Find commits with relevant changes
git log --oneline --since="$SINCE" --all -i --grep="$KEYWORDS" -- docs/pages/

# Find files with keyword in path or content changes
git diff --name-only $(git log -1 --format=%H --since="$SINCE")..HEAD -- docs/pages/ | \
    grep -iE "$KEYWORDS" || echo "(no path matches)"
```

## Comprehensive Sync Check

```bash
#!/bin/bash
# check-all-skills.sh - Check all skills for potential updates

REPO_DIR="${1:-.}"
SINCE="${2:-30 days ago}"

cd "$REPO_DIR" || exit 1

echo "=== SEAL Skills Sync Check ==="
echo "Repository: $(pwd)"
echo "Checking changes since: $SINCE"
echo "Current commit: $(git rev-parse --short HEAD)"
echo ""

# Get all changed directories under docs/pages
changed=$(git diff --name-only HEAD~100..HEAD -- docs/pages/ 2>/dev/null | \
          cut -d'/' -f3 | sort -u | grep -v '^\s*$')

if [ -z "$changed" ]; then
    echo "No documentation changes detected."
    exit 0
fi

echo "Changed documentation areas:"
echo "$changed" | while read dir; do
    count=$(git log --oneline --since="$SINCE" -- "docs/pages/$dir/" 2>/dev/null | wc -l)
    if [ "$count" -gt 0 ]; then
        echo "  - $dir/ ($count commits)"
    fi
done

echo ""
echo "Recent commit summary:"
git log --oneline --since="$SINCE" -- docs/pages/ | head -20
```

## GitHub API Approach

For more robust tracking, use GitHub API:

```bash
#!/bin/bash
# Use GitHub CLI to check merged PRs affecting docs

REPO="security-alliance/frameworks"
SINCE="2024-01-01"

# List merged PRs touching docs
gh pr list \
    --repo "$REPO" \
    --state merged \
    --search "merged:>$SINCE" \
    --json number,title,mergedAt,files \
    --jq '.[] | select(.files[].path | startswith("docs/pages/")) |
          {number, title, merged: .mergedAt}'

# Or simpler - just PR titles
gh pr list \
    --repo "$REPO" \
    --state merged \
    --limit 50 \
    --json number,title,mergedAt \
    --template '{{range .}}#{{.number}} {{.title}} ({{.mergedAt}}){{"\n"}}{{end}}'
```

## Sync Status Tracking

Store sync state dynamically:

```bash
#!/bin/bash
# Record current sync state

SYNC_FILE="$HOME/.claude/skills/advisors/.sync-status"

echo "last_sync=$(date -I)" > "$SYNC_FILE"
echo "last_commit=$(git rev-parse HEAD)" >> "$SYNC_FILE"
echo "repo=$(git remote get-url origin)" >> "$SYNC_FILE"

echo "Sync state recorded to $SYNC_FILE"
cat "$SYNC_FILE"
```

Read sync state:

```bash
#!/bin/bash
# Check time since last sync

SYNC_FILE="$HOME/.claude/skills/advisors/.sync-status"

if [ -f "$SYNC_FILE" ]; then
    source "$SYNC_FILE"
    echo "Last sync: $last_sync"
    echo "Last commit: $last_commit"

    # Show commits since last sync
    git log --oneline "$last_commit"..HEAD -- docs/pages/
else
    echo "No sync status found. Run initial sync."
fi
```

## Best Practices

1. **Don't hardcode file paths** - They change as docs evolve
2. **Use keywords and grep** - More resilient to restructuring
3. **Track by commit hash** - Precise point-in-time reference
4. **Check PR descriptions** - Often contain context for changes
5. **Review before updating** - Not all doc changes need skill updates
