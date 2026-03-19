______________________________________________________________________

## name: git-workflow description: > Git branch strategy with atomic commits and squash merges. Use when committing, branching, creating PRs, or any git operations

# Git Workflow

## Branch Strategy

```bash
git checkout main && git pull
git checkout -b feature/description
# work...
git add -p                            # Stage intentionally
git commit -m "Clear message"
git push -u origin feature/description
gh pr create --title "..." --body "..."
gh pr merge --squash
```

## Rules

- Never commit directly to main — feature branches + PRs only
- Atomic commits: one logical change per commit
- Squash merge keeps main history clean
- `git add -p` — stage intentionally, not `git add .`
