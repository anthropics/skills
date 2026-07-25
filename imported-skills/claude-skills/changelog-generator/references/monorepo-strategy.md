# Monorepo Changelog Strategy

## Approaches

| Strategy | When to use | Tradeoff |
|----------|-------------|----------|
| Single root changelog | Product-wide releases, small teams | Simple but loses package-level detail |
| Per-package changelogs | Independent versioning, large teams | Clear ownership but harder to see full picture |
| Hybrid model | Root summary + package-specific details | Best of both, more maintenance |

## Commit Scoping Pattern

Enforce scoped conventional commits to enable per-package filtering:

```
feat(payments): add Stripe webhook handler
fix(auth): handle expired refresh tokens
chore(infra): bump base Docker image
```

**Rules:**
- Scope must match a package/directory name exactly
- Unscoped commits go to root changelog only
- Multi-package changes get separate scoped commits (not one mega-commit)

## Filtering for Package Releases

```bash
# Generate changelog for 'payments' package only
git log v1.3.0..HEAD --pretty=format:'%s' | grep '^[a-z]*\(payments\)' | \
  python3 scripts/generate_changelog.py --next-version v1.4.0 --format markdown
```

## Ownership Model

- Package maintainers own their scoped changelog
- Platform/infra team owns root changelog
- CI enforces scope presence on all commits touching package directories
- Root changelog aggregates breaking changes from all packages for visibility
