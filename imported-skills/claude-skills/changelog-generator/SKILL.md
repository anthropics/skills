---
name: "changelog-generator"
description: "Produce consistent, auditable release notes from Conventional Commits. Separates commit parsing, semantic-bump logic, and changelog rendering for automated releases with editorial control. Use when cutting a release, generating CHANGELOG.md from git history, computing the next semantic version from commits, automating release notes in CI, or planning a hotfix/rollback. Examples: 'generate the changelog for v1.4.0', 'what version bump do these commits require', 'we need an emergency hotfix process'."
---

# Changelog Generator

**Tier:** POWERFUL  
**Category:** Engineering  
**Domain:** Release Management / Documentation

## Overview

Use this skill to produce consistent, auditable release notes from Conventional Commits. It separates commit parsing, semantic bump logic, and changelog rendering so teams can automate releases without losing editorial control.

## Core Capabilities

- Parse commit messages using Conventional Commit rules
- Detect semantic bump (`major`, `minor`, `patch`) from commit stream
- Render Keep a Changelog sections (`Added`, `Changed`, `Fixed`, etc.)
- Generate release entries from git ranges or provided commit input
- Enforce commit format with a dedicated linter script
- Support CI integration via machine-readable JSON output

## When to Use

- Before publishing a release tag
- During CI to generate release notes automatically
- During PR checks to block invalid commit message formats
- In monorepos where package changelogs require scoped filtering
- When converting raw git history into user-facing notes

## Key Workflows

### 1. Generate Changelog Entry From Git

```bash
python3 scripts/generate_changelog.py \
  --from-tag v1.3.0 \
  --to-tag v1.4.0 \
  --next-version v1.4.0 \
  --format markdown
```

### 2. Generate Entry From stdin/File Input

```bash
git log v1.3.0..v1.4.0 --pretty=format:'%s' | \
  python3 scripts/generate_changelog.py --next-version v1.4.0 --format markdown

python3 scripts/generate_changelog.py --input commits.txt --next-version v1.4.0 --format json
```

### 3. Update `CHANGELOG.md`

```bash
python3 scripts/generate_changelog.py \
  --from-tag v1.3.0 \
  --to-tag HEAD \
  --next-version v1.4.0 \
  --write CHANGELOG.md
```

### 4. Compute the Next Version From Commits

When the user has not decided the next version, derive it instead of guessing:

```bash
git log v1.3.0..HEAD --oneline | \
  python3 scripts/version_bumper.py --current-version 1.3.0 --output-format json
```

Output JSON contains `recommended_version`, `bump_type` (`major`/`minor`/`patch`/`none`), and with `--include-commands` the exact `git tag` commands. Feed `recommended_version` into `generate_changelog.py --next-version`. Pre-releases: add `--prerelease alpha|beta|rc`. Input must be real `git log --oneline` output (hex hashes); a sample lives at `assets/sample_git_log.txt`.

### 5. Lint Commits Before Merge

```bash
python3 scripts/commit_linter.py --from-ref origin/main --to-ref HEAD --strict --format text
```

Or file/stdin:

```bash
python3 scripts/commit_linter.py --input commits.txt --strict
cat commits.txt | python3 scripts/commit_linter.py --format json
```

## Conventional Commit Rules

Supported types:

- `feat`, `fix`, `perf`, `refactor`, `docs`, `test`, `build`, `ci`, `chore`
- `security`, `deprecated`, `remove`

Breaking changes:

- `type(scope)!: summary`
- Footer/body includes `BREAKING CHANGE:`

SemVer mapping:

- breaking -> `major`
- non-breaking `feat` -> `minor`
- all others -> `patch`

## Script Interfaces

- `python3 scripts/generate_changelog.py --help`
  - Reads commits from git or stdin/`--input`
  - Renders markdown or JSON
  - Optional in-place changelog prepend
- `python3 scripts/commit_linter.py --help`
  - Validates commit format
  - Returns non-zero in `--strict` mode on violations

## Common Pitfalls

1. Mixing merge commit messages with release commit parsing
2. Using vague commit summaries that cannot become release notes
3. Failing to include migration guidance for breaking changes
4. Treating docs/chore changes as user-facing features
5. Overwriting historical changelog sections instead of prepending

## Best Practices

1. Keep commits small and intent-driven.
2. Scope commit messages (`feat(api): ...`) in multi-package repos.
3. Enforce linter checks in PR pipelines.
4. Review generated markdown before publishing.
5. Tag releases only after changelog generation succeeds.
6. Keep an `[Unreleased]` section for manual curation when needed.

## Hotfix Severity & SLAs

When a release goes wrong, classify before acting (full procedures in [references/hotfix-procedures.md](references/hotfix-procedures.md)):

| Severity | Definition | SLA | Approval |
|---|---|---|---|
| P0 — Critical | Outage, data loss, exploited vulnerability | Fix deployed ≤ 2h; emergency deploy bypasses normal gates | Engineering Lead + On-call Manager |
| P1 — High | Major feature broken, significant user impact | Fix deployed ≤ 24h; expedited review | Engineering Lead + Product Manager |
| P2 — Medium | Minor issues, limited impact | Next release cycle | Standard PR review |

Hotfix branch comes from the last stable tag, contains the minimal fix only, and gets its own patch-bump changelog entry via the workflow above.

## Rollback Triggers

Pre-commit to these thresholds before tagging; roll back when any fires:

| Trigger | Threshold |
|---|---|
| Error rate spike | > 2x baseline within 30 min |
| Performance degradation | > 50% latency increase |
| Feature failure | Core functionality broken |
| Security incident | Vulnerability being exploited |
| Data corruption | Database integrity compromised |

Prefer feature-flag disable over code rollback; database rollbacks only for non-destructive migrations (forward-only migrations preferred). See [references/hotfix-procedures.md](references/hotfix-procedures.md).

## References

- [references/ci-integration.md](references/ci-integration.md)
- [references/changelog-formatting-guide.md](references/changelog-formatting-guide.md)
- [references/monorepo-strategy.md](references/monorepo-strategy.md)
- [references/hotfix-procedures.md](references/hotfix-procedures.md)
- [README.md](README.md)

## Release Governance

Use this release flow for predictability:

1. Lint commit history for target release range.
2. Generate changelog draft from commits.
3. Manually adjust wording for customer clarity.
4. Validate semver bump recommendation.
5. Tag release only after changelog is approved.

## Output Quality Checks

- Each bullet is user-meaningful, not implementation noise.
- Breaking changes include migration action.
- Security fixes are isolated in `Security` section.
- Sections with no entries are omitted.
- Duplicate bullets across sections are removed.

## CI Policy

- Run `commit_linter.py --strict` on all PRs.
- Block merge on invalid conventional commits.
- Auto-generate draft release notes on tag push.
- Require human approval before writing into `CHANGELOG.md` on main branch.

## Monorepo Guidance

- Prefer commit scopes aligned to package names.
- Filter commit stream by scope for package-specific releases.
- Keep infra-wide changes in root changelog.
- Store package changelogs near package roots for ownership clarity.

## Failure Handling

- If no valid conventional commits found: fail early, do not generate misleading empty notes.
- If git range invalid: surface explicit range in error output.
- If write target missing: create safe changelog header scaffolding.
