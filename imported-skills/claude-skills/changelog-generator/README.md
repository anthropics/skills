# Changelog Generator

Automates release notes from Conventional Commits with Keep a Changelog output and strict commit linting. Designed for CI-friendly release workflows.

## Quick Start

```bash
# Generate entry from git range
python3 scripts/generate_changelog.py \
  --from-tag v1.2.0 \
  --to-tag v1.3.0 \
  --next-version v1.3.0 \
  --format markdown

# Lint commit subjects
python3 scripts/commit_linter.py --from-ref origin/main --to-ref HEAD --strict --format text
```

## Included Tools

- `scripts/generate_changelog.py`: parse commits, infer semver bump, render markdown/JSON, optional file prepend
- `scripts/commit_linter.py`: validate commit subjects against Conventional Commits rules
- `scripts/version_bumper.py`: compute the recommended next version from `git log --oneline` output (`--current-version`, `--prerelease`, `--include-commands`)

## References

- `references/ci-integration.md`
- `references/changelog-formatting-guide.md`
- `references/monorepo-strategy.md`
- `references/hotfix-procedures.md` (hotfix severity SLAs + rollback triggers, absorbed from the retired release-manager skill)

## Installation

### Claude Code

```bash
cp -R engineering/changelog-generator ~/.claude/skills/changelog-generator
```

### OpenAI Codex

```bash
cp -R engineering/changelog-generator ~/.codex/skills/changelog-generator
```

### OpenClaw

```bash
cp -R engineering/changelog-generator ~/.openclaw/skills/changelog-generator
```
