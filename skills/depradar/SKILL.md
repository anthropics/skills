---
name: depradar
description: "Dependency breaking-change radar. TRIGGER when: user asks about breaking changes, outdated dependencies, upgrade risks, migration issues, or runs /depradar. Scans package.json, requirements.txt, pyproject.toml, go.mod, Cargo.toml, Gemfile, pom.xml for outdated packages, extracts breaking changes from release notes, finds impacted files in the codebase, and surfaces community pain signals from GitHub Issues, Stack Overflow, Reddit, and Hacker News."
---

# /depradar — Dependency Breaking-Change Radar

Scan your project's dependencies for breaking changes, find which files in YOUR codebase will break, and surface community reports — all in one command.

## What It Does

1. **Reads dependency files** — `package.json`, `requirements.txt`, `pyproject.toml`, `go.mod`, `Cargo.toml`, `Gemfile`, `pom.xml`
2. **Checks registries** — npm, PyPI, crates.io, Maven Central, GitHub Releases
3. **Extracts breaking changes** — from release notes, CHANGELOGs, Conventional Commits
4. **Scans your codebase** — Python AST, JS/TS import tracking, grep fallback
5. **Searches community** — GitHub Issues, Stack Overflow, Reddit, Hacker News
6. **Scores 0-100** — severity × recency × codebase impact × community pain

Zero external dependencies. Python 3.8+ stdlib only.

## Install

```bash
npx skills add tarun-khatri/depradar-skill
```

Or manually:
```bash
git clone https://github.com/tarun-khatri/depradar-skill.git ~/.claude/skills/depradar-skill
```

## Usage

```
/depradar                    # Scan all production deps
/depradar stripe openai      # Check specific packages
/depradar --quick            # 60s timeout, top 5
/depradar --deep             # 300s, exhaustive community search
/depradar --emit=json        # Machine-readable output
/depradar --diagnose         # Show API key config status
```

## How Claude Should Execute

```bash
cd "{PROJECT_ROOT}" && python3 "{SKILL_ROOT}/scripts/depradar.py" {ARGS}
```

Where `{SKILL_ROOT}` is `~/.claude/skills/depradar-skill/` (or wherever installed).

## Configuration (Optional)

Create `~/.config/depradar/.env`:
```bash
GITHUB_TOKEN=ghp_...            # 60 → 5,000 req/hr (free, no scopes needed)
SCRAPECREATORS_API_KEY=sc_...   # Enables Reddit signals
STACKOVERFLOW_API_KEY=...       # 300 → 10,000 req/day
```

Zero-config covers ~80% of the skill's value (npm, PyPI, crates.io, Maven, GitHub, SO, HN all work without keys).

## Supported Ecosystems

| File | Ecosystem |
|------|-----------|
| `package.json` / `yarn.lock` / `pnpm-lock.yaml` | npm |
| `requirements.txt` / `pyproject.toml` / `Pipfile` | PyPI |
| `Cargo.toml` | crates.io |
| `go.mod` | Go |
| `pom.xml` | Maven |
| `Gemfile` | RubyGems |

## Links

- **Repository**: [github.com/tarun-khatri/depradar-skill](https://github.com/tarun-khatri/depradar-skill)
- **ClawHub**: `clawhub install depradar`
- **Skills.sh**: `npx skills add tarun-khatri/depradar-skill`
- **Tests**: 838 tests across 38 test files
- **License**: MIT
