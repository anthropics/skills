# Reusable CI Workflow for Claude Skills

This repository provides a reusable GitHub Actions workflow that any Claude skill implementation can use for automated testing and validation.

## Features

- **SKILL.md Validation** - Validates frontmatter format, required fields, and naming conventions
- **Zip Generation** - Creates installable `.zip` files uploaded as artifacts
- **Claude API Testing** - Uploads skill to Claude API to verify format is accepted
- **Claude Code Testing** - Integration test with Claude Code action

## Quick Start

### Single-Skill Repository

If your repository contains a single skill at the root:

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  test:
    uses: anthropics/skills/.github/workflows/skill-ci.yml@main
    with:
      skill_path: "."
    secrets:
      ANTHROPIC_API_KEY: ${{ secrets.ANTHROPIC_API_KEY }}
```

### Multi-Skill Repository

If your repository contains multiple skills in subdirectories:

```yaml
# .github/workflows/ci.yml
name: CI

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  test:
    uses: anthropics/skills/.github/workflows/skill-ci.yml@main
    with:
      skill_path: "skills"
      multi_skill: true
      test_skill_name: "my-skill"  # Which skill to use for API tests
    secrets:
      ANTHROPIC_API_KEY: ${{ secrets.ANTHROPIC_API_KEY }}
```

## Inputs

| Input | Required | Default | Description |
|-------|----------|---------|-------------|
| `skill_path` | No | `.` | Path to skill directory. Use `.` for single-skill repos or a subdirectory name for multi-skill repos |
| `skill_name` | No | auto | Name of the skill. Auto-detected from SKILL.md frontmatter if not provided |
| `multi_skill` | No | `false` | Set to `true` if the repository contains multiple skills in subdirectories |
| `run_api_test` | No | `true` | Whether to run the Claude API upload test |
| `run_claude_code_test` | No | `true` | Whether to run the Claude Code integration test |
| `test_skill_name` | No | first found | For multi-skill repos, which skill to use for API and Claude Code tests |

## Secrets

| Secret | Required | Description |
|--------|----------|-------------|
| `ANTHROPIC_API_KEY` | No | Anthropic API key for testing skill upload. If not provided, API and Claude Code tests will be skipped |

## What Gets Validated

### SKILL.md Format

The workflow validates that your `SKILL.md` file:

1. **Starts with YAML frontmatter** (between `---` markers)
2. **Has required fields:**
   - `name` - The skill identifier (should be lowercase with hyphens)
   - `description` - A description of what the skill does
3. **Has meaningful content** after the frontmatter

Example valid SKILL.md:

```markdown
---
name: my-awesome-skill
description: Creates amazing things when users ask for awesome content
---

# My Awesome Skill

Instructions for Claude on how to use this skill...
```

### Generated Artifacts

The workflow uploads generated `.zip` files as artifacts that can be:
- Downloaded from the GitHub Actions run
- Uploaded to Claude at https://claude.ai/settings/capabilities

## Example Repository Structure

### Single Skill

```
my-skill/
├── .github/
│   └── workflows/
│       └── ci.yml
├── SKILL.md
├── scripts/
│   └── helper.py
└── templates/
    └── default.html
```

### Multiple Skills

```
my-skills-collection/
├── .github/
│   └── workflows/
│       └── ci.yml
└── skills/
    ├── skill-one/
    │   ├── SKILL.md
    │   └── scripts/
    └── skill-two/
        ├── SKILL.md
        └── templates/
```

## Minimal Example

The simplest possible workflow for a single skill:

```yaml
name: CI
on: [push, pull_request]

jobs:
  test:
    uses: anthropics/skills/.github/workflows/skill-ci.yml@main
```

This will:
- Validate your SKILL.md format
- Generate a downloadable zip file
- Skip API tests (no secrets provided)

## Troubleshooting

### "Missing SKILL.md file"

Ensure your SKILL.md is in the correct location:
- For `skill_path: "."` → `./SKILL.md`
- For `skill_path: "skills"` with `multi_skill: true` → `./skills/*/SKILL.md`

### "Invalid frontmatter format"

Check that your SKILL.md:
1. Starts with `---` on the first line
2. Has a closing `---` after the YAML content
3. Contains valid YAML between the markers

### API test skipped

The API test requires `ANTHROPIC_API_KEY` secret. Add it to your repository:
1. Go to Settings → Secrets and variables → Actions
2. Click "New repository secret"
3. Name: `ANTHROPIC_API_KEY`
4. Value: Your Anthropic API key

## Contributing

Found an issue or want to improve the workflow? PRs welcome at [anthropics/skills](https://github.com/anthropics/skills).
