---
name: skills-claude-conventions
description: Development conventions and patterns for skills_claude. Python project with mixed commits.
---

# Skills Claude Conventions

> Generated from [Eaprime1/skills_claude](https://github.com/Eaprime1/skills_claude) on 2026-03-24

## Overview

This skill teaches Claude the development patterns and conventions used in skills_claude.

## Tech Stack

- **Primary Language**: Python
- **Architecture**: hybrid module organization
- **Test Location**: separate

## When to Use This Skill

Activate this skill when:
- Making changes to this repository
- Adding new features following established patterns
- Writing tests that match project conventions
- Creating commits with proper message format

## Commit Conventions

Follow these commit message conventions based on 42 analyzed commits.

### Commit Style: Mixed Style

### Prefixes Used

- `feat`
- `chore`

### Message Guidelines

- Average message length: ~56 characters
- Keep first line concise and descriptive
- Use imperative mood ("Add feature" not "Added feature")


*Commit message example*

```text
feat: add skills_claude ECC bundle (.claude/commands/update-or-export-example-skills.md)
```

*Commit message example*

```text
chore: update claude-api skill [auto-sync] (#729)
```

*Commit message example*

```text
Merge branch 'anthropics:main' into claude/skills-brainstorm-Nd4vz
```

*Commit message example*

```text
Merge pull request #2 from Eaprime1/ecc-tools/skills_claude-1774393541560
```

*Commit message example*

```text
feat: add skills_claude ECC bundle (.claude/commands/add-new-skill.md)
```

*Commit message example*

```text
feat: add skills_claude ECC bundle (.claude/commands/feature-development.md)
```

*Commit message example*

```text
feat: add skills_claude ECC bundle (.codex/agents/docs-researcher.toml)
```

*Commit message example*

```text
feat: add skills_claude ECC bundle (.codex/agents/reviewer.toml)
```

## Architecture

### Project Structure: Single Package

This project uses **hybrid** module organization.

### Guidelines

- This project uses a hybrid organization
- Follow existing patterns when adding new code

## Code Style

### Language: Python

### Naming Conventions

| Element | Convention |
|---------|------------|
| Files | kebab-case |
| Functions | camelCase |
| Classes | PascalCase |
| Constants | SCREAMING_SNAKE_CASE |

### Import Style: Relative Imports

### Export Style: Named Exports


*Preferred import style*

```typescript
// Use relative imports
import { Button } from '../components/Button'
import { useAuth } from './hooks/useAuth'
```

*Preferred export style*

```typescript
// Use named exports
export function calculateTotal() { ... }
export const TAX_RATE = 0.1
export interface Order { ... }
```

## Common Workflows

These workflows were detected from analyzing commit patterns.

### Feature Development

Standard feature implementation workflow

**Frequency**: ~19 times per month

**Steps**:
1. Add feature implementation
2. Add tests for feature
3. Update documentation

**Files typically involved**:
- `**/*.test.*`
- `**/api/**`

**Example commit sequence**:
```
Add 3rd Party notices (#4)
Add initial Agent Skills Spec (#2)
Small tweak to blog link (#7)
```

### Refactoring

Code refactoring and cleanup workflow

**Frequency**: ~2 times per month

**Steps**:
1. Ensure tests pass before refactor
2. Refactor code structure
3. Verify tests still pass

**Files typically involved**:
- `src/**/*`

**Example commit sequence**:
```
Reorganize the example skills (#1)
Adding more details to README (#3)
Add 3rd Party notices (#4)
```

### Add Or Update Skill

Adds a new skill or updates an existing skill, including its SKILL.md and related scripts/assets.

**Frequency**: ~2 times per month

**Steps**:
1. Create or update SKILL.md in skills/<skill-name>/
2. Add or update supporting scripts, templates, or assets in the skill's folder
3. If applicable, update marketplace or index files (e.g., .claude-plugin/marketplace.json)
4. Optionally, add language-specific guides or reference files

**Files typically involved**:
- `skills/*/SKILL.md`
- `skills/*/scripts/*.py`
- `skills/*/templates/*`
- `skills/*/reference/*`
- `.claude-plugin/marketplace.json`

**Example commit sequence**:
```
Create or update SKILL.md in skills/<skill-name>/
Add or update supporting scripts, templates, or assets in the skill's folder
If applicable, update marketplace or index files (e.g., .claude-plugin/marketplace.json)
Optionally, add language-specific guides or reference files
```

### Export Or Bundle Skills

Exports multiple skills as distributable bundles or updates the exported set of skills.

**Frequency**: ~1 times per month

**Steps**:
1. Aggregate or update SKILL.md and related files for all relevant skills
2. Generate distributable bundles (e.g., .skill files in dist/)
3. Update index/marketplace files if needed

**Files typically involved**:
- `dist/*.skill`
- `skills/*/SKILL.md`
- `.claude-plugin/marketplace.json`

**Example commit sequence**:
```
Aggregate or update SKILL.md and related files for all relevant skills
Generate distributable bundles (e.g., .skill files in dist/)
Update index/marketplace files if needed
```

### Office Skill Shared Module Update

Updates or reorganizes shared Office document processing modules (docx, pptx, xlsx) and their schemas/scripts.

**Frequency**: ~1 times per month

**Steps**:
1. Update or reorganize scripts in skills/{docx,pptx,xlsx}/scripts/office/
2. Update or add schemas in skills/{docx,pptx,xlsx}/scripts/office/schemas/
3. Update pack/unpack/validate scripts for each Office skill
4. Optionally, update SKILL.md or documentation for each skill

**Files typically involved**:
- `skills/docx/scripts/office/**/*`
- `skills/pptx/scripts/office/**/*`
- `skills/xlsx/scripts/office/**/*`
- `skills/docx/scripts/office/schemas/**/*`
- `skills/pptx/scripts/office/schemas/**/*`
- `skills/xlsx/scripts/office/schemas/**/*`
- `skills/docx/scripts/office/pack.py`
- `skills/pptx/scripts/office/pack.py`
- `skills/xlsx/scripts/office/pack.py`
- `skills/docx/SKILL.md`
- `skills/pptx/SKILL.md`
- `skills/xlsx/SKILL.md`

**Example commit sequence**:
```
Update or reorganize scripts in skills/{docx,pptx,xlsx}/scripts/office/
Update or add schemas in skills/{docx,pptx,xlsx}/scripts/office/schemas/
Update pack/unpack/validate scripts for each Office skill
Optionally, update SKILL.md or documentation for each skill
```

### Skill Creator Tooling Update

Updates scripts, references, or documentation in the skill-creator tool, including validation, packaging, and optimization scripts.

**Frequency**: ~1 times per month

**Steps**:
1. Update or add scripts in skills/skill-creator/scripts/
2. Update references or documentation in skills/skill-creator/references/
3. Update SKILL.md for skill-creator if needed

**Files typically involved**:
- `skills/skill-creator/scripts/*.py`
- `skills/skill-creator/references/*.md`
- `skills/skill-creator/SKILL.md`

**Example commit sequence**:
```
Update or add scripts in skills/skill-creator/scripts/
Update references or documentation in skills/skill-creator/references/
Update SKILL.md for skill-creator if needed
```

### Add Or Update Claude Api Skill

Adds or updates the claude-api documentation skill, including language-specific guides and shared references.

**Frequency**: ~1 times per month

**Steps**:
1. Add or update skills/claude-api/SKILL.md
2. Add or update language guides in skills/claude-api/{python,typescript,java,go,ruby,csharp,php,curl}/
3. Update shared documentation in skills/claude-api/shared/
4. Update marketplace or index if needed

**Files typically involved**:
- `skills/claude-api/SKILL.md`
- `skills/claude-api/*/claude-api.md`
- `skills/claude-api/*/README.md`
- `skills/claude-api/*/*.md`
- `skills/claude-api/shared/*.md`
- `.claude-plugin/marketplace.json`

**Example commit sequence**:
```
Add or update skills/claude-api/SKILL.md
Add or update language guides in skills/claude-api/{python,typescript,java,go,ruby,csharp,php,curl}/
Update shared documentation in skills/claude-api/shared/
Update marketplace or index if needed
```


## Best Practices

Based on analysis of the codebase, follow these practices:

### Do

- Use kebab-case for file names
- Prefer named exports

### Don't

- Don't deviate from established patterns without discussion

---

*This skill was auto-generated by [ECC Tools](https://ecc.tools). Review and customize as needed for your team.*
