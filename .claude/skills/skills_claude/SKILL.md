---
name: skills-claude-conventions
description: Development conventions and patterns for skills_claude. Python project with freeform commits.
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

Follow these commit message conventions based on 19 analyzed commits.

### Commit Style: Free-form Messages

### Message Guidelines

- Average message length: ~46 characters
- Keep first line concise and descriptive
- Use imperative mood ("Add feature" not "Added feature")


*Commit message example*

```text
Package 8 skills as distributable .skill files for upload
```

*Commit message example*

```text
Add 8 new skills: foundation, standards, and development series
```

*Commit message example*

```text
Add link to Agent Skills specification website (#160)
```

*Commit message example*

```text
Fix links in agent skills specification (#159)
```

*Commit message example*

```text
Split agent-skills-spec into separate authoring and client integration guides (#148)
```

*Commit message example*

```text
Add doc-coauthoring skill and update example skills (#134)
```

*Commit message example*

```text
Move example skills into dedicated folder and create minimal top-level folder structure (#129)
```

*Commit message example*

```text
Update example skills and rename 'artifacts-builder' (#112)
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

## Error Handling

### Error Handling Style: Try-Catch Blocks


*Standard error handling pattern*

```typescript
try {
  const result = await riskyOperation()
  return result
} catch (error) {
  console.error('Operation failed:', error)
  throw new Error('User-friendly message')
}
```

## Common Workflows

These workflows were detected from analyzing commit patterns.

### Feature Development

Standard feature implementation workflow

**Frequency**: ~13 times per month

**Steps**:
1. Add feature implementation
2. Add tests for feature
3. Update documentation

**Files typically involved**:
- `**/*.test.*`

**Example commit sequence**:
```
Add 3rd Party notices (#4)
Add initial Agent Skills Spec (#2)
Small tweak to blog link (#7)
```

### Add New Skill

Adds a new skill to the repository, including its SKILL.md and any supporting files.

**Frequency**: ~1 times per month

**Steps**:
1. Create a new folder under skills/ (or previously examples/, document-skills/, office-examples/).
2. Add SKILL.md to the new skill folder.
3. Optionally add LICENSE.txt, scripts/, templates/, examples/, or reference/ subfolders and files as needed.
4. Update skills/README.md or .claude-plugin/marketplace.json if necessary.

**Files typically involved**:
- `skills/*/SKILL.md`
- `skills/*/LICENSE.txt`
- `skills/*/scripts/*`
- `skills/*/templates/*`
- `skills/*/examples/*`
- `skills/*/reference/*`
- `skills/README.md`
- `.claude-plugin/marketplace.json`

**Example commit sequence**:
```
Create a new folder under skills/ (or previously examples/, document-skills/, office-examples/).
Add SKILL.md to the new skill folder.
Optionally add LICENSE.txt, scripts/, templates/, examples/, or reference/ subfolders and files as needed.
Update skills/README.md or .claude-plugin/marketplace.json if necessary.
```

### Update Or Export Example Skills

Bulk updates or exports of example skills, often including renaming, reorganizing, or synchronizing multiple skill folders and their contents.

**Frequency**: ~1 times per month

**Steps**:
1. Modify, move, or rename multiple skill folders (e.g., from examples/ to skills/, or document-skills/).
2. Update SKILL.md and supporting files for each skill.
3. Update marketplace.json or skills/README.md as needed.

**Files typically involved**:
- `skills/*/SKILL.md`
- `skills/*/LICENSE.txt`
- `skills/*/scripts/*`
- `skills/*/templates/*`
- `skills/*/examples/*`
- `skills/*/reference/*`
- `.claude-plugin/marketplace.json`
- `skills/README.md`

**Example commit sequence**:
```
Modify, move, or rename multiple skill folders (e.g., from examples/ to skills/, or document-skills/).
Update SKILL.md and supporting files for each skill.
Update marketplace.json or skills/README.md as needed.
```

### Package Skills For Distribution

Packages one or more skills into distributable .skill (zip) files for upload or API use.

**Frequency**: ~1 times per month

**Steps**:
1. Run packaging scripts or commands.
2. Generate .skill files in the dist/ directory.
3. Ensure SKILL.md and all necessary assets are included in each .skill file.

**Files typically involved**:
- `dist/*.skill`
- `skills/*/SKILL.md`
- `skills/*/scripts/*`
- `skills/*/templates/*`

**Example commit sequence**:
```
Run packaging scripts or commands.
Generate .skill files in the dist/ directory.
Ensure SKILL.md and all necessary assets are included in each .skill file.
```

### Update Spec Or Documentation

Updates to specification or documentation files, such as splitting, fixing links, or adding references.

**Frequency**: ~1 times per month

**Steps**:
1. Edit spec/agent-skills-spec.md or related spec/*.md files.
2. Optionally split or merge documentation files.
3. Update README.md with new links or notes.

**Files typically involved**:
- `spec/agent-skills-spec.md`
- `spec/skill-authoring.md`
- `spec/skill-client-integration.md`
- `README.md`

**Example commit sequence**:
```
Edit spec/agent-skills-spec.md or related spec/*.md files.
Optionally split or merge documentation files.
Update README.md with new links or notes.
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
