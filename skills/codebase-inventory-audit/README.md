# Codebase Inventory Audit Skill

> Comprehensive codebase cleanup and documentation audit skill for Claude Code

A systematic workflow for auditing codebases to identify orphaned code, unused files, documentation gaps, and infrastructure bloat. Creates a single-source-of-truth **CODEBASE-STATUS.md** document.

## What This Skill Does

This skill guides Claude through a **10-step comprehensive audit process** that produces a detailed inventory of your codebase:

- ✅ **Routes/Pages Analysis** - Categorize all routes as Complete, Partial, Scaffolded, or Missing
- 🗄️ **Data Models Audit** - Identify active, infrastructure, and orphaned database models
- 📚 **Lib Directory Audit** - Find unused or stub library files
- 🧩 **Components Audit** - Detect orphaned React/UI components
- 📖 **Documentation Gap Analysis** - Flag outdated docs and missing documentation
- 🏗️ **Infrastructure Status** - Document deployed infrastructure and test coverage
- 🗑️ **Removal Candidates** - Categorized list of safe-to-remove vs needs-decision items
- 🎯 **Prioritized Action Items** - Recommended next steps with checkboxes

## When to Use This Skill

Use this skill when you need to:

- 🧹 Perform spring cleaning before a major release
- 📊 Create an accurate "single source of truth" inventory
- 🔍 Audit a new codebase you've inherited
- 📉 Identify and remove code bloat
- 🗂️ Update outdated documentation
- 🧪 Find test coverage gaps

## Features

### Automated Detection Scripts

Two Python scripts automate the most time-consuming parts:

**find_orphaned_models.py**
- Parses Prisma schema files
- Searches codebase for model usage patterns
- Reports models with zero usage

**find_unused_imports.py**
- Scans directories for files with zero imports
- Configurable file extensions
- Validates usage across codebase

### Parallel Execution Pattern

The workflow uses parallel Explore agents to minimize audit time:
- Routes analysis
- Model categorization
- Lib directory scan
- Component audit
- Documentation review

All running concurrently for maximum efficiency.

### Comprehensive Template

Includes a complete CODEBASE-STATUS.md template with:
- Executive summary tables
- Feature status matrix with emoji indicators
- Removal candidates inventory
- Prioritized action items
- Changelog tracking

## Installation

### Option 1: Install from .skill File

```bash
# Copy the .skill file to your local machine
# Then install via Claude Code CLI (if available)
claude skill install codebase-inventory-audit.skill
```

### Option 2: Manual Installation

```bash
# Extract to your Claude skills directory
unzip codebase-inventory-audit.skill -d ~/.claude/skills/codebase-inventory-audit
```

### Option 3: Use as Standalone Scripts

The Python scripts work independently:

```bash
# Find orphaned Prisma models
python scripts/find_orphaned_models.py prisma/schema.prisma --search-root .

# Find unused files
python scripts/find_unused_imports.py lib/ --extensions .ts,.tsx
python scripts/find_unused_imports.py components/ --extensions .tsx,.ts
```

## Usage

### In Claude Code

Simply mention the need for a codebase audit:

```
"I need to audit this codebase for orphaned code and documentation gaps"
```

Claude will automatically trigger this skill and guide you through the 10-step process.

### Manual Trigger

You can also explicitly invoke the skill:

```
Use the codebase-inventory-audit skill to create a comprehensive inventory
```

### Output Location

The skill creates:
- `docs/MAJOR_CORE_PLANS/CODEBASE-STATUS.md` - Main audit document

## Workflow Overview

```
Step 1: Initialize Audit Document
  ↓
Step 2: Analyze Routes/Pages (✅🔨📦❌)
  ↓
Step 3: Audit Data Models (Active/Orphaned/Infrastructure)
  ↓
Step 4: Audit Lib Directory (find_unused_imports.py)
  ↓
Step 5: Audit Components (find_unused_imports.py)
  ↓
Step 6: Documentation Gap Analysis
  ↓
Step 7: Infrastructure & Test Coverage
  ↓
Step 8: Create Removal Candidates Inventory
  ↓
Step 9: Recommended Next Steps (Prioritized)
  ↓
Step 10: Review and Validate
```

## Example Output

The skill produces a comprehensive report like this:

```markdown
## Executive Summary

| Category | Count | Notes |
|----------|-------|-------|
| **Routes (pages)** | 94 total | 80+ complete, 3 partial, 10 stubs |
| **Prisma Models** | 94 total | 73 active, 2 orphaned |
| **Components** | 300+ total | ~24 verified unused |
| **Lib Files** | 169 total | 2 unused (verified) |

## Removal Candidates Inventory

### Safe to Remove (Verified)

| Item | Type | Reason |
|------|------|--------|
| `EventType` model | Prisma | Zero usage (verified: no `prisma.eventType.` calls) |
| `lib/feature-flags.ts` | Lib | 0 imports, duplicate of configurator |
| `forms/user-form` | Component | Legacy (users UI removed) |
```

## Best Practices

1. **Don't Delete During Audit** - Only identify candidates for review
2. **Verify Before Flagging** - Check for indirect usage and dynamic imports
3. **Archive, Don't Delete Docs** - Move old docs to `/docs/past-work/archive/`
4. **Run Regularly** - Schedule audits before major releases
5. **Update Changelog** - Track audit dates and methodologies

## Requirements

- Python 3.x
- Claude Code with Task tool support
- Codebase with:
  - Routes/pages (e.g., Next.js App Router, React Router)
  - Optional: Prisma schema (for model auditing)
  - Optional: TypeScript/JavaScript (for import analysis)

## Tech Stack Support

Works best with:
- **Frameworks:** Next.js, React, Vue, Angular, Express, FastAPI
- **ORMs:** Prisma, TypeORM, Sequelize, SQLAlchemy
- **Languages:** TypeScript, JavaScript, Python

The workflow is adaptable to other stacks.

## Development

This skill was created using Anthropic's `skill-creator` skill and follows best practices for:
- Progressive disclosure (minimal SKILL.md, references loaded as needed)
- Executable scripts for deterministic reliability
- Parallel agent execution patterns
- Clear workflow with concrete examples

## Version History

- **v1.0.0** (2025-12-16) - Initial release
  - 10-step audit workflow
  - 2 automation scripts
  - Comprehensive CODEBASE-STATUS.md template
  - Parallel execution pattern

## Author

Created by Pete Dixon using Claude Code and Anthropic's skill-creator framework.

## License

MIT License - Feel free to use, modify, and share!

## Contributing

Contributions welcome! If you improve this skill:

1. Test changes on real codebases
2. Update SKILL.md with new patterns
3. Add new automation scripts to `/scripts/`
4. Share improvements via pull request

## Support

For issues, questions, or suggestions:
- Open an issue in your distribution channel
- Share improvements with the community
- Test on diverse codebases and report findings

---

**Happy auditing! 🧹✨**
