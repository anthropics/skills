---
name: codebase-inventory-audit
description: Comprehensive codebase inventory and cleanup audit to identify orphaned code, unused files, documentation gaps, and code bloat. Use when you need to audit a codebase for unused models, orphaned components, stale documentation, or perform spring cleaning before major releases. Creates a CODEBASE-STATUS.md document as single source of truth for what's actually implemented.
---

# Codebase Inventory Audit

Systematic workflow for auditing codebases to identify orphaned code, unused components, documentation gaps, and infrastructure bloat. Produces a comprehensive CODEBASE-STATUS.md report.

## Overview

Run this audit when:
- Preparing for a major release or refactor
- Documentation seems out of sync with reality
- Suspecting code bloat or orphaned files
- Need a "single source of truth" inventory
- Starting work on a new codebase

The audit uses parallel exploration agents to thoroughly analyze routes, data models, lib files, components, documentation, and infrastructure.

## Workflow

### Step 1: Initialize Audit Document

Create `docs/MAJOR_CORE_PLANS/CODEBASE-STATUS.md` using the template in `references/audit-template.md`.

Update the frontmatter with:
- Current date
- Audit methodology (e.g., "5 parallel Explore agents")

### Step 2: Analyze Routes/Pages

**Goal:** Categorize all routes as Complete, Partial, Scaffolded, or Missing.

**Process:**
1. Use `find` or `glob` to list all route files (e.g., `app/**/page.tsx`)
2. For each route, spawn an Explore agent to:
   - Check if it renders actual content or shows "ComingSoon"
   - Verify backend integration (server actions, API calls)
   - Identify feature flags or conditional rendering
3. Categorize routes using status icons:
   - ✅ Complete: Fully functional with UI and backend
   - 🔨 Partial: Some functionality working, some missing
   - 📦 Scaffolded: Page exists but shows stub/placeholder
   - ❌ Missing: Planned but not implemented

**Output:** Routes table in CODEBASE-STATUS.md

### Step 3: Audit Data Models (Prisma/ORM)

**Goal:** Identify active, referenced, infrastructure, and orphaned models.

**Process:**
1. Parse `prisma/schema.prisma` (or equivalent) to list all models
2. Run `scripts/find_orphaned_models.py` to detect zero-usage models:
   ```bash
   python scripts/find_orphaned_models.py prisma/schema.prisma --search-root .
   ```
3. For each model, categorize as:
   - **Active:** Regularly queried/mutated in code
   - **Referenced:** Used only via relations
   - **Infrastructure:** Provisioned for future use (seeded, validated, but not in production flows)
   - **Orphaned:** Zero usage anywhere (safe to remove)

**Output:** Prisma Models Audit section with categorized models

### Step 4: Audit Lib Directory

**Goal:** Find unused or stub lib files.

**Process:**
1. Run `scripts/find_unused_imports.py` on `lib/` directory:
   ```bash
   python scripts/find_unused_imports.py lib/ --extensions .ts,.tsx
   ```
2. For flagged files, verify:
   - Are they truly unused or just imported indirectly?
   - Are they stubs (functions that return "not implemented")?
   - Are they conditional (only work with certain env vars)?
3. Categorize as:
   - **Active & Core:** Regular usage
   - **Partial/Conditional:** Works only with specific config
   - **Unused/Stub:** Zero imports or stub implementation

**Output:** Lib Directory Audit section

### Step 5: Audit Components

**Goal:** Identify unused component files.

**Process:**
1. Run `scripts/find_unused_imports.py` on `components/` directory:
   ```bash
   python scripts/find_unused_imports.py components/ --extensions .tsx,.ts
   ```
2. Verify false positives (components used only in specific routes)
3. Group by category (Admin, Auth, Forms, UI, etc.)

**Output:** Unused Components section

### Step 6: Documentation Gap Analysis

**Goal:** Find docs that claim features are "planned" when they're actually complete, or docs that are outdated.

**Process:**
1. List all documentation in `docs/` and `docs/MAJOR_CORE_PLANS/`
2. For each design/planning doc:
   - Check claimed status (e.g., "DESIGN PHASE", "Ready for Implementation")
   - Verify actual implementation status by checking routes/models/code
   - Flag mismatches
3. Identify old docs (pre-2025, superseded sprints) to archive

**Output:** Documentation Gap Analysis section

### Step 7: Infrastructure & Test Coverage

**Goal:** Document deployed infrastructure and test coverage gaps.

**Process:**
1. List deployed infrastructure (Docker, app platform specs, migrations, etc.)
2. Count test files and map to features:
   ```bash
   find e2e -name "*.spec.ts" -exec grep -l "describe" {} \; | wc -l
   find tests -name "*.test.ts" | wc -l
   ```
3. Identify features with zero test coverage

**Output:** Infrastructure Status and Test Coverage sections

### Step 8: Create Removal Candidates Inventory

**Goal:** Provide actionable removal recommendations (but don't delete anything).

**Process:**
1. Compile all identified orphans, unused files, and stale docs
2. Categorize as:
   - **Safe to Remove (Verified):** Zero usage confirmed
   - **Needs Decision:** Usage unclear or strategic decision required
   - **Keep (Infrastructure Ready):** Provisioned for future use

**Important:** This is for review only. No deletions during audit.

**Output:** Removal Candidates Inventory section

### Step 9: Recommended Next Steps

**Goal:** Prioritize cleanup actions.

**Process:**
1. Group actions by priority:
   - Priority 1: Documentation accuracy (update claims vs reality)
   - Priority 2: Code cleanup (remove verified orphans)
   - Priority 3: Test coverage (add missing tests)
   - Priority 4: Feature decisions (implement or defer stub pages)

**Output:** Recommended Next Steps section with checkboxes

### Step 10: Review and Validate

**Goal:** Ensure audit accuracy before finalizing.

**Process:**
1. Review flagged orphans with a verification pass
2. Check false positives (indirect imports, dynamic imports)
3. Update changelog with audit date and methodology

**Output:** Verified, accurate CODEBASE-STATUS.md

## Execution Pattern

Use **parallel Explore agents** for independent analysis tasks:

```
Task 1 (Routes): Analyze all routes in app/ directory
Task 2 (Models): Categorize all Prisma models by usage
Task 3 (Lib): Audit lib/ directory for unused files
Task 4 (Components): Check components/ for orphans
Task 5 (Docs): Compare documentation claims vs reality
```

Run agents concurrently to minimize audit time.

## Best Practices

1. **Don't delete during audit** - Only identify candidates
2. **Verify before flagging** - Check for indirect usage, dynamic imports
3. **Update regularly** - Re-run audit before major releases
4. **Archive, don't delete docs** - Move old docs to `docs/past-work/archive/`
5. **Use emoji status** - Makes report scannable (✅🔨📦❌🗑️)

## Scripts Reference

- **find_orphaned_models.py**: Detect Prisma models with zero usage
- **find_unused_imports.py**: Find files with zero import statements

Both scripts support `--help` for detailed usage.

## Output Template

See `references/audit-template.md` for the complete CODEBASE-STATUS.md structure.

## Maintenance

Update CODEBASE-STATUS.md changelog whenever:
- New features are completed
- Orphaned code is removed
- Documentation is updated
- Infrastructure changes
