---
name: claude-md-restructure
description: |
  Restructure and optimize CLAUDE.md documentation in repositories following best practices for larger codebases.
  Use when user asks to: (1) audit/review CLAUDE.md structure, (2) optimize/restructure project documentation,
  (3) reduce CLAUDE.md size or context bloat, (4) implement hierarchical CLAUDE.md structure,
  (5) organize scattered .md files, or mentions "CLAUDE.md best practices", "documentation restructure",
  or "context optimization". Applies lazy loading patterns and progressive disclosure principles.
---

# CLAUDE.md Restructuring Skill

**Author**: Cosimo Eugenio Bortone
**Version**: 1.0.0
**Created**: 2026-01-28
**License**: MIT

Optimize CLAUDE.md documentation structure for efficient context loading.

## Core Principles

### Loading Mechanisms
1. **Ancestor Loading (upward)**: Root CLAUDE.md loads at startup for ALL sessions
2. **Descendant Loading (downward)**: Subdirectory CLAUDE.md files load ONLY when accessing files in that directory (lazy loading)
3. **Siblings Never Load**: Working in `frontend/` won't load `backend/` instructions

### Target Structure
```
project-root/
├── CLAUDE.md              # ~50-100 lines (global conventions ONLY)
├── CLAUDE.local.md        # Personal preferences (.gitignore)
├── README.md
├── CHANGELOG.md
│
├── docs/                  # Organized documentation
│   ├── integrations/
│   └── architecture/
│
└── component-name/        # Each major component
    ├── CLAUDE.md          # Component-specific (lazy loaded)
    └── docs/
```

## Restructuring Workflow

### Phase 1: Analyze Current State

```bash
# Count CLAUDE.md files
find . -name "CLAUDE*.md" -type f

# Count all .md files in root
ls -1 *.md 2>/dev/null | wc -l

# Check CLAUDE.md size
wc -l CLAUDE.md
```

**Red flags**:
- Root CLAUDE.md > 150 lines
- No CLAUDE.md in major subdirectories
- > 10 .md files in root directory
- Implementation details in root CLAUDE.md

### Phase 2: Categorize Files

Classify each .md file:

| Category | Action | Destination |
|----------|--------|-------------|
| **Global conventions** | Keep in root CLAUDE.md | Root |
| **Component-specific** | Move to component/CLAUDE.md | Subdirectory |
| **Reference docs** | Move to docs/ | `docs/` or `docs/integrations/` |
| **Obsolete** (completed fixes, old analysis) | Delete | - |
| **Changelog/history** | Keep CHANGELOG.md only | Root |

**Obsolete file patterns** (typically safe to delete):
- `ANALISI-*`, `ANALYSIS-*` (completed analysis)
- `FIX-*`, `BUG-FIX-*` (applied fixes)
- `IMPLEMENTAZIONE-*`, `IMPLEMENTATION-*` (completed work)
- `SOLUZIONE-*`, `SOLUTION-*` (implemented solutions)
- `REFACTORING-*` (completed refactoring)
- `REPORT-*`, `RIEPILOGO-*` (one-time reports)

### Phase 3: Create Directory Structure

```bash
mkdir -p docs/integrations docs/architecture
```

### Phase 4: Write Root CLAUDE.md

**Include ONLY**:
- Project context (2-3 lines)
- Stack/tech summary
- Critical architectural rules (e.g., multi-tenant patterns)
- Code conventions (patterns, error handling)
- Build commands
- Documentation links table
- Commit conventions
- Security notes

**Template**: See `references/root-template.md`

### Phase 5: Create Component CLAUDE.md

For each major component/service, create dedicated CLAUDE.md with:
- Component-specific workflows
- Endpoints/API (if applicable)
- Status codes/enums
- Error codes
- Configuration
- Utility classes reference

**Template**: See `references/component-template.md`

### Phase 6: Move Reference Files

```bash
# Move integration/external docs
mv *_rina*.md *_api*.md docs/integrations/

# Move pattern guides
mv *-PATTERN*.md docs/
```

### Phase 7: Delete Obsolete Files

```bash
# Delete completed analysis/fixes (after user confirmation)
rm -f ANALISI-*.md FIX-*.md IMPLEMENTAZIONE-*.md
rm -f SOLUZIONE-*.md REFACTORING-*.md REPORT-*.md
```

### Phase 8: Verify Structure

```bash
# Final check
echo "=== ROOT ===" && ls *.md
echo "=== docs/ ===" && ls docs/*.md
echo "=== component/ ===" && ls component/CLAUDE.md

# Line counts
wc -l CLAUDE.md */CLAUDE.md
```

## Success Metrics

| Metric | Before | Target |
|--------|--------|--------|
| Root CLAUDE.md lines | >200 | <100 |
| .md files in root | >10 | <6 |
| Component CLAUDE.md | 0 | 1+ per major component |
| Lazy loading | Disabled | Enabled |

## Resources

- `references/root-template.md` - Template for root CLAUDE.md
- `references/component-template.md` - Template for component CLAUDE.md
- `references/examples.md` - Before/after examples
