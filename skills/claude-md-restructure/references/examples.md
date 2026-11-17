# Before/After Examples

Real-world examples of CLAUDE.md restructuring.

## Example 1: Spring Boot Microservice

### Before (Problematic)

```
project-root/
├── CLAUDE.md                    # 682 lines (!)
├── README.md
├── CHANGELOG.md
├── AGENTS.md
├── ANALISI-BUG-X.md            # Obsolete
├── ANALISI-BUG-Y.md            # Obsolete
├── FIX-FEATURE-A.md            # Obsolete
├── FIX-FEATURE-B.md            # Obsolete
├── IMPLEMENTAZIONE-X.md        # Obsolete
├── IMPLEMENTAZIONE-Y.md        # Obsolete
├── REFACTORING-Z.md            # Obsolete
├── REPORT-ANALYSIS.md          # Obsolete
├── RIEPILOGO-V1.md             # Obsolete
├── RIEPILOGO-V2.md             # Obsolete
├── SOLUZIONE-A.md              # Obsolete
├── SOLUZIONE-B.md              # Obsolete
├── SWAGGER-PATTERN.md          # Reference doc
├── country_api.md              # Reference doc
├── external_service.md         # Reference doc
└── workflow-service/
    └── docs/
        ├── API.md
        └── INTEGRATION.md
```

**Problems**:
- Root CLAUDE.md: 682 lines (should be <100)
- 40 .md files in root (should be <6)
- No component-level CLAUDE.md
- Obsolete files cluttering root
- Reference docs mixed with project files

### After (Optimized)

```
project-root/
├── CLAUDE.md                    # 82 lines
├── README.md
├── CHANGELOG.md
├── QUICK-REFERENCE.md
├── AGENTS.md
│
├── docs/
│   ├── SWAGGER-PATTERN.md
│   ├── BATCH-DISABLED.md
│   └── integrations/
│       ├── country_api.md
│       ├── external_service.md
│       └── soap_guide.md
│
└── workflow-service/
    ├── CLAUDE.md                # 175 lines (NEW)
    └── docs/
        ├── API.md
        └── INTEGRATION.md
```

**Improvements**:
- Root CLAUDE.md: 82 lines (-88%)
- Root .md files: 5 (-87%)
- Component CLAUDE.md: Created (lazy loaded)
- Obsolete files: Deleted (28 files)
- Reference docs: Organized in docs/

### Metrics Comparison

| Metric | Before | After | Change |
|--------|--------|-------|--------|
| Root CLAUDE.md | 682 lines | 82 lines | -88% |
| Root .md files | 40 | 5 | -87% |
| Component CLAUDE.md | 0 | 1 | +1 |
| Obsolete files | 28 | 0 | -100% |
| Lazy loading | No | Yes | Enabled |

---

## Example 2: Monorepo with Multiple Services

### Before

```
monorepo/
├── CLAUDE.md                    # 1200 lines (!)
├── frontend/
│   └── src/
├── backend/
│   └── src/
├── api-gateway/
│   └── src/
└── shared/
    └── src/
```

**Problems**:
- Single massive CLAUDE.md with ALL service details
- No separation of concerns
- Context bloat on every session

### After

```
monorepo/
├── CLAUDE.md                    # 60 lines (shared conventions)
│
├── frontend/
│   ├── CLAUDE.md                # React/TypeScript patterns
│   └── src/
│
├── backend/
│   ├── CLAUDE.md                # Spring Boot patterns
│   └── src/
│
├── api-gateway/
│   ├── CLAUDE.md                # Gateway config, routing
│   └── src/
│
└── shared/
    ├── CLAUDE.md                # Shared types, utilities
    └── src/
```

**Key principle**: Working in `frontend/` only loads:
1. Root CLAUDE.md (60 lines)
2. frontend/CLAUDE.md (lazy loaded)

Backend, api-gateway, shared instructions NEVER load.

---

## Content Migration Guide

### What stays in Root CLAUDE.md

```markdown
# Project Conventions

## Context
[2-3 lines]

## Stack
[Technologies list]

## Code Conventions
[Universal patterns - error handling, response format]

## Build
[Commands]

## Documentation Links
[Table of file locations]

## Commit Format
[Convention]

## Security
[Essential notes]
```

### What moves to Component CLAUDE.md

```markdown
# Component Name

## Workflows
[Step-by-step processes]

## Status/States
[Enums, state machines]

## Endpoints
[API routes]

## Error Codes
[Component-specific errors]

## Configuration
[Environment variables]
```

### What gets deleted

- `ANALISI-*.md` - Analysis complete
- `FIX-*.md` - Fix applied
- `IMPLEMENTAZIONE-*.md` - Implementation done
- `SOLUZIONE-*.md` - Solution implemented
- `REFACTORING-*.md` - Refactoring complete
- `REPORT-*.md` - One-time report
- `RIEPILOGO-*.md` - Summary now in CHANGELOG
