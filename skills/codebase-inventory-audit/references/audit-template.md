# Codebase Status - Single Source of Truth

> **Document Location:** `docs/MAJOR_CORE_PLANS/CODEBASE-STATUS.md`
> **Last Audit:** [DATE]
> **Purpose:** Accurate picture of what's actually implemented vs. planned
> **Methodology:** Comprehensive analysis via parallel Explore agents

---

## Quick Reference

| Status | Meaning |
|--------|---------|
| ✅ Complete | Fully implemented with UI, backend, and working |
| 🔨 Partial | Some pieces work, others missing |
| 📦 Scaffolded | Files/models exist but feature not functional |
| ❌ Missing | Planned but not started |
| 🗑️ Orphaned | Code exists but unused/abandoned |

---

## Executive Summary

| Category | Count | Notes |
|----------|-------|-------|
| **Routes (pages)** | [N] total | [Complete], [Partial], [Stubs], [Broken] |
| **Data Models** | [N] total | [Active], [Referenced], [Infrastructure], [Orphaned] |
| **Components** | [N] total | [Verified unused] |
| **Lib Files** | [N] total | [Core active], [Unused] |
| **API Endpoints** | [N] routes | [Functional status] |

---

## Feature Status Matrix

### Core Features

| Feature | Status | Completeness | Test Coverage | Notes |
|---------|--------|--------------|---------------|-------|
| **[Feature Name]** | ✅ Complete | [%] | [N] tests | [Notes] |

### Partially Implemented

| Feature | Status | What Works | What's Missing |
|---------|--------|------------|----------------|
| **[Feature]** | 🔨 [%] | [Description] | [Missing pieces] |

### Scaffolded Only (Stub Pages)

| Feature | Route | Status | Notes |
|---------|-------|--------|-------|
| **[Feature]** | `/path/` | 📦 ComingSoon | [Implementation status] |

---

## Data Models Audit

### Active Models - Regularly queried/mutated

**Core Application:**
- [List models with checkmarks]

**[Category]:**
- [List models with checkmarks]

### Referenced Models - Used via relations only

- [List models]

### Infrastructure Models - Provisioned for future use

| Model | Usage | Notes |
|-------|-------|-------|
| [Model] | [Status] | [Purpose] |

### Orphaned Models - Zero usage anywhere

| Model | Notes | Recommendation |
|-------|-------|----------------|
| **[Model]** | [Why orphaned] | Remove or implement |

---

## Lib Directory Audit

### Active & Core

- **[Category]:** `lib/path/*.ts` ✓

### Partial/Conditional

| File | Status | Notes |
|------|--------|-------|
| `lib/path.ts` | Conditional | [Why conditional] |

### Unused/Stub

| File | Status | Recommendation |
|------|--------|----------------|
| `lib/path.ts` | Stub | [Action] |

---

## Unused Components

### [Category] Components

| Component | Notes |
|-----------|-------|
| `path/component` | [Why unused] |

---

## Documentation Gap Analysis

### Documents Needing Updates

| Document | Claimed Status | Actual Status | Action |
|----------|----------------|---------------|--------|
| `[Doc]` | "[Claim]" | ✅ Complete | Update |

### Documents That Are Accurate

| Document | Status |
|----------|--------|
| `[Doc]` | ✅ Accurate |

### Old Docs to Archive

[List of old documentation that should move to archive]

---

## Infrastructure Status

### Deployed

- ✅ [Infrastructure item]

### Implemented (Verified)

- ✅ [Infrastructure item]

### Missing

- ❌ [Missing infrastructure]

---

## Test Coverage

### Strong Coverage

- [Feature] ([N] E2E tests)
- Unit tests: [N] files

### Gaps (0 tests)

- [Feature or workflow]

---

## Removal Candidates Inventory

**Note: No deletions made. This is for review only.**

### Safe to Remove (Verified)

| Item | Type | Reason |
|------|------|--------|
| `[Item]` | [Type] | [Reason] |

### Needs Decision

| Item | Type | Options |
|------|------|---------|
| [Item] | [Type] | [Options] |

### Keep (Infrastructure Ready)

- [Item] - [Reason to keep]

---

## Recommended Next Steps

### Priority 1: [Category]

- [ ] [Action item]

### Priority 2: [Category]

- [ ] [Action item]

### Priority 3: [Category]

- [ ] [Action item]

---

## Changelog

| Date | Change |
|------|--------|
| [DATE] | [Description] |

---

**This document reflects actual codebase state. Update when features change.**
