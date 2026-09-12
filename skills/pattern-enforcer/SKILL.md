---
name: pattern-enforcer
description: Use before implementing any UI component, error handling, test, or named symbol. Scans the codebase for existing patterns and enforces consistency — never introduces a new approach when one already exists. Triggered by "add a dropdown", "write a test for", "handle this error", "create a new file/function/class", or "/pattern-enforcer <what to implement>".
---

# Pattern Enforcer

## Overview

Scan before you act. Find how it's already done in this codebase, then do it the same way. One rule: never introduce a new pattern when an existing one can be reused.

## Invocation

```
/pattern-enforcer <what you want to implement>
```

Also activates automatically when Claude is about to implement anything in the four domains: UI components, error handling, tests, or named symbols.

## Phase 0: Detect Domain

Identify the abstraction layer of what is being added, then map it to a domain:

| Abstraction layer | Domain |
|-------------------|--------|
| Visual element the user interacts with (button, dropdown, modal, form, input, table, card, toast, dialog) | **UI** |
| Code that handles failure, validates input, or formats errors for users or logs | **Error handling** |
| Code whose purpose is to verify other code's behavior | **Tests** |
| A new file, function, class, variable, hook, service, or controller being named | **Naming** |

A single request can span multiple domains (e.g. "write a test for the error handler" → both Tests and Error handling). Run the scan for each domain that applies. If ambiguous, list the detected domains and confirm with the user before scanning.

## Phase 1: Scan

### UI Domain
Search for existing usage of the same element type. Adjust keywords to match the specific element being added:
```bash
grep -r "dropdown\|<Select\|<Combobox\|<Listbox" --include="*.tsx" --include="*.jsx" --include="*.vue" --include="*.svelte" -l
```
Sort results by match frequency. Read the top 2–3 files by occurrence count to understand:
- Which component/library is used (shadcn, MUI, custom, etc.)
- How it's imported
- What props are passed
- How it's styled (Tailwind, CSS modules, inline)

### Error Handling Domain
```bash
grep -r "catch\|rescue\|except\|AppError\|ApiError\|raise\|throw new" --include="*.ts" --include="*.rb" --include="*.py" -l | head -10
```
Read the top 2–3 files by occurrence count to understand:
- Error class hierarchy (custom vs native)
- How errors are logged
- What user-facing error messages look like
- HTTP status codes used

### Tests Domain
```bash
find . -name "*.test.*" -o -name "*.spec.*" -o -name "*_test.*" | head -20
```
Prioritize the test file closest to the code being tested (same directory or same module). Read it to understand:
- Test framework and imports
- `describe`/`it`/`test` structure
- How mocks are set up
- Assertion style (`expect`, `assert`, `should`)
- Helper functions used

### Naming Domain
```bash
ls -la <target-directory>
grep -r "export function\|export class\|export const\|def \|class " <adjacent-files> | head -20
```
Extract: casing convention (camelCase, snake_case, PascalCase, kebab-case) and prefix/suffix patterns (e.g. `useX` for hooks, `XService`, `XController`).

## Phase 2: Assess Findings

**One clear pattern found:**
> "Found 8 dropdowns using `<Select>` from shadcn/ui, imported from `@/components/ui/select`, styled with Tailwind. Implementing the same way."

Proceed to Phase 3 immediately.

**Multiple patterns found:**
- Count occurrences of each pattern
- If counts differ: use the higher-count pattern automatically
  > "Found two approaches: `<Select>` (6 uses) vs native `<select>` (2 uses). Using `<Select>` — more widely adopted."
- If counts are equal: ask the user to choose, then proceed to Phase 3 with their answer

**No pattern found:**
> "No existing [element type] found in this codebase. This will be the first one.
> Based on your stack ([detected stack]), the standard approach is [best-practice recommendation].
> Proceeding with that — this will set the pattern for future use."

Proceed to Phase 3 using the best-practice approach for the detected stack.

## Phase 3: Implement

Implement using exactly the pattern identified:
- Same component / same import path
- Same props structure
- Same styling approach
- Same error class hierarchy
- Same test structure and helpers
- Same naming convention

After implementing, add a brief note:
> "Used `<Select>` from shadcn/ui — consistent with [filename] and 7 other places."

## Rules

- Never import a new UI library if one already exists in the project
- Never create a new error class if an existing one covers the case
- Never write a test in a different style from adjacent tests
- Never name a file/function using a different casing from its neighbors
- Do not refactor existing inconsistencies unless the user explicitly asks — just match the dominant pattern
- Always show which files you found the pattern in so the user can verify
