---
name: test-driven-development
description: "Use when modifying core utilities like mermaidProcessor or formulaFixer, to ensure all 35 Jest regression tests pass before and after changes"
---

# NoteMD Pro - Testing & Regression Defense

## Overview

The `obsidian-NoteMD_new` source project contains a robust suite of 35 Jest unit tests located in the `src/tests/` directory. When acting as an AI Agent modifying core utilities, heuristic engines, or batch processors within this skill set, you **MUST** engage this testing framework to prevent regressions.

## 🛡️ The Prime Directive

> [!CAUTION] Mandatory Regression Testing
> If you modify `fileUtils.ts`, `mermaidProcessor.ts`, `formulaFixer.ts`, or any other core utility, you are required to run the local test suite and ensure all 35 mocked tests pass. Do not present a "completed" refactor to the user without terminal proof that `npm test` succeeded.

## Test Suite Structure

The tests are located in `src/tests/` and use Obsidian-specific mocks (`src/__mocks__/`):

| Test File                     | Responsibilities                                                                             |
| ----------------------------- | -------------------------------------------------------------------------------------------- |
| `mermaidDeepDebug.test.ts`    | Validates complex Mermaid structural repairs                                                 |
| `mermaidFix*.test.ts`         | 15+ individual files testing specific Mermaid regex fixes (e.g., arrows, quotes, semicolons) |
| `conceptNoteCreation.test.ts` | Tests the `createConceptNotes` logic and de-duplication                                      |
| `formulaCorrection.test.ts`   | Validates the LaTeX delimiter `$..$` conversions                                             |
| `parallelBatch.test.ts`       | Tests concurrency control and processor limits                                               |
| `processFile.test.ts`         | End-to-end testing of the wiki-link processing pipeline                                      |

## Executing Tests

To run the full suite:

```bash
npm run test
```

To run a specific test file when iterating on a feature:

```bash
npm run test -- mermaidDeepDebug.test.ts
```

## Creating New Tests

When implementing new features (e.g., upgrading to an AST parser for formulas or adding the xAI provider), you must create a corresponding `.test.ts` file.

**Standard Mocking Pattern:**

```typescript
import { App, TFile } from "obsidian";
import { myNewFunction } from "../myModule";

// The Obsidian App mock is auto-injected by Jest setup
describe("My New Feature", () => {
  let mockApp: App;

  beforeEach(() => {
    mockApp = new App();
    // Setup mock vault files if needed
  });

  it("should correctly process the input", async () => {
    const result = await myNewFunction(mockApp, "input data");
    expect(result).toBe("expected output");
  });
});
```

## Handling Test Failures

If a test fails during your work:

1. **Read the Output**: Jest will output the exact `Expected` vs `Received` diff.
2. **Do Not Skip**: Never comment out a failing test to push a feature through.
3. **Analyze the Regression**: Determine if your change broke existing functionality or if the test itself needs to be updated to reflect a new, correct behavior (e.g., if you change the Mermaid output format).
