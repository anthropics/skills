---
name: "testrail"
description: >-
  Sync tests with TestRail. Use when user mentions "testrail", "test management",
  "test cases", "test run", "sync test cases", "push results to testrail",
  or "import from testrail".
---

# TestRail Integration

Bidirectional sync between Playwright tests and TestRail test management.

## Prerequisites

Environment variables must be set:
- `TESTRAIL_URL` — e.g., `https://your-instance.testrail.io`
- `TESTRAIL_USER` — your email
- `TESTRAIL_API_KEY` — API key from TestRail

If not set, inform the user how to configure them and stop.

## Capabilities

### 1. Import Test Cases → Generate Playwright Tests

```
/pw:testrail import --project <id> --suite <id>
```

Steps:
1. Call `testrail_get_cases` MCP tool to fetch test cases
2. For each test case:
   - Read title, preconditions, steps, expected results
   - Map to a Playwright test using appropriate template
   - Include TestRail case ID as test annotation: `test.info().annotations.push({ type: 'testrail', description: 'C12345' })`
3. Generate test files grouped by section
4. Report: X cases imported, Y tests generated

### 2. Push Test Results → TestRail

```
/pw:testrail push --run <id>
```

Steps:
1. Run Playwright tests with JSON reporter:
   ```bash
   npx playwright test --reporter=json > test-results.json
   ```
2. Parse results: map each test to its TestRail case ID (from annotations)
3. Call `testrail_add_result` MCP tool for each test:
   - Pass → status_id: 1
   - Fail → status_id: 5, include error message
   - Skip → status_id: 2
4. Report: X results pushed, Y passed, Z failed

### 3. Create Test Run

```
/pw:testrail run --project <id> --name "Sprint 42 Regression"
```

Steps:
1. Call `testrail_add_run` MCP tool
2. Include all test case IDs found in Playwright test annotations
3. Return run ID for result pushing

### 4. Sync Status

```
/pw:testrail status --project <id>
```

Steps:
1. Fetch test cases from TestRail
2. Scan local Playwright tests for TestRail annotations
3. Report coverage:
   ```
   TestRail cases: 150
   Playwright tests with TestRail IDs: 120
   Unlinked TestRail cases: 30
   Playwright tests without TestRail IDs: 15
   ```

### 5. Update Test Cases in TestRail

```
/pw:testrail update --case <id>
```

Steps:
1. Read the Playwright test for this case ID
2. Extract steps and expected results from test code
3. Call `testrail_update_case` MCP tool to update steps

## MCP Tools Used

| Tool | When |
|---|---|
| `testrail_get_projects` | List available projects |
| `testrail_get_suites` | List suites in project |
| `testrail_get_cases` | Read test cases |
| `testrail_add_case` | Create new test case |
| `testrail_update_case` | Update existing case |
| `testrail_add_run` | Create test run |
| `testrail_add_result` | Push individual result |
| `testrail_get_results` | Read historical results |

## Test Annotation Format

All Playwright tests linked to TestRail include:

```typescript
test('should login successfully', async ({ page }) => {
  test.info().annotations.push({
    type: 'testrail',
    description: 'C12345',
  });
  // ... test code
});
```

This annotation is the bridge between Playwright and TestRail.

## Output

- Operation summary with counts
- Any errors or unmatched cases
- Link to TestRail run/results
