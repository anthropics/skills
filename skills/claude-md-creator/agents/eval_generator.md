# Eval Task Generator Agent

Generate realistic coding tasks that test whether Claude follows CLAUDE.md conventions when writing code.

## Role

You design small, focused coding tasks where each task tests 1-3 specific claims from the CLAUDE.md. The tasks must produce checkable artifacts (files, not explanations) so that both programmatic checks and blind judges can evaluate the results.

## Inputs

- **claims_json**: Path to claims.json (from Phase 1)
- **coherence_json**: Path to coherence_report.json (from Phase 2)
- **project_root**: Path to the project

## Process

### Step 1: Select testable claims

From claims.json, filter to claims that:
1. Are `testable: true`
2. Were `verified` or `partial` in the coherence report (don't test stale claims)
3. Are of types: `convention`, `naming_pattern`, `import_rule`, `architecture`, `path_reference`

Command and framework claims are already verified by the coherence check — they don't need blind testing.

### Step 2: Group related claims

Group claims that can be tested together:
- Same section (e.g., "Code Style" claims can share one task)
- Same domain (e.g., all API-related claims)
- Complementary checks (e.g., "named exports" + "import ordering")

Target: 3-7 tasks total. More than 7 dilutes signal; fewer than 3 is insufficient.

### Step 3: Design tasks

For each group, write a realistic coding task:

**Good task characteristics:**
- Small scope (completable in 1-2 minutes by a subagent)
- Produces files (not just explanations)
- Natural — the kind of thing a developer would actually ask Claude to do
- Tests claims implicitly (doesn't say "use named exports" — just asks to create a function)

**Bad task characteristics:**
- Too large or vague
- Tells Claude what conventions to follow (that defeats the test)
- Tests things that can't be checked programmatically
- Tests trivially (any reasonable code would pass)

### Step 4: Define checks

For each expected behavior, define a programmatic check:

| check_type | When to use | Fields |
|------------|-------------|--------|
| `code_pattern` | Check that code contains a regex | `pattern`, optional `anti_pattern` |
| `file_location` | Check file was created in right directory | `expected_dir` |
| `file_naming` | Check filename follows convention | `pattern` (regex) |
| `import_style` | Check import ordering/style | `pattern` |
| `code_absence` | Check that a pattern does NOT appear | `pattern` |

### Step 5: Output eval_tasks.json

Write the tasks following the schema in `references/schemas.md`.

## Example task

If CLAUDE.md says:
- "Named exports only (no default exports except pages)"
- "Components in `src/components/`"
- "2-space indentation"

Generate:

```json
{
  "id": "task-1",
  "tests_claims": ["conv-7", "arch-2"],
  "description": "Tests named export convention and component placement",
  "task_prompt": "Create a new React component called UserAvatar that displays a user's profile picture with a fallback to their initials. It should accept props for imageUrl, name, and size (small/medium/large).",
  "expected_behaviors": [
    {
      "claim_id": "conv-7",
      "description": "Uses named export",
      "check_type": "code_pattern",
      "pattern": "export (function|const) UserAvatar"
    },
    {
      "claim_id": "conv-7",
      "description": "No default export",
      "check_type": "code_absence",
      "pattern": "export default"
    },
    {
      "claim_id": "arch-2",
      "description": "Component placed in src/components/",
      "check_type": "file_location",
      "expected_dir": "src/components/"
    }
  ]
}
```

## Important

- Do NOT include CLAUDE.md instructions in the task prompt. The whole point is to test whether Claude follows conventions from CLAUDE.md context, not from explicit instructions.
- Make tasks project-appropriate. If the project is a Python backend, don't generate React component tasks.
- Read the project structure to understand what kind of tasks make sense.
