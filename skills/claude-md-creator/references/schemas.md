# JSON Schemas

Data structures used across all phases of the CLAUDE.md evaluation pipeline.

## Table of Contents

1. [claims.json](#claimsjson) — Phase 1 output
2. [coherence_report.json](#coherence_reportjson) — Phase 2 output
3. [eval_tasks.json](#eval_tasksjson) — Phase 3 output
4. [blind_results.json](#blind_resultsjson) — Phase 4 output
5. [evaluation_summary.json](#evaluation_summaryjson) — Phase 5 output

---

## claims.json

Output of Phase 1 (Claim Extraction). Every testable instruction from the CLAUDE.md is parsed into a structured claim.

```json
{
  "source_file": "CLAUDE.md",
  "rules_files": ["rules/code-style.md", "rules/testing.md"],
  "total_claims": 42,
  "claims": [
    {
      "id": "cmd-1",
      "type": "command",
      "raw_text": "`pnpm dev` — start dev server on localhost:3000",
      "source_file": "CLAUDE.md",
      "source_line": 15,
      "source_section": "Build & Run",
      "extracted": {
        "command": "pnpm dev",
        "description": "start dev server on localhost:3000"
      },
      "testable": true
    },
    {
      "id": "path-3",
      "type": "path_reference",
      "raw_text": "API handlers live in `src/api/handlers/`",
      "source_file": "CLAUDE.md",
      "source_line": 34,
      "source_section": "Architecture",
      "extracted": {
        "path": "src/api/handlers/",
        "assertion": "API handlers live here"
      },
      "testable": true
    },
    {
      "id": "conv-7",
      "type": "convention",
      "raw_text": "Named exports only (no default exports except pages)",
      "source_file": "rules/code-style.md",
      "source_line": 12,
      "source_section": "Code Style",
      "extracted": {
        "rule": "Use named exports, not default exports",
        "exception": "page.tsx and layout.tsx files",
        "check_pattern": "export default"
      },
      "testable": true
    },
    {
      "id": "fw-2",
      "type": "framework_reference",
      "raw_text": "Database queries through Prisma; schema at `prisma/schema.prisma`",
      "source_file": "CLAUDE.md",
      "source_line": 52,
      "source_section": "Architecture",
      "extracted": {
        "framework": "prisma",
        "config_path": "prisma/schema.prisma"
      },
      "testable": true
    },
    {
      "id": "vague-1",
      "type": "vague",
      "raw_text": "Write clean, maintainable code",
      "source_file": "CLAUDE.md",
      "source_line": 60,
      "source_section": "Code Style",
      "extracted": {
        "issue": "Too vague to verify — replace with specific rules"
      },
      "testable": false
    }
  ]
}
```

### Claim fields

| Field | Type | Description |
|-------|------|-------------|
| `id` | string | Unique identifier, prefixed by type: `cmd-`, `path-`, `conv-`, `fw-`, `name-`, `arch-`, `env-`, `wf-`, `vague-`, `generic-` |
| `type` | string | One of the types from claim-taxonomy.md |
| `raw_text` | string | Original text from the CLAUDE.md |
| `source_file` | string | Which file the claim came from |
| `source_line` | number | Line number in the source file |
| `source_section` | string | Section header the claim falls under |
| `extracted` | object | Type-specific structured data |
| `testable` | boolean | Whether this claim can be verified against the codebase |

---

## coherence_report.json

Output of Phase 2 (Codebase Coherence Verification). Each claim is checked against the real project.

```json
{
  "project_root": "/path/to/project",
  "total_claims": 42,
  "testable_claims": 38,
  "verified": 32,
  "stale": 4,
  "unverifiable": 2,
  "coherence_score": 84.2,
  "results": [
    {
      "claim_id": "cmd-1",
      "type": "command",
      "claim_text": "`pnpm dev` — start dev server",
      "status": "verified",
      "evidence": "Found in package.json scripts: \"dev\": \"next dev\"",
      "confidence": 1.0
    },
    {
      "claim_id": "path-3",
      "type": "path_reference",
      "claim_text": "API handlers live in `src/api/handlers/`",
      "status": "stale",
      "evidence": "Directory src/api/handlers/ does not exist. Similar: src/app/api/ (exists, 12 files)",
      "confidence": 0.0,
      "suggestion": "Update path reference to `src/app/api/`"
    },
    {
      "claim_id": "conv-7",
      "type": "convention",
      "claim_text": "Named exports only",
      "status": "verified",
      "evidence": "Sampled 20 .ts files: 18/20 use named exports (90%). 2 default exports are page.tsx files (allowed exception).",
      "confidence": 0.9,
      "adherence_ratio": 0.9
    }
  ]
}
```

### Result statuses

| Status | Meaning |
|--------|---------|
| `verified` | Claim matches the codebase |
| `stale` | Claim references something that no longer exists or is wrong |
| `partial` | Claim is partially correct (e.g., convention followed 60% of the time) |
| `unverifiable` | Cannot be checked programmatically |

---

## eval_tasks.json

Output of Phase 3 (Dynamic Eval Task Generation). Coding tasks designed to test whether Claude follows CLAUDE.md conventions.

```json
{
  "project_root": "/path/to/project",
  "total_tasks": 5,
  "tasks": [
    {
      "id": "task-1",
      "tests_claims": ["conv-7"],
      "description": "Tests whether named export convention is followed",
      "task_prompt": "Create a new utility function called `formatCurrency` in src/utils/ that formats a number as USD currency (e.g., 1234.56 -> '$1,234.56'). Include TypeScript types.",
      "expected_behaviors": [
        {
          "claim_id": "conv-7",
          "description": "Uses named export, not default export",
          "check_type": "code_pattern",
          "pattern": "export (function|const) formatCurrency",
          "anti_pattern": "export default"
        }
      ]
    },
    {
      "id": "task-2",
      "tests_claims": ["path-3", "fw-2"],
      "description": "Tests API handler placement and Prisma usage",
      "task_prompt": "Add a new API endpoint POST /api/users/invite that accepts an email and creates an invitation record.",
      "expected_behaviors": [
        {
          "claim_id": "path-3",
          "description": "Creates handler in correct API directory",
          "check_type": "file_location",
          "expected_dir": "src/app/api/"
        },
        {
          "claim_id": "fw-2",
          "description": "Uses Prisma for database operations",
          "check_type": "code_pattern",
          "pattern": "prisma\\."
        }
      ]
    }
  ]
}
```

### Check types

| check_type | Description | Fields |
|------------|-------------|--------|
| `code_pattern` | Regex match in generated code | `pattern`, optional `anti_pattern` |
| `file_location` | File created in expected directory | `expected_dir` |
| `file_naming` | File follows naming convention | `pattern` (regex for filename) |
| `import_style` | Import follows stated convention | `pattern` |
| `code_absence` | Certain pattern should NOT appear | `pattern` |

---

## blind_results.json

Output of Phase 4 (Effectiveness Blind Test). Paired comparison of with/without CLAUDE.md.

```json
{
  "total_tasks": 5,
  "tasks": [
    {
      "task_id": "task-1",
      "programmatic_checks": {
        "with_claude_md": {
          "passed": 2,
          "total": 2,
          "details": [
            {"claim_id": "conv-7", "check": "named export", "passed": true, "evidence": "Found: export function formatCurrency"}
          ]
        },
        "without_claude_md": {
          "passed": 0,
          "total": 2,
          "details": [
            {"claim_id": "conv-7", "check": "named export", "passed": false, "evidence": "Found: export default function formatCurrency"}
          ]
        }
      },
      "blind_judgment": {
        "assignment": {"A": "without_claude_md", "B": "with_claude_md"},
        "winner": "B",
        "reasoning": "Output B uses named exports consistently and follows the project's existing patterns.",
        "scores": {
          "A": {"naming": 3, "structure": 4, "style": 3, "overall": 3.3},
          "B": {"naming": 5, "structure": 5, "style": 4, "overall": 4.7}
        }
      },
      "claude_md_won": true
    }
  ],
  "summary": {
    "claude_md_wins": 4,
    "ties": 1,
    "claude_md_losses": 0,
    "programmatic_pass_rate_with": 0.9,
    "programmatic_pass_rate_without": 0.4,
    "effectiveness_score": 85.0
  }
}
```

---

## evaluation_summary.json

Final output of Phase 5. Aggregates all phase results.

```json
{
  "overall_score": 84,
  "grade": "B",
  "coherence": {
    "score": 84,
    "total_claims": 42,
    "verified": 32,
    "stale": 4,
    "partial": 2,
    "unverifiable": 4
  },
  "effectiveness": {
    "score": 85,
    "total_tasks": 5,
    "claude_md_wins": 4,
    "ties": 1,
    "losses": 0,
    "programmatic_delta": "+50%"
  },
  "top_issues": [
    {
      "severity": "high",
      "claim_id": "path-3",
      "issue": "Stale path: `src/api/handlers/` does not exist",
      "suggestion": "Update to `src/app/api/`"
    },
    {
      "severity": "medium",
      "claim_id": "vague-1",
      "issue": "Vague instruction: 'Write clean, maintainable code'",
      "suggestion": "Replace with specific rules like '2-space indentation' or 'max 150 lines per component'"
    }
  ],
  "recommendations": {
    "remove": ["vague-1", "generic-2"],
    "fix": [{"claim_id": "path-3", "current": "src/api/handlers/", "suggested": "src/app/api/"}],
    "add": ["No test command found — add test runner instructions"],
    "strengthen": ["conv-7 adherence is 90% — add linting rule to enforce"]
  }
}
```
