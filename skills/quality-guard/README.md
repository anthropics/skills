# quality-guard v1.0

Behavior-driven test design and execution for AI-generated or legacy code.

quality-guard is an [Agent Skill](https://www.mintlify.com/blog/skill-md) that reviews your code, maps its behaviors, designs multi-layer tests (E2E / Integration / Behavioral / Unit), and writes tests — all without modifying production code.

## Why

Traditional testing chases coverage metrics. quality-guard chases **behavioral truth**.

- Tests must verify **intent**, not implementation
- Test failures are **discoveries**, not errors
- What you don't cover matters as much as what you do

## Core Principles

| Principle | What it means |
|-----------|---------------|
| **Accuracy** | Report only what is true. When uncertain, pause and ask. |
| **Independence** | Tests verify intent, not implementation. Never just confirm "code does what code does". |
| **Falsifiability** | Every test must be capable of failing. Vacuous assertions are rejected. |
| **Honest Incompleteness** | Explicitly declare uncovered behaviors. False completeness is dangerous. |
| **Adversarial Mindset** | Design tests to break the system, not confirm it works. |

## Install

### Claude Code

```bash
# Copy to your project
cp -r quality-guard/SKILL.md .claude/skills/quality-guard/SKILL.md

# Or copy to global skills (available in all projects)
cp -r quality-guard/SKILL.md ~/.claude/skills/quality-guard/SKILL.md
```

### Cursor

```bash
# Copy to your project
cp -r quality-guard/SKILL.md .cursor/skills/quality-guard/SKILL.md

# Or copy to global skills
cp -r quality-guard/SKILL.md ~/.cursor/skills/quality-guard/SKILL.md
```

## Usage

```
/quality-guard
```

Just run `/quality-guard` — the skill automatically detects which phase to enter based on existing artifacts:

1. **Phase 0: Scope Selection** — helps you pick the right area to focus on
2. **Phase 1: Behavior Mapping** — reads code, maps behaviors, asks you to confirm
3. **Phase 2: Test Plan Design** — designs test cases with rationale, you review priorities
4. **Phase 3: Test Execution** — writes tests, runs them, reports discoveries

Each phase ends with a confirmation gate — the skill never proceeds without your approval.

### Key constraints

- **No production code modifications** — only test files, mocks, and fixtures
- **No branch-coverage testing** — every test must have a behavioral rationale
- **No internal mocking** — only mock at system boundaries (external APIs, time, randomness)
- **Failures = discoveries** — test failures are reported as behavioral discrepancies, never silently fixed

## Runtime Artifacts

All artifacts are stored in `.quality-guard/` (add to `.gitignore` if desired):

```
.quality-guard/
├── project.md              ← Project architecture map
├── scope.md                ← Scope index and status
└── {scope-name}/
    ├── behavior-map.md     ← What the code does (Phase 1)
    ├── test-plan.md        ← Test design + checklist (Phase 2)
    └── discovery-report.md ← Findings and discrepancies (Phase 3)
```

## License

MIT
