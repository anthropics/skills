---
name: agent-first-refactoring
description: Reshape and refactor existing repositories to be agent-first — optimized for AI coding agents like Claude Code and Codex. Use when a user wants to audit a codebase for agent-readiness, create or improve AGENTS.md files, refactor tests to run fast and in isolation, create clean interfaces between components, make internal tools agent-accessible (via CLI or MCP), establish code review processes for AI-generated code, or generally restructure a project so that AI agents are the primary tool for development rather than manual editing.
---

# Agent-First Repository Refactoring

Reshape existing repositories so that AI coding agents become the default tool for development tasks — reading, writing, testing, debugging, and operating the codebase.

## Guiding Principles

1. **Agent as first resort** — For any technical task, the tool of first resort for humans should be interacting with an agent rather than an editor or terminal directly.
2. **Safe defaults, productive workflows** — The default way agents operate should be explicitly safe, yet productive enough that most workflows need no additional permissions.
3. **No slop** — AI-generated code must meet the same review bar as human-written code. A human is accountable for every merge.

## Process

Refactoring a repository to be agent-first involves these steps:

1. Audit the repository for agent-readiness (run `scripts/audit_repo.py`)
2. Create or improve the AGENTS.md
3. Refactor tests for speed and isolation
4. Establish clean component interfaces
5. Make internal tools agent-accessible
6. Set up code quality guardrails for AI-generated code

Follow the steps in order. Steps 3–6 can be interleaved based on priority from the audit.

---

## Step 1: Audit the Repository

Run the audit script to get a baseline assessment:

```bash
python scripts/audit_repo.py <path-to-repo>
```

The script checks for:
- Presence and quality of AGENTS.md / CLAUDE.md
- Test suite characteristics (speed, isolation, naming)
- Interface boundaries between components
- CLI accessibility of internal tools
- CI/CD configuration agent-friendliness

Review the report and use it to prioritize which areas to address first.

---

## Step 2: Create or Improve AGENTS.md

Every agent-first repository needs an AGENTS.md (or CLAUDE.md) at the root. This is the single most impactful change — it gives agents the context they need to work autonomously.

See [references/agents-md-guide.md](references/agents-md-guide.md) for the complete guide on writing effective AGENTS.md files, including structure, examples, and anti-patterns.

**Quick checklist for a good AGENTS.md:**

- Build and test commands (exact copy-paste commands)
- Project structure overview (what lives where)
- Code conventions and style rules
- Common pitfalls and how to avoid them
- How to run linters, formatters, and type checkers
- Architecture decisions that affect how code should be written

Update AGENTS.md whenever the agent does something wrong or struggles with a task.

---

## Step 3: Refactor Tests for Speed and Isolation

Fast, reliable tests are the backbone of agent-first development. Agents run tests frequently as a feedback loop — slow or flaky tests destroy agent productivity.

See [references/test-refactoring.md](references/test-refactoring.md) for detailed patterns and strategies.

**Key targets:**

- **Individual test speed**: Each test should complete in under 1 second. Test suites for a single module should finish in under 10 seconds.
- **Isolation**: Tests must not depend on shared mutable state, external services, or execution order.
- **Granularity**: Prefer many small, focused tests over few large integration tests. Agents need precise failure signals.
- **Naming**: Test names should describe the behavior being verified, not the implementation.
- **Selective running**: Support running a single test file or test case without loading the entire suite.

**Common refactorings:**

1. Replace real API calls with deterministic mocks/fixtures
2. Replace database access with in-memory alternatives
3. Split monolithic test files by component or behavior
4. Add pytest markers (or equivalent) for fast/slow categorization
5. Extract test fixtures into shared conftest or setup modules

---

## Step 4: Establish Clean Component Interfaces

High-quality interfaces between components let agents work on one part of the codebase without understanding the whole thing. This is the "blast radius" principle — changes in one module should not ripple unpredictably.

See [references/codebase-patterns.md](references/codebase-patterns.md) for detailed patterns.

**Key actions:**

1. **Define explicit module boundaries** — Each major component should have a clear public API (exported functions/classes) and private internals. Use `__init__.py` exports, `index.ts` barrels, or equivalent.

2. **Use typed interfaces** — Type annotations, interfaces, and schemas at module boundaries make it possible for agents to understand contracts without reading implementation details.

3. **Reduce hidden coupling** — Identify and eliminate implicit dependencies: global state, environment variable reads scattered throughout, magic strings, and import side effects.

4. **Document architecture in AGENTS.md** — Describe the dependency graph and data flow between components so agents know which modules to read for context.

---

## Step 5: Make Internal Tools Agent-Accessible

Agents interact with tools through CLIs, scripts, and MCP servers. Any internal tool that team members use should have an agent-friendly interface.

**Inventory internal tools:**

1. List every tool the team uses for development, deployment, and operations
2. For each tool, assess: Can an agent invoke it via CLI or API?
3. Prioritize wrapping the most frequently used tools first

**Making tools accessible:**

- **CLI wrappers**: Create scripts with `--help`, clear argument names, structured output (JSON where appropriate), and non-zero exit codes on failure.
- **MCP servers**: For tools that benefit from richer interaction, create MCP servers. See the `mcp-builder` skill for guidance.
- **Documentation**: Add usage examples to AGENTS.md so agents know the tools exist and how to invoke them.

**Common tools to wrap:**
- Database migration runners
- Deployment scripts
- Secret/config management
- Internal API clients
- Code generation tools
- Monitoring/alerting queries

---

## Step 6: Code Quality Guardrails

AI-generated code at scale requires new processes to maintain quality.

**Establish these guardrails:**

1. **Require human accountability** — Every merged PR must have a human reviewer who understands and takes responsibility for the changes.

2. **Maintain the same review bar** — AI-generated code gets the same scrutiny as human-written code. Reviewers should not rubber-stamp because "the AI wrote it."

3. **Automate what you can** — Set up CI checks that agents can run before submitting:
   - Linters and formatters (with auto-fix where possible)
   - Type checkers
   - Test suites (fast subset for pre-commit, full suite in CI)
   - Security scanners (dependency audit, SAST)

4. **Track agent contributions** — Consider tagging commits or PRs that were agent-generated for observability. This helps teams understand the ratio of agent vs. human code and identify patterns in quality issues.

5. **Update AGENTS.md on failures** — When a reviewer catches a recurring issue in agent-generated code, add a rule to AGENTS.md to prevent it in the future. This creates a feedback loop.

---

## Reference Files

- [references/agents-md-guide.md](references/agents-md-guide.md) — Complete guide to writing effective AGENTS.md files with structure, examples, and anti-patterns
- [references/test-refactoring.md](references/test-refactoring.md) — Detailed strategies for making test suites fast, isolated, and agent-friendly
- [references/codebase-patterns.md](references/codebase-patterns.md) — Structural patterns for clean interfaces, modular boundaries, and reduced coupling
