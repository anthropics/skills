# Codex CLI Prompt Templates

Ready-to-use prompt templates for common tasks. Customize as needed.

## Architecture & Planning

### Plan Migration
```
Plan: migrate [project/system] from [current] to [target]
Include:
1. Risk analysis (breaking changes, performance impact)
2. Step-by-step implementation plan
3. Testing strategy for each phase
4. Rollback plan
5. Time estimate for each step
```

**Usage:**
```bash
codex -m gpt-5-codex --reasoning high "Plan: migrate from SQLAlchemy 1.x to 2.x\nInclude: risk analysis, step-by-step plan, testing strategy, rollback plan"
```

### Architecture Review
```
Review the architecture in [directory/files]
Analyze:
1. Separation of concerns
2. Dependency flow (do we have cycles?)
3. Testability (how would you add unit tests?)
4. Scalability constraints
5. Security concerns
Suggest improvements with rationale.
```

**Usage:**
```bash
./scripts/codex-review.sh "Review src/ architecture for scalability and testability"
```

---

## Code Review

### Security Audit
```
Security audit of [files/directory]
Identify:
1. Input validation issues
2. Authentication/authorization gaps
3. SQL injection / code injection risks
4. Sensitive data exposure
5. Dependency vulnerabilities

For each issue, provide:
- Severity (critical/high/medium/low)
- Example vulnerable code
- Recommended fix
- CWE/OWASP reference if applicable
```

**Usage:**
```bash
./scripts/codex-review.sh "Security audit of src/api/ for input validation and injection risks"
```

### Design Pattern Review
```
Code review of [files]
Focus on:
1. Design patterns used (identify them)
2. Adherence to SOLID principles
3. Opportunities for refactoring
4. Testing opportunities
Provide concrete examples of improvements.
```

**Usage:**
```bash
./scripts/codex-review.sh "Review src/services/ for design patterns and SOLID compliance"
```

---

## Refactoring

### Extract Interfaces
```
Refactor [files] to extract interfaces
Current architecture: [describe]
Goal: [improve testability/modularity/flexibility]

For each interface:
1. Define the interface
2. Show which classes implement it
3. Update code samples
4. List breaking changes (if any)
5. Testing approach
```

**Usage:**
```bash
./scripts/codex-refactor.sh "Extract interfaces from src/handlers/ to improve testability"
```

### Modernize Pattern
```
Modernize [files] from [old pattern] to [new pattern]
Examples of patterns to modernize:
- Callbacks → async/await
- Promise chains → async/await
- Class components → functional components (React)
- var → const/let (JavaScript)

For each change:
1. Before/after code
2. Migration steps
3. Potential breaking changes
4. Testing approach
```

**Usage:**
```bash
./scripts/codex-refactor.sh "Modernize src/utils/ from callbacks to async/await"
```

---

## Documentation

### API Documentation
```
Write comprehensive API documentation for [endpoint/file/directory]

Include for each endpoint:
1. Purpose and use case
2. HTTP method and path
3. Request parameters (query, body, headers)
4. Response codes and bodies
5. Error cases and recovery
6. Example requests/responses
7. Rate limits (if applicable)
8. Authentication required

Format: [Markdown/OpenAPI/HTML]
```

**Usage:**
```bash
./scripts/codex-document.sh "Write comprehensive API documentation for src/api/users/ in OpenAPI format"
```

### Architecture Decision Record (ADR)
```
Write an ADR (Architecture Decision Record) for [decision]

Format:
1. Status: [Proposed/Accepted/Deprecated/Superseded]
2. Context: [Problem, constraints, assumptions]
3. Decision: [What was decided and why]
4. Consequences: [Benefits and drawbacks]
5. Alternatives considered: [Why we didn't choose them]
6. Related decisions: [Other ADRs this connects to]

Decision examples:
- Use PostgreSQL instead of MongoDB
- Switch to microservices architecture
- Adopt event-driven design
- Move to Kubernetes
```

**Usage:**
```bash
./scripts/codex-document.sh "Write an ADR for adopting event-driven architecture instead of request-response"
```

### Getting Started Guide
```
Write a Getting Started guide for [project]

Include:
1. Prerequisites (Node.js version, etc.)
2. Installation (git clone, npm install, setup steps)
3. Environment setup (.env, secrets, configuration)
4. Running the application (dev server, build, etc.)
5. Running tests (unit, integration, e2e)
6. Common tasks (making a request, testing a feature)
7. Troubleshooting (common issues and solutions)
8. Next steps (architecture tour, deeper dives)

Assume audience: new developer joining the team
```

**Usage:**
```bash
./scripts/codex-document.sh "Write a Getting Started guide for onboarding new developers to this project"
```

---

## Debugging

### Analyze Logs
```
Analyze these logs and identify:
1. Root causes of errors
2. Patterns or repeated issues
3. Severity (critical/high/warning)
4. Recommended fixes

Logs:
[paste logs]
```

**Usage:**
```bash
./scripts/codex-debug.sh "Analyze error logs and identify root causes"
```

### Memory/Performance Investigation
```
Investigate performance issue: [description]

Analyze:
1. Potential causes (bottlenecks, memory leaks, inefficient queries)
2. How to measure/reproduce
3. Recommended fixes (with code examples)
4. Expected performance improvement
5. Testing approach

Provide:
- Profiling commands to use
- Code changes with explanations
- Before/after metrics estimate
```

**Usage:**
```bash
./scripts/codex-debug.sh "Diagnose: why is memory usage growing indefinitely in production"
```

---

## Testing

### Test Generation
```
Generate comprehensive tests for [file/function]

Include:
1. Unit tests (happy path + edge cases)
2. Integration tests (if applicable)
3. Mocking strategy (what to mock)
4. Test data setup
5. Coverage goals

Framework: [Jest/Vitest/pytest/etc.]
Coverage target: 80%+
```

**Usage:**
```bash
codex exec -o tests.js "Generate comprehensive tests for src/utils/parser.ts using Vitest\nInclude: happy path, edge cases, error handling, mocking strategy"
```

---

## Performance

### Optimization Opportunities
```
Identify optimization opportunities in [files]

Analyze:
1. Algorithm complexity (any O(n²) that could be better?)
2. Database queries (N+1 queries? Missing indexes?)
3. Memory usage (unnecessary allocations?)
4. I/O operations (parallelizable?)
5. Caching opportunities

For each opportunity:
1. Estimated impact (% improvement)
2. Implementation effort (quick/medium/complex)
3. Code changes needed
4. Trade-offs
```

**Usage:**
```bash
./scripts/codex-review.sh "Identify performance optimization opportunities in src/database/ focusing on queries and caching"
```

---

## General Command Patterns

### Basic Syntax
```bash
# Interactive mode (REPL-like, asks for approval)
codex "Your prompt here"

# Non-interactive (auto-execute, no approval)
codex exec "Your prompt here"

# Specify model and reasoning
codex -m gpt-5-codex --reasoning high "Your prompt"

# Save to file
codex exec -o output.md "Your prompt"

# JSON output for piping
codex exec --json "Your prompt" | jq '.content'
```

### Using Helper Scripts
```bash
# Make scripts executable
chmod +x scripts/codex-*.sh

# Run from project root
./scripts/codex-plan.sh "Plan: add feature X"
./scripts/codex-review.sh "Review src/ for security"
./scripts/codex-document.sh "Write API docs"
./scripts/codex-refactor.sh "Extract interfaces"
./scripts/codex-debug.sh "Debug: why is X happening"
```

---

## Tips for Better Results

1. **Be Specific** - Include context: filenames, frameworks, constraints
2. **Show Examples** - If relevant, include before/after or example data
3. **Set Clear Goals** - "Improve readability" is vague; "Make this testable" is clear
4. **Use Right Model** - gpt-5-codex for complex code, gpt-5 for simple tasks
5. **Use Right Reasoning** - high for complex/ambiguous, medium for normal, low for simple/fast
6. **Structure Output** - Ask for numbered lists, code examples, rationale
7. **Iterate** - Review results, refine prompt, re-run if needed
