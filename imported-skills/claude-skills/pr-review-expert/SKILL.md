---
name: "pr-review-expert"
description: "Use when the user asks to review pull requests, analyze code changes, check for security issues in PRs, or assess code quality of diffs."
---

# PR Review Expert

**Tier:** POWERFUL
**Category:** Engineering
**Domain:** Code Review / Quality Assurance

---

## Overview

Structured, systematic code review for GitHub PRs and GitLab MRs. Goes beyond style nits — this skill
performs blast radius analysis, security scanning, breaking change detection, and test coverage delta
calculation. Produces a reviewer-ready report with a 30+ item checklist and prioritized findings.

---

## Core Capabilities

- **Blast radius analysis** — trace which files, services, and downstream consumers could break
- **Security scan** — SQL injection, XSS, auth bypass, secret exposure, dependency vulns
- **Test coverage delta** — new code vs new tests ratio
- **Breaking change detection** — API contracts, DB schema migrations, config keys
- **Ticket linking** — verify Jira/Linear ticket exists and matches scope
- **Performance impact** — N+1 queries, bundle size regression, memory allocations

---

## When to Use

- Before merging any PR/MR that touches shared libraries, APIs, or DB schema
- When a PR is large (>200 lines changed) and needs structured review
- Onboarding new contributors whose PRs need thorough feedback
- Security-sensitive code paths (auth, payments, PII handling)
- After an incident — review similar PRs proactively

---

## Fetching the Diff

### GitHub (gh CLI)
```bash
# View diff in terminal
gh pr diff <PR_NUMBER>

# Get PR metadata (title, body, labels, linked issues)
gh pr view <PR_NUMBER> --json title,body,labels,assignees,milestone

# List files changed
gh pr diff <PR_NUMBER> --name-only

# Check CI status
gh pr checks <PR_NUMBER>

# Download diff to file for analysis
gh pr diff <PR_NUMBER> > /tmp/pr-<PR_NUMBER>.diff
```

### GitLab (glab CLI)
```bash
# View MR diff
glab mr diff <MR_IID>

# MR details as JSON
glab mr view <MR_IID> --output json

# List changed files
glab mr diff <MR_IID> --name-only

# Download diff
glab mr diff <MR_IID> > /tmp/mr-<MR_IID>.diff
```

---

## Workflow

### Step 1 — Fetch Context

```bash
PR=123
gh pr view $PR --json title,body,labels,milestone,assignees | jq .
gh pr diff $PR --name-only
gh pr diff $PR > /tmp/pr-$PR.diff
```

### Step 2 — Blast Radius Analysis

For each changed file, identify:

1. **Direct dependents** — who imports this file?
```bash
# Find all files importing a changed module
grep -r "from ['\"].*changed-module['\"]" src/ --include="*.ts" -l
grep -r "require(['\"].*changed-module" src/ --include="*.js" -l

# Python
grep -r "from changed_module import\|import changed_module" . --include="*.py" -l
```

2. **Service boundaries** — does this change cross a service?
```bash
# Check if changed files span multiple services (monorepo)
gh pr diff $PR --name-only | cut -d/ -f1-2 | sort -u
```

3. **Shared contracts** — types, interfaces, schemas
```bash
gh pr diff $PR --name-only | grep -E "types/|interfaces/|schemas/|models/"
```

**Blast radius severity:**
- CRITICAL — shared library, DB model, auth middleware, API contract
- HIGH     — service used by >3 others, shared config, env vars
- MEDIUM   — single service internal change, utility function
- LOW      — UI component, test file, docs

### Step 3 — Security Scan

```bash
DIFF=/tmp/pr-$PR.diff

# SQL Injection — raw query string interpolation
grep -n "query\|execute\|raw(" $DIFF | grep -E '\$\{|f"|%s|format\('

# Hardcoded secrets
grep -nE "(password|secret|api_key|token|private_key)\s*=\s*['\"][^'\"]{8,}" $DIFF

# AWS key pattern
grep -nE "AKIA[0-9A-Z]{16}" $DIFF

# JWT secret in code
grep -nE "jwt\.sign\(.*['\"][^'\"]{20,}['\"]" $DIFF

# XSS vectors
grep -n "dangerouslySetInnerHTML\|innerHTML\s*=" $DIFF

# Auth bypass patterns
grep -n "bypass\|skip.*auth\|noauth\|TODO.*auth" $DIFF

# Insecure hash algorithms
grep -nE "md5\(|sha1\(|createHash\(['\"]md5|createHash\(['\"]sha1" $DIFF

# eval / exec
grep -nE "\beval\(|\bexec\(|\bsubprocess\.call\(" $DIFF

# Prototype pollution
grep -n "__proto__\|constructor\[" $DIFF

# Path traversal risk
grep -nE "path\.join\(.*req\.|readFile\(.*req\." $DIFF
```

### Step 4 — Test Coverage Delta

```bash
# Count source vs test files changed
CHANGED_SRC=$(gh pr diff $PR --name-only | grep -vE "\.test\.|\.spec\.|__tests__")
CHANGED_TESTS=$(gh pr diff $PR --name-only | grep -E "\.test\.|\.spec\.|__tests__")

echo "Source files changed: $(echo "$CHANGED_SRC" | wc -w)"
echo "Test files changed:   $(echo "$CHANGED_TESTS" | wc -w)"

# Lines of new logic vs new test lines
LOGIC_LINES=$(grep "^+" /tmp/pr-$PR.diff | grep -v "^+++" | wc -l)
echo "New lines added: $LOGIC_LINES"

# Run coverage locally
npm test -- --coverage --changedSince=main 2>/dev/null | tail -20
pytest --cov --cov-report=term-missing 2>/dev/null | tail -20
```

**Coverage delta rules:**
- New function without tests → flag
- Deleted tests without deleted code → flag
- Coverage drop >5% → block merge
- Auth/payments paths → require 100% coverage

### Step 5 — Breaking Change Detection

#### API Contract Changes
```bash
# OpenAPI/Swagger spec changes
grep -n "openapi\|swagger" /tmp/pr-$PR.diff | head -20

# REST route removals or renames
grep "^-" /tmp/pr-$PR.diff | grep -E "router\.(get|post|put|delete|patch)\("

# GraphQL schema removals
grep "^-" /tmp/pr-$PR.diff | grep -E "^-\s*(type |field |Query |Mutation )"

# TypeScript interface removals
grep "^-" /tmp/pr-$PR.diff | grep -E "^-\s*(export\s+)?(interface|type) "
```

#### DB Schema Changes
```bash
# Migration files added
gh pr diff $PR --name-only | grep -E "migrations?/|alembic/|knex/"

# Destructive operations
grep -E "DROP TABLE|DROP COLUMN|ALTER.*NOT NULL|TRUNCATE" /tmp/pr-$PR.diff

# Index removals (perf regression risk)
grep "DROP INDEX\|remove_index" /tmp/pr-$PR.diff
```

#### Config / Env Var Changes
```bash
# New env vars referenced in code (might be missing in prod)
grep "^+" /tmp/pr-$PR.diff | grep -oE "process\.env\.[A-Z_]+" | sort -u

# Removed env vars (could break running instances)
grep "^-" /tmp/pr-$PR.diff | grep -oE "process\.env\.[A-Z_]+" | sort -u
```

### Step 6 — Performance Impact

```bash
# N+1 query patterns (DB calls inside loops)
grep -n "\.find\|\.findOne\|\.query\|db\." /tmp/pr-$PR.diff | grep "^+" | head -20
# Then check surrounding context for forEach/map/for loops

# Heavy new dependencies
grep "^+" /tmp/pr-$PR.diff | grep -E '"[a-z@].*":\s*"[0-9^~]' | head -20

# Unbounded loops
grep -n "while (true\|while(true" /tmp/pr-$PR.diff | grep "^+"

# Missing await (accidentally sequential promises)
grep -n "await.*await" /tmp/pr-$PR.diff | grep "^+" | head -10

# Large in-memory allocations
grep -n "new Array([0-9]\{4,\}\|Buffer\.alloc" /tmp/pr-$PR.diff | grep "^+"
```

---

## Ticket Linking Verification

```bash
# Extract ticket references from PR body
gh pr view $PR --json body | jq -r '.body' | \
  grep -oE "(PROJ-[0-9]+|[A-Z]+-[0-9]+|https://linear\.app/[^)\"]+)" | sort -u

# Verify Jira ticket exists (requires JIRA_API_TOKEN to be SET in the environment).
# Credentials are fed to curl via a config read from stdin (-K -) so the token
# never appears in argv — `ps aux` / /proc/*/cmdline can't see it, and nothing
# secret lands in shell history. Never paste the raw token on the command line.
TICKET="PROJ-123"
: "${JIRA_API_TOKEN:?JIRA_API_TOKEN must be set}"
curl -s -K - "https://your-org.atlassian.net/rest/api/3/issue/$TICKET" <<EOF | \
  jq '{key, summary: .fields.summary, status: .fields.status.name}'
user = "user@company.com:$JIRA_API_TOKEN"
EOF

# Linear ticket — same pattern: the Authorization header goes through the
# stdin config, not a -H flag, to keep the key out of the process list.
LINEAR_ID="abc-123"
: "${LINEAR_API_KEY:?LINEAR_API_KEY must be set}"
curl -s -K - -H "Content-Type: application/json" \
  --data "{\"query\": \"{ issue(id: \\\"$LINEAR_ID\\\") { title state { name } } }\"}" \
  https://api.linear.app/graphql <<EOF | jq .
header = "Authorization: $LINEAR_API_KEY"
EOF
```

> **Security note:** for repeated Jira use, prefer a `~/.netrc` entry
> (`machine your-org.atlassian.net login user@company.com password <token>`,
> `chmod 600 ~/.netrc`) and call `curl -s --netrc …` — no secret material in
> the command at all.

---

## Complete Review Checklist (30+ Items)

```markdown
## Code Review Checklist

### Scope & Context
- [ ] PR title accurately describes the change
- [ ] PR description explains WHY, not just WHAT
- [ ] Linked Jira/Linear ticket exists and matches scope
- [ ] No unrelated changes (scope creep)
- [ ] Breaking changes documented in PR body

### Blast Radius
- [ ] Identified all files importing changed modules
- [ ] Cross-service dependencies checked
- [ ] Shared types/interfaces/schemas reviewed for breakage
- [ ] New env vars documented in .env.example
- [ ] DB migrations are reversible (have down() / rollback)

### Security
- [ ] No hardcoded secrets or API keys
- [ ] SQL queries use parameterized inputs (no string interpolation)
- [ ] User inputs validated/sanitized before use
- [ ] Auth/authorization checks on all new endpoints
- [ ] No XSS vectors (innerHTML, dangerouslySetInnerHTML)
- [ ] New dependencies checked for known CVEs
- [ ] No sensitive data in logs (PII, tokens, passwords)
- [ ] File uploads validated (type, size, content-type)
- [ ] CORS configured correctly for new endpoints

### Testing
- [ ] New public functions have unit tests
- [ ] Edge cases covered (empty, null, max values)
- [ ] Error paths tested (not just happy path)
- [ ] Integration tests for API endpoint changes
- [ ] No tests deleted without clear reason
- [ ] Test names clearly describe what they verify

### Breaking Changes
- [ ] No API endpoints removed without deprecation notice
- [ ] No required fields added to existing API responses
- [ ] No DB columns removed without two-phase migration plan
- [ ] No env vars removed that may be set in production
- [ ] Backward-compatible for external API consumers

### Performance
- [ ] No N+1 query patterns introduced
- [ ] DB indexes added for new query patterns
- [ ] No unbounded loops on potentially large datasets
- [ ] No heavy new dependencies without justification
- [ ] Async operations correctly awaited
- [ ] Caching considered for expensive repeated operations

### Code Quality
- [ ] No dead code or unused imports
- [ ] Error handling present (no bare empty catch blocks)
- [ ] Consistent with existing patterns and conventions
- [ ] Complex logic has explanatory comments
- [ ] No unresolved TODOs (or tracked in ticket)
```

---

## Output Format

Structure your review comment as:

```
## PR Review: [PR Title] (#NUMBER)

Blast Radius: HIGH — changes lib/auth used by 5 services
Security: 1 finding (medium severity)
Tests: Coverage delta +2%
Breaking Changes: None detected

--- MUST FIX (Blocking) ---

1. SQL Injection risk in src/db/users.ts:42
   Raw string interpolation in WHERE clause.
   Fix: db.query("SELECT * WHERE id = $1", [userId])

--- SHOULD FIX (Non-blocking) ---

2. Missing auth check on POST /api/admin/reset
   No role verification before destructive operation.

--- SUGGESTIONS ---

3. N+1 pattern in src/services/reports.ts:88
   findUser() called inside results.map() — batch with findManyUsers(ids)

--- LOOKS GOOD ---
- Test coverage for new auth flow is thorough
- DB migration has proper down() rollback method
- Error handling consistent with rest of codebase
```

---

## Common Pitfalls

- **Reviewing style over substance** — let the linter handle style; focus on logic, security, correctness
- **Missing blast radius** — a 5-line change in a shared utility can break 20 services
- **Approving untested happy paths** — always verify error paths have coverage
- **Ignoring migration risk** — NOT NULL additions need a default or two-phase migration
- **Indirect secret exposure** — secrets in error messages/logs, not just hardcoded values
- **Skipping large PRs** — if a PR is too large to review properly, request it be split

---

## Best Practices

1. Read the linked ticket before looking at code — context prevents false positives
2. Check CI status before reviewing — don't review code that fails to build
3. Prioritize blast radius and security over style
4. Reproduce locally for non-trivial auth or performance changes
5. Label each comment clearly: "nit:", "must:", "question:", "suggestion:"
6. Batch all comments in one review round — don't trickle feedback
7. Acknowledge good patterns, not just problems — specific praise improves culture
