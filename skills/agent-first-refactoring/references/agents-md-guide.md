# Writing Effective AGENTS.md Files

An AGENTS.md (or CLAUDE.md) file is the single most impactful artifact for agent-first development. It serves as the onboarding document that gives AI agents the context they need to work autonomously in a repository.

## Table of Contents

- [Core Structure](#core-structure)
- [Section-by-Section Guide](#section-by-section-guide)
- [Nested AGENTS.md Files](#nested-agentsmd-files)
- [Maintenance](#maintenance)
- [Anti-Patterns](#anti-patterns)
- [Example](#example)

---

## Core Structure

A good AGENTS.md answers these questions in order:

1. **What is this project?** (1-2 sentences)
2. **How do I build and run it?** (exact commands)
3. **How do I run tests?** (exact commands, including single-file)
4. **What does the directory structure look like?**
5. **What are the code conventions?**
6. **What are the common pitfalls?**

## Section-by-Section Guide

### Project Overview

Keep it to 1-2 sentences. The agent needs orientation, not a marketing pitch.

```markdown
## Overview
Backend API service for user authentication and session management. Built with FastAPI, PostgreSQL, and Redis.
```

### Build and Run Commands

Provide exact, copy-paste commands. Include prerequisites.

```markdown
## Build & Run

Prerequisites: Python 3.11+, PostgreSQL 15+, Redis 7+

```bash
# Install dependencies
pip install -e ".[dev]"

# Run database migrations
alembic upgrade head

# Start development server
uvicorn app.main:app --reload --port 8000

# Start with docker compose (alternative)
docker compose up -d
```​
```

### Test Commands

This is the most critical section for agents. Include:
- How to run the full suite
- How to run a single file
- How to run a single test
- How to run fast tests only
- What the expected output looks like

```markdown
## Tests

```bash
# Full test suite
pytest

# Single file
pytest tests/test_auth.py

# Single test
pytest tests/test_auth.py::test_login_success

# Fast tests only (no network/DB)
pytest -m "not slow"

# With coverage
pytest --cov=app --cov-report=term-missing
```​

Tests should pass in under 30 seconds. If a test requires database access, it uses the test database configured via TEST_DATABASE_URL.
```

### Project Structure

Give a high-level directory map. Focus on where agents should look for different kinds of code.

```markdown
## Project Structure

```
app/
├── main.py              # FastAPI app initialization and middleware
├── api/                 # Route handlers, organized by domain
│   ├── auth.py          # Authentication endpoints
│   └── users.py         # User CRUD endpoints
├── models/              # SQLAlchemy ORM models
├── schemas/             # Pydantic request/response schemas
├── services/            # Business logic (called by routes)
├── db/                  # Database connection, session management
└── utils/               # Shared utilities (logging, errors)
tests/
├── conftest.py          # Shared fixtures (test DB, client, auth)
├── test_auth.py         # Auth endpoint tests
└── test_users.py        # User endpoint tests
```​
```

### Code Conventions

List the rules that matter. Be specific — vague guidelines are useless.

```markdown
## Conventions

- **Formatting**: Use `ruff format`. Run `ruff check --fix` before committing.
- **Type hints**: All function signatures must have type annotations. Use `mypy --strict` to verify.
- **Imports**: Use absolute imports. Group as: stdlib, third-party, local. `isort` handles this.
- **Error handling**: Raise `HTTPException` in route handlers. Use domain exceptions in services.
- **Naming**: snake_case for functions/variables, PascalCase for classes, UPPER_CASE for constants.
- **Database**: Never write raw SQL in route handlers. Use SQLAlchemy ORM or repository pattern.
```

### Common Pitfalls

Document things agents get wrong repeatedly. This section is the feedback loop — update it whenever an agent makes a mistake.

```markdown
## Pitfalls

- **Do not** modify `alembic/versions/` manually. Always generate migrations with `alembic revision --autogenerate -m "description"`.
- **Do not** import from `app.db.session` directly in tests. Use the `db_session` fixture from `conftest.py`.
- **Do not** add new environment variables without adding them to `.env.example` and documenting them in this file.
- The `User.email` field has a unique constraint. Tests that create users must use unique emails (use `faker` or UUID suffixes).
- The auth middleware skips `/health` and `/docs` routes. Do not add authentication checks to these paths.
```

---

## Nested AGENTS.md Files

For large repositories, place additional AGENTS.md files in subdirectories to provide context specific to that area. Agents typically read the root AGENTS.md first, then the one closest to the files they are working on.

```
repo/
├── AGENTS.md              # Global: build, test, structure, conventions
├── frontend/
│   └── AGENTS.md          # Frontend-specific: React patterns, component conventions
├── backend/
│   └── AGENTS.md          # Backend-specific: API patterns, DB conventions
└── infra/
    └── AGENTS.md          # Infra-specific: Terraform conventions, deployment
```

Each nested file should only contain information specific to that directory. Do not repeat global conventions.

---

## Maintenance

AGENTS.md is a living document. Update it:

- **After agent mistakes** — When an agent does something wrong, add a pitfall or convention to prevent it.
- **After onboarding** — When a new team member (human or agent) struggles, the missing context belongs in AGENTS.md.
- **After architecture changes** — New modules, changed conventions, or updated commands must be reflected immediately.
- **Periodically** — Review quarterly to remove stale information.

---

## Anti-Patterns

**Too long** — AGENTS.md over 500 lines becomes noise. Split into nested files or reference docs.

**Too vague** — "Follow best practices" or "Write clean code" tells the agent nothing. Be specific.

**Stale commands** — Commands that don't work are worse than no commands. Verify periodically.

**Duplicated info** — Don't repeat what's in README.md or docstrings. AGENTS.md is for agent-specific operational context.

**No pitfalls section** — This is the most valuable section. If it's empty, you're not iterating.

---

## Example

A minimal but effective AGENTS.md:

```markdown
# AGENTS.md

## Overview
URL shortener service. Go backend, React frontend, PostgreSQL database.

## Build & Run
```bash
make dev          # Start all services with hot reload
make build        # Production build
```​

## Tests
```bash
make test         # Full suite (~20s)
go test ./...     # Backend only
cd frontend && npm test -- --watchAll=false  # Frontend only
go test ./internal/shortener/...             # Single package
```​

## Structure
- `cmd/server/` — Entry point
- `internal/` — All Go packages (shortener, auth, storage)
- `frontend/` — React SPA
- `migrations/` — SQL migration files
- `Makefile` — All development commands

## Conventions
- Go: Follow `golangci-lint` rules. Run `make lint` before committing.
- React: Functional components only. Use `tanstack-query` for data fetching.
- DB: Migrations via `golang-migrate`. Never edit existing migration files.

## Pitfalls
- The `SHORT_URL_LENGTH` env var defaults to 6 in dev and 8 in prod. Tests assume 6.
- `internal/storage` uses connection pooling. Do not create new connections in request handlers.
- The React build expects `REACT_APP_API_URL` to be set. It defaults to `/api` in production.
```
