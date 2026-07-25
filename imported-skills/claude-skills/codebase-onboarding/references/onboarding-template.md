# Onboarding Document Template

## README.md - Full Template

```markdown
# [Project Name]

> One-sentence description of what this does and who uses it.

[![CI](https://github.com/org/repo/actions/workflows/ci.yml/badge.svg)](https://github.com/org/repo/actions/workflows/ci.yml)
[![Coverage](https://codecov.io/gh/org/repo/branch/main/graph/badge.svg)](https://codecov.io/gh/org/repo)

## What is this?

[2-3 sentences: problem it solves, who uses it, current state]

**Live:** https://myapp.com  
**Staging:** https://staging.myapp.com  
**Docs:** https://docs.myapp.com

---

## Quick Start

### Prerequisites

| Tool | Version | Install |
|------|---------|---------|
| Node.js | 20+ | `nvm install 20` |
| pnpm | 8+ | `npm i -g pnpm` |
| Docker | 24+ | [docker.com](https://docker.com) |
| PostgreSQL | 16+ | via Docker (see below) |

### Setup (5 minutes)

```bash
git clone https://github.com/org/repo
cd repo
pnpm install
docker compose up -d
cp .env.example .env
pnpm db:migrate
pnpm db:seed
pnpm dev
pnpm test
```

### Verify it works

- [ ] App loads on localhost
- [ ] Health endpoint returns ok
- [ ] Tests pass

---

## Architecture

### System Overview

```
Browser / Mobile
    |
    v
[Next.js App] <- [Auth]
    |
    +-> [PostgreSQL]
    +-> [Redis]
    +-> [S3]
```

### Tech Stack

| Layer | Technology | Why |
|-------|-----------|-----|
| Frontend | Next.js | SSR + routing |
| Styling | Tailwind + shadcn/ui | Rapid UI |
| API | Route handlers | Co-location |
| Database | PostgreSQL | Relational |
| Queue | BullMQ + Redis | Background jobs |

---

## Key Files

| Path | Purpose |
|------|---------|
| `app/` | Pages and route handlers |
| `src/db/` | Schema and migrations |
| `src/lib/` | Shared utilities |
| `tests/` | Test suites and helpers |
| `.env.example` | Required variables |

---

## Common Developer Tasks

### Add a new API endpoint

```bash
touch app/api/my-resource/route.ts
touch tests/api/my-resource.test.ts
```

### Run a database migration

```bash
pnpm db:generate
pnpm db:migrate
```

### Add a background job

```bash
# Create worker module and enqueue path
```

---

## Debugging Guide

### Common Errors

- Missing environment variable
- Database connectivity failure
- Expired auth token
- Generic 500 in local dev

### Useful SQL Queries

- Slow query checks
- Connection status
- Table bloat checks

### Log Locations

| Environment | Logs |
|-------------|------|
| Local dev | local terminal |
| Production | platform logs |
| Worker | worker process logs |

---

## Contribution Guidelines

### Branch Strategy

- `main` protected
- feature/fix branches with ticket IDs

### PR Requirements

- CI green
- Tests updated
- Why documented
- Self-review completed

### Commit Convention

- `feat(scope): ...`
- `fix(scope): ...`
- `docs: ...`

---

## Audience-Specific Notes

### Junior Developers
- Start with core auth/data modules
- Follow tests as executable examples

### Senior Engineers
- Read ADRs and scaling notes first
- Validate performance/security assumptions early

### Contractors
- Stay within scoped feature boundaries
- Use wrappers for external integrations
```

## Usage Notes

- Keep onboarding setup under 10 minutes where possible.
- Include executable verification checks after each setup phase.
- Prefer links to canonical docs instead of duplicating long content.
- Update this template when stack conventions or tooling change.
