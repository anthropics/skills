# Spec Parsing Guide

How to extract structured requirements from ambiguous, incomplete, or conversational natural-language specifications.

---

## Parsing Strategy

Read the full spec once. On the second pass, extract fields into the structured interpretation table. Don't ask questions for anything you can reasonably infer.

### Extraction Priority

1. **Explicit statements** — "Use PostgreSQL", "Build with Next.js" — non-negotiable
2. **Strong signals** — "users can sign up" implies auth + user model + database
3. **Contextual inference** — "dashboard" implies web app; "track expenses" implies CRUD + database
4. **Defaults** — When nothing is specified, pick the most common choice for the domain

---

## Ambiguity Resolution

### Stack Not Specified

| Spec pattern | Default stack | Reasoning |
|---|---|---|
| Web app with UI | Next.js + TypeScript | Most versatile, SSR + API routes |
| API / backend only | FastAPI | Fast to scaffold, great DX, typed |
| Mobile app | Flutter | Cross-platform, single codebase |
| CLI tool | Python | Fastest to ship, stdlib-rich |
| "Simple" / "lightweight" | Express or Flask | Minimal overhead |
| "Fast" / "performance" | Go | Compiled, concurrent |

### Database Not Specified

| Signal | Default |
|---|---|
| User accounts, persistent data | PostgreSQL |
| Small project, local-only, CLI | SQLite |
| Document-oriented, flexible schema | MongoDB (only if user signals) |
| No data persistence mentioned | No database — don't add one |

### Auth Not Specified

| Signal | Default |
|---|---|
| "Users", "accounts", "login" | Yes — session-based or JWT |
| "Admin panel", "roles" | Yes — with role-based access |
| API with "API keys" | Yes — API key middleware |
| No user-facing features | No auth — don't add one |

---

## Common Spec Shapes

### Shape 1: Stream of Consciousness

> "I want an app where people can post recipes and other people can comment on them and save their favorites, maybe add a rating system too, and it should look nice on mobile"

**Extract:**
- Features: post recipes, comment, favorites, ratings
- UI: responsive / mobile-friendly
- Implies: auth (users), database (recipes, comments, favorites, ratings), web app

### Shape 2: Feature List

> "Features: 1. User registration 2. Create projects 3. Invite team members 4. Kanban board 5. File uploads"

**Extract:**
- Features: numbered list, each gets a route/component
- Auth: yes (registration)
- Database: yes (users, projects, teams, files)
- Complex features: kanban (drag-drop), file uploads (storage)

### Shape 3: Technical Spec

> "FastAPI backend with PostgreSQL. Endpoints: POST /items, GET /items, GET /items/{id}, PUT /items/{id}, DELETE /items/{id}. Use SQLAlchemy ORM. Add JWT auth."

**Extract:**
- Stack: explicit (FastAPI, PostgreSQL, SQLAlchemy, JWT)
- API: 5 CRUD endpoints, fully defined
- Minimal inference needed — generate exactly what's asked

### Shape 4: Existing PRD

> [Multi-page document with overview, user personas, feature requirements, acceptance criteria]

**Extract:**
- Read the overview first for scope
- Map feature requirements to files
- Use acceptance criteria as test case seeds
- Ignore personas, market analysis, timelines — they don't affect code generation

---

## What to Ask vs. What to Infer

**Ask (max 3 questions):**
- Stack preference when the spec is truly ambiguous and could go multiple ways
- Database choice when both SQL and NoSQL are equally valid
- Deploy target when it materially affects the code (serverless vs. container)

**Infer silently:**
- Auth method (JWT for APIs, session for web apps)
- Testing framework (most popular for the stack)
- Linter / formatter (stack default)
- CSS approach (Tailwind for React/Next, stack default otherwise)
- Package versions (latest stable)

**Never ask:**
- "What folder structure do you want?" — use the stack convention
- "Do you want TypeScript?" — yes, always for JS projects
- "Should I add error handling?" — yes, always
- "Do you want tests?" — yes, always
