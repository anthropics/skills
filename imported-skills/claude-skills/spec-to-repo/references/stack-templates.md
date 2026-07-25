# Stack Templates

Quick-reference templates for common tech stacks. Each template defines: file structure, manifest, entry point, and build/run commands.

---

## Next.js (TypeScript + Tailwind)

**When:** Web apps, dashboards, SaaS, landing pages with dynamic content.

**Manifest:** `package.json`
```json
{
  "scripts": {
    "dev": "next dev",
    "build": "next build",
    "start": "next start",
    "lint": "next lint",
    "test": "jest"
  }
}
```

**Core deps:** `next`, `react`, `react-dom`, `tailwindcss`, `postcss`, `autoprefixer`
**Auth:** `next-auth` (default) or `clerk`
**Database:** `prisma` (ORM) + `@prisma/client`
**Testing:** `jest`, `@testing-library/react`

**File structure:**
```
src/app/layout.tsx        — Root layout with providers
src/app/page.tsx          — Homepage
src/app/api/*/route.ts    — API routes
src/components/*.tsx       — Shared components
src/lib/*.ts              — Utilities, DB client
prisma/schema.prisma      — Database schema (if DB)
```

**Config files:** `tsconfig.json`, `tailwind.config.ts`, `next.config.ts`, `postcss.config.mjs`

---

## FastAPI (Python)

**When:** REST APIs, backends, microservices, data-driven services.

**Manifest:** `requirements.txt`
```
fastapi>=0.110.0
uvicorn>=0.29.0
sqlalchemy>=2.0.0
pydantic>=2.0.0
pytest>=8.0.0
httpx>=0.27.0
```

**File structure:**
```
main.py                   — FastAPI app, CORS, lifespan
models.py                 — SQLAlchemy models
schemas.py                — Pydantic schemas
database.py               — Engine, session factory
routers/*.py              — Route modules
tests/test_*.py           — pytest tests
```

**Run:** `uvicorn main:app --reload`
**Test:** `pytest`

---

## Express (TypeScript)

**When:** Node.js APIs, middleware-heavy backends, real-time services.

**Manifest:** `package.json`
```json
{
  "scripts": {
    "dev": "tsx watch src/index.ts",
    "build": "tsc",
    "start": "node dist/index.js",
    "test": "jest"
  }
}
```

**Core deps:** `express`, `cors`, `dotenv`
**Dev deps:** `typescript`, `tsx`, `@types/express`, `@types/node`, `jest`, `ts-jest`

**File structure:**
```
src/index.ts              — App setup, middleware, listen
src/routes/*.ts           — Route handlers
src/middleware/*.ts        — Auth, validation, error handling
src/models/*.ts           — Data models / ORM entities
src/lib/*.ts              — Utilities
tests/*.test.ts           — Jest tests
```

---

## Go (net/http or Gin)

**When:** High-performance APIs, CLI tools, systems programming.

**Manifest:** `go.mod`

**File structure (API):**
```
main.go                   — Entry point, router setup
handlers/*.go             — HTTP handlers
models/*.go               — Data structs
middleware/*.go            — Auth, logging
db/*.go                   — Database connection
*_test.go                 — Table-driven tests
```

**File structure (CLI):**
```
main.go                   — Entry point, flag parsing
cmd/*.go                  — Subcommands
internal/*.go             — Business logic
*_test.go                 — Tests
```

**Run:** `go run .`
**Test:** `go test ./...`
**Build:** `go build -o app .`

---

## Rust (Actix-web or Axum)

**When:** High-performance, safety-critical APIs, systems.

**Manifest:** `Cargo.toml`

**File structure:**
```
src/main.rs               — Entry point, server setup
src/routes/*.rs           — Route handlers
src/models/*.rs           — Data structs, serde
src/db.rs                 — Database pool
src/error.rs              — Error types
tests/*.rs                — Integration tests
```

**Run:** `cargo run`
**Test:** `cargo test`

---

## Flutter (Dart)

**When:** Cross-platform mobile apps (iOS + Android).

**Manifest:** `pubspec.yaml`

**File structure:**
```
lib/main.dart             — Entry point, MaterialApp
lib/screens/*.dart        — Screen widgets
lib/widgets/*.dart        — Reusable components
lib/models/*.dart         — Data classes
lib/services/*.dart       — API clients, storage
lib/providers/*.dart      — State management
test/*_test.dart          — Widget tests
```

**Run:** `flutter run`
**Test:** `flutter test`

---

## Rails (Ruby)

**When:** Full-stack web apps, CRUD-heavy applications, rapid prototyping.

**Manifest:** `Gemfile`

**File structure:** Standard Rails conventions (`app/`, `config/`, `db/`, `spec/`).

**Run:** `bin/rails server`
**Test:** `bin/rspec`

---

## Django (Python)

**When:** Full-stack Python web apps, admin-heavy apps, content management.

**Manifest:** `requirements.txt`
```
django>=5.0
djangorestframework>=3.15
pytest-django>=4.8
```

**File structure:**
```
manage.py
config/settings.py        — Settings
config/urls.py            — Root URL config
apps/<name>/models.py     — Models
apps/<name>/views.py      — Views or ViewSets
apps/<name>/serializers.py — DRF serializers
apps/<name>/urls.py       — App URL config
tests/test_*.py
```

**Run:** `python manage.py runserver`
**Test:** `pytest`

---

## CI Template (.github/workflows/ci.yml)

Adapt per stack:

```yaml
name: CI
on: [push, pull_request]
jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - name: Setup [runtime]
        uses: actions/setup-[runtime]@v5
        with:
          [runtime]-version: '[version]'
      - name: Install
        run: [install command]
      - name: Lint
        run: [lint command]
      - name: Test
        run: [test command]
      - name: Build
        run: [build command]
```

---

## .gitignore Essentials by Stack

| Stack | Must ignore |
|-------|------------|
| Node/Next.js | `node_modules/`, `.next/`, `.env`, `dist/`, `.turbo/` |
| Python | `__pycache__/`, `*.pyc`, `.venv/`, `.env`, `*.egg-info/` |
| Go | Binary name, `.env`, `vendor/` (if not committed) |
| Rust | `target/`, `.env` |
| Flutter | `.dart_tool/`, `build/`, `.env`, `*.iml` |
| Rails | `log/`, `tmp/`, `.env`, `storage/`, `node_modules/` |

All stacks: `.env`, `.DS_Store`, `*.log`, IDE folders (`.idea/`, `.vscode/`)
