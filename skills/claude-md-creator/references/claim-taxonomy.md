# Claim Taxonomy

Every instruction in a CLAUDE.md is a **claim** about how the project works or how code should be written. This document defines the types of claims, how to extract them, and how to verify each type.

## Table of Contents

1. [Claim Types](#claim-types)
2. [Extraction Patterns](#extraction-patterns)
3. [Verification Strategies](#verification-strategies)

---

## Claim Types

| Type | Description | Example | Testable |
|------|-------------|---------|----------|
| `command` | A CLI command for building, testing, linting, etc. | `` `pnpm dev` — start dev server `` | Yes |
| `path_reference` | A file or directory path | "API handlers live in `src/api/handlers/`" | Yes |
| `framework_reference` | A framework, library, or tool name | "Database queries through Prisma" | Yes |
| `convention` | A coding rule or pattern to follow | "Named exports only (no default exports)" | Yes |
| `naming_pattern` | A naming convention for files or identifiers | "Components: PascalCase, hooks: use- prefix" | Yes |
| `import_rule` | Import ordering or style requirement | "Import order: react → external → @/ → relative → types" | Yes |
| `architecture` | A structural description of the project | "App Router: pages in `app/`, components in `src/components/`" | Yes |
| `env_reference` | An environment variable reference | "`NEXT_PUBLIC_*` vars are in client bundle" | Yes |
| `workflow` | A git, CI/CD, or process instruction | "Run `npm test` before committing" | Partially |
| `vague` | An instruction too vague to verify | "Write clean code" | No |
| `generic` | Generic advice Claude already knows | "Use meaningful variable names" | No |

---

## Extraction Patterns

### command

Look for backtick-enclosed strings that start with a known command prefix or appear in a "commands" section.

**Regex patterns:**
```
`(npm|pnpm|yarn|npx|pip|python|cargo|make|go|ruby|bundle|docker|kubectl|terraform|gradle|mvn|dotnet|mix)\s+[^`]+`
```

Also match: bullets starting with `` ` `` followed by ` — ` or ` - ` description.

**Section hints:** "Build", "Run", "Test", "Lint", "Deploy", "Scripts"

### path_reference

Look for backtick-enclosed strings that look like filesystem paths.

**Regex patterns:**
```
`\.?/?[\w@-]+(/[\w@.*{}-]+)+/?`
```

Also match: directory descriptions like "X lives in `path`" or "X at `path`".

**Exclusions:** URLs (http/https), import paths without `/` context.

### framework_reference

Look for known framework/library names in natural language context.

**Known frameworks (detect case-insensitively):**
- JS/TS: React, Next.js, Vue, Angular, Svelte, Express, Fastify, Nest, Nuxt, Remix, Vite, Webpack, esbuild, Tailwind, Prisma, Drizzle, TypeORM, Sequelize, Mongoose, Jest, Vitest, Playwright, Cypress, ESLint, Prettier, Storybook, MSW, Zod
- Python: Django, Flask, FastAPI, SQLAlchemy, Alembic, pytest, Pydantic, Celery, Redis, Ruff, Black, mypy
- Rust: Tokio, Actix, Axum, Diesel, SeaORM, Serde, Clap
- Go: Gin, Echo, Fiber, GORM, sqlx
- Ruby: Rails, Sinatra, RSpec, Sidekiq
- General: Docker, Kubernetes, Terraform, PostgreSQL, MySQL, MongoDB, Redis, Elasticsearch, GraphQL, gRPC, Kafka, RabbitMQ

**Disambiguation:** "React" in "React component" = framework. "react" in "react to events" = not a framework.

### convention

Look for directive language patterns:

**Patterns:**
- "Use X" / "Always use X"
- "X only" / "X, not Y"
- "No X" / "Never X" / "Avoid X"
- "Prefer X over Y"
- "X should be Y"
- "X must be Y"
- Negation with reason: "Don't X because Y"

**Section hints:** "Style", "Conventions", "Rules", "Standards", "Guidelines"

### naming_pattern

Look for naming convention descriptions:

**Patterns:**
- "PascalCase" / "camelCase" / "snake_case" / "kebab-case" / "UPPER_SNAKE_CASE"
- "X: YCase" (e.g., "Components: PascalCase")
- "prefix X with Y" (e.g., "hooks: use- prefix")
- File naming patterns: "*.test.ts", "*.spec.ts"

### import_rule

Look for import ordering or style descriptions:

**Patterns:**
- "Import order: A → B → C"
- "`import type` on separate line"
- "No barrel imports"
- "@/ absolute path"
- "relative imports only within same directory"

### architecture

Look for directory structure descriptions:

**Patterns:**
- "X in `path/`" or "X lives in `path/`"
- Directory tree diagrams (indented with ├── or └──)
- "App Router" / "Pages Router" patterns
- Layer descriptions: "controllers", "services", "repositories"

### env_reference

Look for environment variable patterns:

**Patterns:**
- `UPPER_SNAKE_CASE` strings (especially with `NEXT_PUBLIC_`, `VITE_`, `REACT_APP_` prefixes)
- ".env" file references
- "environment variable" in text

### workflow

Look for process instructions:

**Patterns:**
- "before committing" / "before pushing"
- "branch naming" / "PR process"
- "CI/CD" / "pipeline"
- Git-related commands and conventions

### vague

Flag instructions that are too vague to verify:

**Indicators:**
- No specific tool, pattern, or measurable outcome
- Subjective quality terms without definition: "clean", "readable", "maintainable", "good", "proper"
- "Write X code" without specifying what X means

### generic

Flag advice Claude already knows:

**Known generic patterns:**
- "DRY principle" / "Don't repeat yourself"
- "KISS principle"
- "SOLID principles"
- "Keep functions small"
- "Use meaningful variable names"
- "Single responsibility"
- "Separation of concerns"

---

## Verification Strategies

### By claim type

| Type | Automated verification | Confidence |
|------|----------------------|------------|
| `command` | Parse package.json/Makefile scripts, check executable existence | High (1.0) |
| `path_reference` | `os.path.exists()` relative to project root | High (1.0) |
| `framework_reference` | Check dependency files (package.json, requirements.txt, etc.) | High (1.0) |
| `convention` | Sample 10-20 relevant files, regex check adherence ratio | Medium (0.7-0.9) |
| `naming_pattern` | List files in relevant dirs, match naming pattern | Medium (0.7-0.9) |
| `import_rule` | Parse import blocks from sampled files | Medium (0.7-0.9) |
| `architecture` | Directory existence + file type matching | High (0.9-1.0) |
| `env_reference` | Check .env.example or grep code for usage | Medium (0.8) |
| `workflow` | Check CI config files, git hooks | Medium (0.7-0.8) |
| `vague` | Not verified — flagged for improvement | N/A |
| `generic` | Not verified — flagged for removal | N/A |

### Dependency file detection

The verification engine auto-detects the project ecosystem by checking for:

| File | Ecosystem | What to check |
|------|-----------|---------------|
| `package.json` | Node.js/JS/TS | `scripts`, `dependencies`, `devDependencies` |
| `pyproject.toml` | Python | `[project.dependencies]`, `[tool.poetry.dependencies]`, `[project.scripts]` |
| `requirements.txt` | Python | Package list |
| `Cargo.toml` | Rust | `[dependencies]`, `[dev-dependencies]` |
| `go.mod` | Go | `require` block |
| `Gemfile` | Ruby | `gem` declarations |
| `pom.xml` | Java (Maven) | `<dependencies>` |
| `build.gradle` | Java/Kotlin (Gradle) | `dependencies` block |
| `composer.json` | PHP | `require`, `require-dev` |
| `mix.exs` | Elixir | `deps` function |
| `Makefile` | Any | Target names |
