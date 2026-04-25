---
name: laravel-boost
description: "Expert Laravel 12.x development skill powered by Laravel Boost MCP. Use this skill when working in any Laravel project that has Laravel Boost installed — building features, debugging errors, writing migrations/models, creating tests, or any Laravel development task. Triggers on: Laravel, Eloquent, Blade, Livewire, Inertia, Artisan, migration, controller, model, route, middleware, Pest, PHPUnit, or any PHP web framework task in a project with composer.json."
---

# Laravel Development with Boost MCP

Build idiomatic Laravel 12.x applications by orchestrating Laravel Boost's MCP tools for deep application context. This skill requires Laravel Boost to be installed in the project.

---

## Prerequisite: Verify Boost

**Before doing anything else**, call the `application-info` Boost MCP tool.

- **If it succeeds**: Extract PHP version, Laravel version, installed packages, and Eloquent models. Proceed with the workflow below.
- **If it fails**: Boost is not available. Tell the user:

```
Laravel Boost is required. Install it with:
  composer require laravel/boost --dev
  php artisan boost:install
```

Then stop — do not proceed without Boost.

---

## Stack Detection

From the `application-info` response, detect the project's stack:

| Check for package | Stack mode |
|---|---|
| `livewire/livewire` | **Livewire** (+ check for `livewire/volt` → Volt) |
| `inertiajs/inertia-laravel` | **Inertia** (+ check for `inertiajs/inertia-react`, `inertia-vue`, `inertia-svelte`) |
| Neither | **Blade-only** |

Also detect:
- **Test framework**: `pestphp/pest` → Pest, otherwise PHPUnit
- **CSS**: `tailwindcss` version (3.x vs 4.x)
- **Other packages**: Flux UI, Folio, Pennant, Wayfinder — adapt guidance if present

Use the detected stack to tailor all code generation and advice throughout the session.

---

## Workflow Selection

Based on the user's task, follow one of four workflows. Each workflow is summarized below — load `references/workflows.md` for expanded steps with concrete examples.

### 1. Feature Development

When the user wants to build something new (endpoint, page, component, feature).

**Tool sequence:**
1. `application-info` → understand installed packages and models
2. `database-schema` → review existing tables and relationships
3. `list-artisan-commands` → find relevant generators (`make:model`, `make:controller`, etc.)
4. `search-docs` → look up relevant Laravel APIs before writing code
5. Implement: migrations → models → controllers/components → routes → views/pages
6. Write tests using detected test framework

**Key rules:**
- Use `artisan make:*` commands instead of manually creating files
- Always use `search-docs` before using an API you're not certain about
- Follow Laravel 12.x conventions: invokable single-action controllers, form requests for validation, API resources for JSON responses, enum casting for status fields

### 2. Debugging

When something is broken or behaving unexpectedly.

**Tool sequence:**
1. `last-error` → get the most recent exception with stack trace
2. `read-log-entries` → get broader log context (last 20-50 entries)
3. `browser-logs` → check for frontend errors (JS, console, network)
4. `database-schema` → verify table/column existence if DB-related
5. `database-query` → run diagnostic read-only queries
6. `search-docs` → confirm correct API usage for the code in question

**Key rules:**
- Read the actual error before guessing — always start with `last-error`
- Use `database-query` for read-only diagnostics only (SELECT queries)
- Check `browser-logs` when the issue involves frontend behavior
- After fixing, verify the fix addresses the root cause, not just the symptom

### 3. Database Work

When working on schema, migrations, models, or relationships.

**Tool sequence:**
1. `database-connections` → identify available connections and the default
2. `database-schema` → get full schema (tables, columns, indexes, foreign keys)
3. `search-docs` → look up migration methods, Eloquent relationships, or casting
4. Generate: `artisan make:migration`, `artisan make:model`
5. `database-query` → verify results after migration with SELECT queries

**Key rules:**
- Always check existing schema before creating migrations to avoid conflicts
- Use Laravel's column types and modifiers (`->nullable()`, `->default()`, `->index()`)
- Define relationships on both sides of the Eloquent models
- Use `$casts` for date, enum, JSON, and boolean columns
- Prefer `foreignId('user_id')->constrained()` over manual foreign keys

### 4. Testing

When writing or fixing tests.

**Tool sequence:**
1. `application-info` → detect Pest or PHPUnit
2. `database-schema` → understand data structures for factories/assertions
3. `search-docs` → look up testing helpers, assertion methods, or mocking patterns
4. Write tests following detected framework conventions
5. Run tests via `php artisan test`

**Key rules:**
- Use Pest if installed (arch tests, `it()`, `expect()` API, `describe()` blocks)
- Use model factories with proper states for test data
- Test HTTP responses: status codes, JSON structure, redirects, session data
- Use `RefreshDatabase` trait for database tests
- Write feature tests for endpoints, unit tests for isolated logic

---

## Cross-Cutting Principles

These apply to ALL workflows:

### Always Use Boost Tools First
- **Before writing Eloquent queries** → call `database-schema` to verify columns and relationships
- **Before using unfamiliar APIs** → call `search-docs` with the topic
- **Before creating files manually** → call `list-artisan-commands` to check if a generator exists
- **Before debugging blindly** → call `last-error` and `read-log-entries`

### Laravel 12.x Conventions
- **Controllers**: Prefer invokable single-action controllers for simple endpoints
- **Validation**: Use Form Request classes, not inline validation for non-trivial rules
- **API responses**: Use API Resources and Resource Collections
- **Routing**: Use `Route::resource()` and `Route::apiResource()` where appropriate
- **Middleware**: Register middleware in `bootstrap/app.php` (Laravel 12.x pattern)
- **Config**: Access via `config()` helper, never `env()` outside config files
- **Enums**: Use backed enums with `$casts` for status/type fields

### Code Quality
- Run `./vendor/bin/pint` for code style (if Pint is installed)
- Follow PSR-12 coding standards
- Use strict types: `declare(strict_types=1);` in all PHP files
- Type-hint method parameters and return types

---

## Reference Files

Load these when you need deeper guidance:

- **[Boost MCP Tools Guide](./references/boost-tools.md)** — Detailed documentation for each Boost MCP tool: what it returns, when to use it, how to combine results, common patterns
- **[Development Workflows](./references/workflows.md)** — Expanded step-by-step workflows with concrete examples, tool call sequences, and decision points for feature development, debugging, database work, and testing
