# Boost MCP Tools Guide

Detailed reference for each Laravel Boost MCP tool. Use this to understand what each tool returns, when to call it, and how to combine tools effectively.

---

## Table of Contents

1. [application-info](#application-info)
2. [database-schema](#database-schema)
3. [database-query](#database-query)
4. [database-connections](#database-connections)
5. [search-docs](#search-docs)
6. [last-error](#last-error)
7. [read-log-entries](#read-log-entries)
8. [browser-logs](#browser-logs)
9. [list-artisan-commands](#list-artisan-commands)
10. [get-absolute-url](#get-absolute-url)
11. [Tool Combination Patterns](#tool-combination-patterns)

---

## application-info

**What it does:** Returns PHP version, Laravel version, database engine, installed ecosystem packages with versions, and registered Eloquent models.

**When to call:**
- At the **start of every session** — this is your prerequisite check and stack detection source
- When you need to know what packages are available before suggesting code
- When you need the list of existing Eloquent models

**What to extract:**
- PHP version → determines available language features (enums require 8.1+, readonly classes require 8.2+)
- Laravel version → determines framework APIs and conventions
- Packages → drives stack detection (Livewire, Inertia, Pest, Tailwind, Flux, etc.)
- Models → understand existing domain structure before creating new ones

**Typical response shape:**
- PHP version string
- Laravel version string
- Database engine (MySQL, PostgreSQL, SQLite)
- List of Laravel ecosystem packages with versions
- List of registered Eloquent model class names

---

## database-schema

**What it does:** Returns the complete database schema — tables, columns with types, indexes, and foreign key constraints.

**When to call:**
- Before writing **any** migration to check for existing tables/columns
- Before writing Eloquent queries or relationships to verify column names
- When debugging "column not found" or relationship errors
- When the user asks to add a feature that involves data storage

**How to use the results:**
- Check column types before writing casts or validation rules
- Identify existing foreign keys to understand relationships
- Spot missing indexes that should be added
- Verify nullable columns before writing NOT NULL constraints

**Combine with:**
- `database-query` → run a SELECT to see actual data after reviewing schema
- `search-docs` → look up migration methods for column types you need
- `application-info` → cross-reference with Eloquent models to find gaps

---

## database-query

**What it does:** Executes a SQL query against the database. Use for **read-only diagnostic queries only**.

**When to call:**
- To verify data exists after running a migration or seeder
- To diagnose data-related bugs (checking actual values, NULL states, duplicates)
- To count records or check relationship integrity
- To validate that a fix resolved a data issue

**Rules:**
- **SELECT queries only** — never use for INSERT, UPDATE, DELETE, or DDL
- Keep queries simple and targeted — avoid full table scans on large tables
- Use LIMIT when exploring data (`SELECT * FROM users LIMIT 10`)
- Use COUNT, GROUP BY, or JOINs for diagnostic summaries

**Combine with:**
- `database-schema` → always review schema first to know column names and types
- `last-error` → if the error is data-related, query to verify the problematic state

---

## database-connections

**What it does:** Lists available database connections and identifies the default connection.

**When to call:**
- When the project might use multiple databases
- Before running `database-schema` or `database-query` if you need to target a specific connection
- When debugging connection-related errors

**Typical use:**
- Most projects use a single default connection — call this only when you suspect multiple databases
- Identify if the project uses MySQL, PostgreSQL, or SQLite — influences migration syntax for some features

---

## search-docs

**What it does:** Queries Laravel's hosted documentation API with semantic search across 17,000+ pieces of Laravel ecosystem documentation. Results are filtered by the project's installed package versions.

**When to call:**
- **Before using any Laravel API you're not 100% certain about** — method signatures, available options, correct usage
- When the user asks "how do I do X in Laravel?"
- When you need to verify the correct syntax for a specific Laravel version
- When working with ecosystem packages (Livewire, Inertia, Pest) and need their specific APIs

**Query tips:**
- Use natural language: "how to define a many-to-many relationship with pivot data"
- Be specific: "Pest expectation API for JSON responses" is better than "testing"
- Include the package name if relevant: "Livewire 4 form validation"

**Combine with:**
- `application-info` → know which packages are installed before searching their docs
- The results are already version-filtered, so you get docs matching the project's actual versions

---

## last-error

**What it does:** Returns the most recent error/exception from the application's log files, including the full stack trace.

**When to call:**
- **First tool to call when debugging** — always start here
- When the user says something is "broken", "not working", or shows an error
- After making a change, to verify no new errors appeared

**How to read the results:**
- Exception class → tells you the category of error (QueryException, ValidationException, etc.)
- Message → the specific error description
- Stack trace → trace back to the originating code file and line
- Previous exception → check for chained exceptions

**Combine with:**
- `read-log-entries` → get broader context around the error
- `database-schema` → if it's a database error, verify the schema
- `search-docs` → look up the correct API usage for the code that threw the error

---

## read-log-entries

**What it does:** Returns the last N log entries from the application's log files.

**When to call:**
- After `last-error` when you need broader context (what happened before/after the error)
- When investigating intermittent issues — look for patterns across multiple entries
- When checking if a scheduled task or queue job ran correctly
- To verify that a fix resolved the issue (no new errors in logs)

**Tips:**
- Request 20-50 entries for initial investigation
- Look for repeated patterns — same error appearing multiple times
- Check timestamps to understand the sequence of events
- Look for warning-level entries that might indicate the root cause

**Combine with:**
- `last-error` → always call this first for the most recent error
- `browser-logs` → if the issue involves both backend and frontend

---

## browser-logs

**What it does:** Returns console logs and errors from the browser.

**When to call:**
- When the issue involves frontend behavior (JS errors, AJAX failures, rendering issues)
- When debugging Livewire or Inertia interactions
- When the backend seems fine but the UI isn't working correctly
- When checking for CORS errors, 422 validation responses, or network failures

**What to look for:**
- JavaScript errors and stack traces
- Failed network requests (4xx, 5xx status codes)
- Console warnings from Livewire/Inertia/Alpine
- Missing asset errors (404 for CSS/JS files)

**Combine with:**
- `last-error` → check if the frontend error triggered a backend error too
- `search-docs` → look up the correct frontend integration pattern

---

## list-artisan-commands

**What it does:** Returns all available Artisan commands with their descriptions and arguments.

**When to call:**
- Before manually creating a file — check if `artisan make:*` can generate it
- When the user asks to run an artisan command and you want to verify it exists
- To discover package-specific commands (e.g., Pest, Livewire, Inertia generators)

**Common generators to look for:**
- `make:model` (with `-m` for migration, `-f` for factory, `-s` for seeder, `-c` for controller)
- `make:controller` (with `--resource`, `--api`, `--invokable`)
- `make:migration`
- `make:request` (form request validation)
- `make:resource` (API resources)
- `make:test` (with `--pest` for Pest tests)
- `make:livewire` / `make:volt` (Livewire components)
- `make:middleware`
- `make:policy`
- `make:event` / `make:listener`

**Combine with:**
- `application-info` → know which packages are installed to expect their commands
- `search-docs` → look up command flags and options

---

## get-absolute-url

**What it does:** Converts relative path URIs to absolute URLs so agents generate valid, clickable URLs.

**When to call:**
- When generating URLs for the user to click (e.g., route URLs, asset paths)
- When constructing API endpoint URLs for documentation or testing
- When the user asks for a link to a specific route or page

---

## Tool Combination Patterns

### Pattern: "I need to build X"
```
application-info → database-schema → list-artisan-commands → search-docs → implement
```

### Pattern: "Something is broken"
```
last-error → read-log-entries → browser-logs → database-schema → search-docs → fix
```

### Pattern: "Add a database table/column"
```
database-connections → database-schema → search-docs → create migration → database-query (verify)
```

### Pattern: "Write tests for X"
```
application-info (detect framework) → database-schema → search-docs → write tests → run
```

### Pattern: "How do I do X in Laravel?"
```
search-docs → (if involves DB) database-schema → (if involves routes) application-info → answer
```
