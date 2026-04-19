# Linting Rules by Language

Key rule sets to cross-check refactored output against. You are **not running** these linters — this file documents their important rules so you produce code that would pass them.

For each language: the standard linter(s), the most important rules, and refactor-relevant style conventions.

## Table of contents

1. [JavaScript / TypeScript / JSX / TSX](#javascript--typescript)
2. [Python](#python)
3. [Go](#go)
4. [C / C++](#c--c)
5. [Java](#java)
6. [C# / .NET](#c--net)
7. [Ruby](#ruby)
8. [PHP](#php)
9. [Rust](#rust)
10. [General principles across languages](#general-principles-across-languages)

---

## JavaScript / TypeScript

**Linters**: ESLint (+ `@typescript-eslint/eslint-plugin` for TS), Prettier (formatting), Biome (newer all-in-one).

### Key ESLint rules to satisfy

- `no-unused-vars` — don't leave unused variables, parameters (prefix unused with `_` where intent is explicit).
- `no-undef` — every identifier must be defined or imported.
- `prefer-const` — use `const` unless reassignment is genuinely needed.
- `no-var` — never use `var`.
- `eqeqeq` — use `===` / `!==`, not `==` / `!=`.
- `no-shadow` — don't shadow outer scope variables with the same name.
- `no-param-reassign` — don't reassign function parameters.
- `consistent-return` — functions should consistently return a value or consistently not.
- `no-implicit-coercion` — no `+"" ` or `!!x` tricks; use explicit `String(x)` / `Boolean(x)`.

### TypeScript-specific (`@typescript-eslint`)

- `no-explicit-any` — avoid `any`; use `unknown` when the type is genuinely unknown and narrow from there.
- `no-unsafe-assignment` / `no-unsafe-call` / `no-unsafe-return` — don't feed `any`-typed values into typed holes.
- `explicit-function-return-type` (often relaxed) — at least public APIs should have explicit return types.
- `no-non-null-assertion` — avoid `!` postfix; use proper narrowing.
- `prefer-readonly` — mark fields `readonly` when they aren't reassigned.
- `consistent-type-imports` — use `import type` for type-only imports.

### React (`eslint-plugin-react`, `eslint-plugin-react-hooks`)

- `react-hooks/rules-of-hooks` — hooks only at top level, only from components/custom hooks.
- `react-hooks/exhaustive-deps` — include all used values in dependency arrays.
- `react/jsx-key` — every element in a list needs a `key`.
- Components extracted during refactoring should be named (PascalCase) and exported.

### Style conventions

- Prefer `.map`/`.filter`/`.reduce` over imperative loops when it reads cleanly.
- Prefer early returns (guard clauses) over nested `if` blocks.
- Prefer named exports over default exports in applications (easier to refactor across files).
- In TS, prefer interfaces for public APIs, types for unions and computed types.

## Python

**Linters**: ruff (preferred — fast, comprehensive), pylint, flake8. Formatters: black, isort (or just ruff format).

### Key ruff/pylint rules

- `E501` — line too long (PEP 8 is 79, black uses 88, many codebases 100 or 120 — match the project).
- `E741` — ambiguous variable names (`l`, `O`, `I`).
- `F401` — unused imports.
- `F811` — redefined names.
- `F841` — unused local variables.
- `W605` — invalid escape sequences in strings (use raw strings for regex).
- `N8xx` (pep8-naming) — snake_case functions/variables, PascalCase classes, UPPER_SNAKE for module constants.
- `B006` (flake8-bugbear) — don't use mutable default arguments (`def f(items=[])`).
- `B008` — don't call a function as a default argument.
- `SIM102`/`SIM108` — simplify nested ifs, use ternary where readable.
- `PLR0913` — too many arguments (default 5; refactor via Introduce Parameter Object, dataclass).

### Style conventions

- Use **type hints** on function signatures and class attributes; this aids refactoring tools.
- Prefer **dataclasses** (or `attrs`, or `pydantic.BaseModel`) for Data Clumps over ad-hoc tuples/dicts.
- Prefer **comprehensions** over `map`/`filter` for simple cases; use generator expressions for large datasets.
- Use **f-strings** (`f"{x}"`) — not `%` or `.format()`.
- Prefer **explicit imports** (`from x import y`) over `from x import *`.
- Respect the import order: stdlib → third-party → local.

## Go

**Linters**: `go vet`, `gofmt`, `golangci-lint` (meta-linter), `staticcheck`.

### Key rules

- `gofmt` is non-negotiable — every file passes gofmt.
- `errcheck` — every returned error is handled or explicitly ignored with `_`.
- `ineffassign` — no assignments whose values are never used.
- `govet` — catches suspicious constructs (wrong printf args, lock copies, etc.).
- `unused` — unused symbols are removed (Go is strict about this).
- `revive`/`golint` idioms — exported names have comments starting with the name; no `_` in names; initialisms stay caps (`URL`, `ID`, `HTTP`).

### Style conventions

- **Keep interfaces small** — the idiomatic Go interface has 1–3 methods (`io.Reader`, `io.Writer`).
- **Composition over inheritance** — the language enforces this; use struct embedding for "is-a-kind-of" reuse.
- Return `error` as the last return value, check immediately: `if err != nil { return err }`.
- Name things for clarity at point of use, not abstractly — short names in narrow scopes (`i`, `ok`), longer in wider.
- Use context (`context.Context`) as the first parameter of functions that might block or time out.
- Don't use getters/setters by default — export the field if it should be public.

## C / C++

**Linters**: clang-tidy (preferred), cpplint, cppcheck. Formatter: clang-format.

### Key clang-tidy checks

- `modernize-*` — use C++11/14/17/20 features (`nullptr`, `auto`, range-for, `make_unique`).
- `cppcoreguidelines-*` — C++ Core Guidelines (resource management, bounds safety, ownership).
- `readability-*` — naming, braces, magic numbers.
- `performance-*` — unnecessary copies, move semantics.
- `bugprone-*` — common bug patterns.
- `clang-analyzer-*` — memory leaks, null deref, undefined behavior.

### Style conventions

- **RAII** for resource management — constructors acquire, destructors release.
- **Smart pointers** (`std::unique_ptr`, `std::shared_ptr`) over raw `new`/`delete`.
- **`const` correctness** — mark methods, parameters, and references `const` by default; drop `const` only when mutation is required.
- **References over pointers** when the argument must not be null.
- **`nullptr` not `NULL` or `0`** in C++.
- Prefer `std::` algorithms over hand-rolled loops (`std::transform`, `std::find_if`, `std::accumulate`).
- Header guards or `#pragma once` on every header.
- In C specifically: check return values of `malloc`, `fopen`, etc. Use `size_t` for sizes. Avoid VLAs.

## Java

**Linters**: Checkstyle, SpotBugs, PMD, ErrorProne.

### Key rules

- Naming: `camelCase` methods/variables, `PascalCase` classes, `UPPER_SNAKE_CASE` constants.
- **No public mutable fields** — use accessors.
- Prefer `final` on fields and local variables where appropriate.
- Use `@Override` annotation on every override.
- Don't use raw types (`List` alone) — always parameterize (`List<String>`).
- Prefer `Optional<T>` over nullable returns where absence is meaningful.
- Use `try-with-resources` for `AutoCloseable` resources.
- Prefer interfaces (`List`, `Map`) in declarations, concrete types (`ArrayList`, `HashMap`) in constructors.
- Use streams (`list.stream().filter(...).map(...).toList()`) for functional transforms.

## C# / .NET

**Linters**: Roslyn analyzers (built in), StyleCop.Analyzers, SonarAnalyzer.

### Key rules

- Naming: `PascalCase` for types, methods, properties; `camelCase` for locals and parameters; `_camelCase` for private fields (optional).
- Use `var` when type is obvious from RHS; use explicit type otherwise.
- Prefer `async`/`await` over raw `Task.ContinueWith`.
- Name async methods with `Async` suffix.
- Use nullable reference types (`string?` vs `string`) and `#nullable enable`.
- Prefer `record` types for immutable data clumps.
- Use LINQ (`Where`, `Select`, `OrderBy`) over hand loops for transforms.
- Prefer `using` declarations / `using` statements for `IDisposable`.
- Use expression-bodied members for one-line methods/properties.

## Ruby

**Linters**: RuboCop, Reek (code smell focused), Standard.

### Key rules

- `Metrics/MethodLength`, `Metrics/ClassLength` — keep methods and classes short.
- `Style/GuardClause` — prefer guard clauses over nested conditionals.
- `Lint/UnusedMethodArgument` / `Lint/UnusedBlockArgument`.
- Use `snake_case` methods/variables, `CamelCase` classes/modules, `SCREAMING_SNAKE_CASE` constants.
- Prefer `each` over `for`; prefer `map`/`select`/`reject` over `each` + accumulator.
- Prefer symbol syntax for hash keys (`{foo: 1}`) in Ruby 1.9+.
- Use `&.` (safe navigation) where null checks would otherwise cascade.
- Use keyword arguments for methods with more than 2–3 parameters.

## PHP

**Linters**: PHPStan, Psalm (static analysis), PHP_CodeSniffer (style).

### Key rules

- Follow PSR-12 coding style.
- Namespace PascalCase; classes PascalCase; methods/variables camelCase; constants SCREAMING_SNAKE.
- Declare types on parameters, return types, and properties (PHP 7.4+ / 8.0+).
- Prefer strict types (`declare(strict_types=1);`) at top of each file.
- Use `readonly` properties (PHP 8.1+) for immutable data.
- Use constructor property promotion (PHP 8.0+) to avoid boilerplate.
- Prefer composition; use interfaces for public contracts.

## Rust

**Linters**: `clippy` (the definitive lint), `rustfmt`.

### Key clippy categories

- `clippy::correctness` — likely bugs (must fix).
- `clippy::suspicious` — probably wrong.
- `clippy::style` — idiomatic Rust.
- `clippy::complexity` — simplifications.
- `clippy::perf` — performance tweaks.
- `clippy::pedantic` (opt-in) — stricter idiomatic Rust.

### Style conventions

- Naming: `snake_case` for fns/vars, `CamelCase` for types, `SCREAMING_SNAKE` for consts.
- Prefer iterators (`.iter().map().filter().collect()`) over explicit loops.
- Use `Result<T, E>` for recoverable errors, `panic!` only for unrecoverable.
- Prefer `?` operator for error propagation.
- Use `match` exhaustively; the compiler enforces it.
- Lifetimes: elide where possible, name explicitly when not.

---

## General principles across languages

Regardless of language, these cross-cutting rules should hold after a refactor:

1. **No unused symbols** — variables, imports, parameters, functions, or methods. Delete or mark intentionally unused (`_`, `@unused`, etc.).
2. **Consistent naming conventions** — don't mix styles within a file or module. Preserve the project's existing convention unless the convention itself is the smell.
3. **Explicit over implicit** — explicit types (when the language supports them), explicit return values, explicit error handling. Refactoring away implicit behavior is usually a win.
4. **Short functions** — if a function exceeds ~30 lines, the linter probably has an opinion; Extract Method before leaving the refactor.
5. **Public API surface should be minimal** — private/internal by default, public only when genuinely needed externally. Most linters have rules enforcing this.
6. **No commented-out code** — if it's worth keeping, it's worth in version control. Delete.
7. **Matching formatter output** — code should look like it was run through the language's standard formatter (gofmt, black, prettier, rustfmt, etc.).
