---
language: rust
extensions: [".rs"]
---

# Rust — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only Rust-specific rules and idioms.

---

## PR Analyzer — Rust Risk Signals

- `unsafe { }` blocks — require explicit justification and sign-off
- `#[allow(...)]` attributes suppressing lints — verify they are justified
- `.unwrap()` / `.expect("")` on `Option` or `Result` outside of tests or prototypes
- Hardcoded credentials or tokens in source
- `TODO` / `FIXME` comments near `unsafe` or ownership code

---

## Code Quality — Rust Checks

- `.unwrap()` used broadly in production code — prefer `?`, `if let`, or `match`
- `clone()` called excessively — may indicate ownership design issues
- `Arc<Mutex<T>>` used where a simpler ownership model would work
- `Box<dyn Trait>` used where generics (`impl Trait`) would avoid heap allocation
- `pub` fields on structs that should enforce invariants — use accessor methods

---

## Security

- Flag `unsafe` blocks accessing raw pointers without clear safety invariant documented in a comment
- Flag `std::mem::transmute` — almost always a logic error or undefined behavior; require strong justification
- Flag `from_utf8_unchecked` on user-controlled data — use `from_utf8` with error handling
- Flag `unwrap()` on user-supplied input parsing — panics are a denial-of-service vector in server code
- Flag hardcoded secrets — use environment variables or a secrets crate

---

## Async / Concurrency

- Flag `std::sync::Mutex` used in async code — use `tokio::sync::Mutex` to avoid blocking the async runtime
- Flag `.await` inside a `std::sync::MutexGuard` scope — holds the lock across an await point, blocking other tasks
- Flag `spawn` without storing the `JoinHandle` — panics in the spawned task are silently ignored
- Flag `Arc<Mutex<T>>` cloned excessively — consider message passing via channels instead
- Flag blocking I/O calls (`std::fs`, `std::net`) inside async functions — use async equivalents

---

## Resource Management

- Flag manual `drop` called explicitly where the natural scope boundary suffices
- Flag `Rc<T>` used in multi-threaded code — use `Arc<T>`; the compiler catches this but flag in review for architecture discussion
- Flag `Vec` or `String` with large pre-allocated capacity never trimmed — call `.shrink_to_fit()` if long-lived
- Flag `impl Drop` that can panic — causes `abort` during stack unwinding

---

## Exception Handling

- Flag `.unwrap()` in production code outside of tests — use `?` to propagate or handle explicitly
- Flag `.expect("todo")` or `.expect("")` — messages must explain the invariant that guarantees safety
- Flag `panic!` used for recoverable errors — use `Result<T, E>`
- Flag `unwrap_or_default()` where the default silently masks a real error
- Prefer typed error enums (`thiserror`) over `Box<dyn Error>` for library crates
- Prefer `anyhow` for application-level error context; `thiserror` for library error types

---

## Performance

- Flag `.clone()` on large types in hot paths — review whether a reference or `Cow<T>` would work
- Flag `format!` used only to create a `String` from a literal — use `.to_string()` or `String::from`
- Flag `collect::<Vec<_>>()` followed immediately by `.iter()` — chain iterators instead
- Flag `Box<T>` for small types where stack allocation is fine
- Flag `Mutex` contention on a hot path — consider `RwLock` for read-heavy workloads or sharding

---

## Idioms and Best Practices

### Ownership
- Prefer borrowing (`&T`, `&mut T`) over cloning wherever the lifetime allows
- Use `Cow<'_, str>` for functions that sometimes need to own and sometimes borrow
- Prefer `impl Trait` in function signatures over `Box<dyn Trait>` for static dispatch

### Error Handling
- Use `?` operator to propagate errors — avoid manual `match Err(e) => return Err(e)`
- Define domain error types with `thiserror` in libraries; use `anyhow` in binaries
- Never use `.unwrap()` in library code — it panics the caller's thread

### Modern Rust
- Prefer `if let` / `while let` for single-variant matches over full `match`
- Prefer `?` over `unwrap` everywhere errors are recoverable
- Use `#[derive(Debug, Clone, PartialEq)]` consistently on data types
- Prefer `iter()` chains over manual loops — they compose and optimize well
- Use `clippy` and treat its lints as required — flag any `#[allow(clippy::...)]` in review
