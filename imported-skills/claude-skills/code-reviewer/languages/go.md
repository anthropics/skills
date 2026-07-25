---
language: go
extensions: [".go"]
---

# Go — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only Go-specific rules and idioms.

---

## PR Analyzer — Go Risk Signals

- `fmt.Println` / `log.Println` debug statements left in production code
- `//nolint` comments — verify they are justified
- `unsafe` package imports — require explicit sign-off
- Hardcoded credentials or tokens in source

---

## Code Quality — Go Checks

- Errors returned but not checked (`_ = someFunc()`)
- `panic()` used outside of package initialization
- Goroutines started without a clear lifetime or cancellation path
- `interface{}` / `any` used where a concrete type or typed interface would work
- Missing context propagation (`context.Context` not threaded through call chains)

---

## Security

- Flag `database/sql` queries built with `fmt.Sprintf` — require `?` / `$N` placeholders
- Flag `os/exec` calls with user-controlled arguments without sanitization
- Flag `html/template` bypassed in favor of `text/template` for HTML output
- Flag `http.ListenAndServeTLS` with `InsecureSkipVerify: true`

---

## Async / Concurrency

- Flag goroutines started with no clear lifetime or cancellation path — always pass `context.Context`
- Flag goroutines that write to a channel with no receiver and no `select` default — causes a leak
- Flag `time.Sleep()` used inside a goroutine as a synchronization mechanism
- Flag `sync.WaitGroup.Add()` called inside the goroutine it tracks — race condition
- Flag `sync.Mutex` copied by value — must always be used as a pointer or embedded in a struct

---

## Resource Management

- Flag `http.Response.Body` not closed after reading — even on error paths (`defer resp.Body.Close()`)
- Flag `os.File` not closed — use `defer f.Close()` immediately after opening
- Flag `rows.Close()` missing after `sql.Query()` — leaks the DB connection
- Flag `context.WithCancel` / `context.WithTimeout` cancel function not called — context and resources leak

---

## Exception Handling

- Flag errors assigned to `_` without a comment explaining why it is safe to ignore
- Flag errors not wrapped with `fmt.Errorf("...: %w", err)` — loses stack context
- Flag `errors.New` / `fmt.Errorf` strings starting with a capital letter or ending in punctuation — violates Go conventions
- Flag `panic()` used for expected runtime errors — reserve for programming errors and unrecoverable states
- Flag `recover()` used to silently swallow panics without logging

---

## Performance

- Flag `fmt.Sprintf` used for simple string concatenation — use `strings.Builder` or `+` for small cases
- Flag `append()` in a tight loop without pre-allocating slice capacity — use `make([]T, 0, n)`
- Flag `json.Marshal` / `json.Unmarshal` on large structs in hot paths — consider `json.Encoder` / streaming
- Flag goroutines spawned per-request without a worker pool for CPU-bound tasks

---

## Idioms and Best Practices

### Error Handling
- All returned errors must be checked — never assign to `_` without a comment
- Prefer wrapping with `fmt.Errorf("...: %w", err)` for stack context
- Use `errors.Is` / `errors.As` for error inspection — never string comparison

### Concurrency
- Every goroutine must have an owner responsible for its lifetime
- Always pass `context.Context` as the first argument to functions that do I/O or block
- Prefer `sync.WaitGroup` or `errgroup` over ad-hoc channel coordination

### Modern Go (1.18+)
- Prefer generics over `interface{}` for container types and utility functions
- Use `any` (alias for `interface{}`) in new code for readability
