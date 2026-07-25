---
language: swift
extensions: [".swift"]
---

# Swift — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only Swift-specific rules and idioms.

---

## PR Analyzer — Swift Risk Signals

- `print()` statements left in production code
- Force unwrap (`!`) on optionals outside of tests or justified init
- Force cast (`as!`) without a safe fallback
- Hardcoded credentials or API keys in source

---

## Code Quality — Swift Checks

- Force unwrap (`!`) used broadly — prefer `guard let` or `if let`
- `try!` used outside of guaranteed-safe contexts
- Retain cycles in closures — missing `[weak self]` or `[unowned self]`
- `@objc` / `dynamic` used without an Objective-C interop reason

---

## Security

- Flag credentials stored in `UserDefaults` — require Keychain
- Flag `URLSession` requests over plain HTTP in production
- Flag `WKWebView` loading arbitrary user-supplied URLs without validation

---

## Async / Concurrency

- Flag `DispatchQueue.main.sync` called from the main thread — deadlock
- Flag `@escaping` closures capturing `self` strongly in reference cycles — use `[weak self]`
- Flag mixing `async/await` and `DispatchQueue` for the same operation without clear reasoning
- Flag `Task { }` (unstructured) where a structured `async let` or `TaskGroup` would maintain structure
- Flag data races — shared mutable state accessed from multiple tasks without an actor

---

## Resource Management

- Flag `URLSessionDataTask` started with no cancellation handle stored — cannot be cancelled if the view disappears
- Flag `NotificationCenter` observers added without a corresponding `removeObserver` — memory leak
- Flag `CLLocationManager` / `AVCaptureSession` not stopped when the owning view controller is dismissed

---

## Exception Handling

- Flag `try!` outside of guaranteed-safe contexts (test fixtures, constants) — crashes on failure
- Flag `try?` discarding errors where the failure mode matters to the caller
- Flag error types conforming to `Error` with no associated values or message — makes debugging hard
- Flag throwing functions calling `fatalError()` as a fallback — choose one error strategy

---

## Performance

- Flag `UIImage(named:)` called repeatedly for the same asset without caching
- Flag synchronous network calls on the main thread
- Flag `Array` used for frequent membership tests — prefer `Set`
- Flag `String` interpolation inside tight loops where a pre-built string would avoid allocations

---

## Idioms and Best Practices

### Optionals
- Prefer `guard let` for early exit; `if let` for local scope
- Prefer optional chaining (`?.`) over force unwrap
- Flag implicitly unwrapped optionals (`var x: String!`) outside of `@IBOutlet`

### Memory Management
- Flag closures capturing `self` strongly in reference cycles — use `[weak self]`
- Prefer `struct` over `class` for value semantics unless identity or inheritance is needed
- Use `unowned` only when the lifetime is guaranteed — otherwise `weak`

### Concurrency (Swift 5.5+)
- Prefer `async/await` over completion handlers in new code
- Flag `DispatchQueue.main.async` where `@MainActor` or `await MainActor.run` is more appropriate
