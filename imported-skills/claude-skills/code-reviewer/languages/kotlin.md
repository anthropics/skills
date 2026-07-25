---
language: kotlin
extensions: [".kt", ".kts"]
---

# Kotlin — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only Kotlin-specific rules and idioms.

---

## PR Analyzer — Kotlin Risk Signals

- `println()` statements left in production code
- `@Suppress` annotations — verify they are justified
- `!!` (not-null assertion) used broadly without justification
- Hardcoded credentials or API keys in source

---

## Code Quality — Kotlin Checks

- `!!` used broadly — prefer `?.let`, `?:`, or `requireNotNull()`
- `lateinit var` accessed before initialization
- Coroutines launched with `GlobalScope` — prefer scoped coroutines
- `runBlocking` used outside of tests or top-level entry points

---

## Security

- Flag Room / SQLite queries built with string concatenation — require parameterized queries
- Flag `WebView.loadUrl()` with user-controlled input without validation
- Flag credentials stored in `SharedPreferences` — require `EncryptedSharedPreferences` or Keychain

---

## Async / Coroutines

- Flag `GlobalScope.launch` / `GlobalScope.async` in production code — use a structured scope
- Flag `runBlocking` outside of tests or top-level main functions
- Flag `launch` / `async` without a `CoroutineExceptionHandler` or `supervisorScope` where individual failures should not cancel siblings
- Flag `Dispatchers.Main` used for CPU-bound work — use `Dispatchers.Default`
- Flag coroutine cancellation not respected — long loops should check `isActive` or call `yield()`

---

## Resource Management

- Flag `Closeable` / `AutoCloseable` not wrapped in `.use { }` (Kotlin's try-with-resources equivalent)
- Flag `OkHttpClient` / `Retrofit` instantiated per-request — share a singleton
- Flag `BroadcastReceiver` registered without a corresponding `unregisterReceiver` — memory / battery leak
- Flag coroutines that hold a resource across a `suspend` point without structured cleanup in `finally`

---

## Exception Handling

- Flag `runCatching { }.getOrNull()` used broadly — silently swallows all exceptions
- Flag `catch (e: Exception)` in coroutines without re-throwing `CancellationException` — breaks structured concurrency
- Flag empty `catch` blocks
- Flag `throw RuntimeException(e)` without a descriptive message
- Prefer typed `sealed class` error hierarchies over raw exceptions for domain errors in coroutine flows

---

## Performance

- Flag `buildString` / `StringBuilder` not used for multi-step string construction in loops
- Flag `List` used for frequent `contains` checks — prefer `Set`
- Flag `flow.collect {}` re-subscribing on every recomposition in Jetpack Compose — use `collectAsStateWithLifecycle`
- Flag `Dispatchers.IO` used for CPU-bound work — use `Dispatchers.Default`
- Flag `suspend` functions calling non-suspend blocking APIs directly — wrap with `withContext(Dispatchers.IO)`

---

## Idioms and Best Practices

### Null Safety
- Prefer safe call (`?.`) and Elvis operator (`?:`) over `!!`
- Use `requireNotNull()` / `checkNotNull()` with a descriptive message when null means a programming error
- Prefer `val` over `var` — immutability by default

### Modern Kotlin
- Prefer `data class` for value carriers
- Prefer `sealed class` / `sealed interface` for exhaustive `when` expressions
- Prefer extension functions over utility classes
- Prefer `object` declarations for singletons
