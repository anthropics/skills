---
language: csharp
extensions: [".cs", ".csx", ".razor", ".cshtml"]
---

# C# / .NET — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only C#-specific rules and idioms.

---

## PR Analyzer — C# Risk Signals

- `#pragma warning disable` and `[SuppressMessage]` — verify they are justified
- `unsafe { }` blocks — require explicit sign-off
- Null-forgiving operator (`!`) used broadly without justification
- `dynamic` used outside of interop scenarios
- Hardcoded connection strings in source files

---

## Code Quality — C# Checks

- `async void` methods (except event handlers)
- `Task` returned but not awaited
- `IDisposable` objects not in `using` / `using var`
- Bare `catch { }` or `catch (Exception e) { }` swallowing silently
- Nullable reference types feature disabled at project level

---

## Security

- Flag raw string interpolation in SQL queries — require parameterized queries (`SqlCommand`) or EF Core
- Flag missing `[ValidateAntiForgeryToken]` on state-changing controller actions
- Flag user-controlled data passed to `Process.Start()` or `File` APIs without validation
- Flag hardcoded connection strings — require `appsettings.json` + secrets management
- Flag `[AllowAnonymous]` on endpoints that should be protected

---

## Async / Await

- Flag `async void` methods outside of event handlers — cannot be awaited and swallow exceptions
- Flag `.Result`, `.Wait()`, or `.GetAwaiter().GetResult()` on `Task` — causes deadlocks in ASP.NET contexts
- Flag missing `ConfigureAwait(false)` in library (non-application) code
- Flag `Task.Run()` wrapping synchronous code inside ASP.NET request handlers unnecessarily
- Flag `CancellationToken` not threaded through to downstream async calls

---

## Resource Management

- Flag `IDisposable` objects (`SqlConnection`, `HttpClient`, `FileStream`, etc.) not wrapped in `using` / `using var`
- Flag `HttpClient` instantiated with `new` inside a method — use `IHttpClientFactory` or a shared static instance to avoid socket exhaustion
- Flag `DbContext` registered as a singleton in DI — it must be scoped
- Flag `MemoryStream` / `MemoryCache` growing unboundedly without eviction policy

---

## Exception Handling

- Flag `catch { }` or `catch (Exception) { }` with no logging or re-throw — silent swallow
- Flag `catch (Exception e) { throw e; }` — resets the stack trace; use `throw;` instead
- Flag catching `Exception` when a specific type (`IOException`, `HttpRequestException`) is appropriate
- Flag exception filters (`when`) used for side effects that suppress the exception
- Flag exceptions used for control flow in hot paths — use `Try*` pattern methods instead

---

## Performance

- Flag `.ToList()` / `.ToArray()` on `IQueryable` before filtering — forces all rows into memory; filter server-side first
- Flag `string` concatenation in loops — use `StringBuilder`
- Flag `Enumerable.Count()` on `IQueryable` when only an existence check is needed — use `Any()`
- Flag `await` in a loop where `Task.WhenAll()` would parallelize the work
- Flag synchronous file or network I/O in an `async` method — use the async overload

---

## Idioms and Best Practices

### Null Safety
- Ensure `<Nullable>enable</Nullable>` is set in the project file
- Flag excessive use of `!` (null-forgiving) without a comment explaining why
- Prefer `is null` / `is not null` over `== null` for null checks

### LINQ
- Flag `First()` where `FirstOrDefault()` is safer
- Flag complex LINQ chains that would be clearer as explicit loops

### Modern C# (10+)
- Prefer `record` types for immutable data carriers
- Prefer `switch` expressions over `switch` statements where a value is returned
- Prefer primary constructors (C# 12) for simple dependency injection
- Prefer file-scoped namespaces (`namespace Foo;`) over block-scoped
- Prefer `is` pattern matching over explicit casts
