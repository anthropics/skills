---
language: dart
extensions: [".dart"]
---

# Dart / Flutter — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only Dart and Flutter-specific rules and idioms.

---

## PR Analyzer — Dart / Flutter Risk Signals

- `print()` statements left in production code — use a logging package
- `// ignore:` lint suppression comments — verify they are justified
- `!` null assertion operator used broadly without justification
- Hardcoded API keys, tokens, or URLs in Dart source — use environment variables or a secrets package
- `TODO` / `FIXME` near widget lifecycle or state management code

---

## Code Quality — Dart Checks

- `dynamic` used where a concrete type is known — defeats static analysis
- `!` (null assertion) used broadly — prefer null-safe patterns
- `StatefulWidget` used where `StatelessWidget` suffices — prefer stateless
- `setState` called with heavy computation inside — offload before calling
- `BuildContext` used across async gaps without checking `mounted`
- Missing `const` constructor on widgets that could be constant

---

## Security

- Flag API keys or secrets hardcoded in Dart source or `pubspec.yaml` — use `--dart-define` or a secrets manager
- Flag `http` package used without certificate validation disabled intentionally
- Flag `SharedPreferences` used to store sensitive data — use `flutter_secure_storage`
- Flag user-controlled input used in `dart:io` file path operations without sanitization
- Flag `WebView` loading arbitrary user-supplied URLs without validation
- Flag deep link / URL scheme handlers that don't validate the incoming URL before acting on it

---

## Async / Concurrency

- Flag `BuildContext` used after an `await` without checking `if (!mounted) return` — context may be invalid
- Flag `Future` returned but not `await`-ed and without `.catchError()` or `unawaited()` — floating future
- Flag `Isolate.spawn` without a clear message-passing protocol
- Flag heavy computation on the main isolate — offload with `compute()` or `Isolate.run()`
- Flag `StreamController` not closed when the owning widget is disposed — memory leak
- Flag `async*` / `yield*` generators with no error handling on the stream consumer side

---

## Resource Management

- Flag `StreamController` not closed in `dispose()`
- Flag `AnimationController` not disposed in `dispose()`
- Flag `TextEditingController` / `FocusNode` / `ScrollController` not disposed in `dispose()`
- Flag `Timer` not cancelled in `dispose()`
- Flag listeners added to `ChangeNotifier` / `ValueNotifier` without a corresponding `removeListener`

---

## Exception Handling

- Flag empty `catch` blocks — swallowed errors
- Flag `catchError` with no handler body — silent failure
- Flag `Future.error` not surfaced to the UI — show an error state
- Flag `FlutterError.onError` overridden without calling the original handler
- Prefer typed `on ExceptionType catch (e)` over generic `catch (e)` where the exception type is known

---

## Performance

- Flag `setState` called for changes that only affect a small subtree — use `ValueNotifier` / `provider` / `Riverpod` to scope rebuilds
- Flag expensive computation inside `build()` — move to `initState`, a controller, or a `FutureBuilder`
- Flag `ListView` without `ListView.builder` for long or infinite lists — builds all children at once
- Flag missing `const` on widgets that never change — prevents unnecessary rebuilds
- Flag `Image.network` without a caching package in a list — re-downloads on every scroll
- Flag `RepaintBoundary` missing around frequently-repainted widgets (animations, counters)

---

## Idioms and Best Practices

### Null Safety
- Prefer `?.` safe navigation and `??` null coalescing over `!` assertions
- Use `late` only when initialization is guaranteed before first access — document why
- Prefer early returns over deeply nested null checks

### Flutter Widget Patterns
- Prefer `StatelessWidget` + external state management over `StatefulWidget` for business logic
- Keep `build()` methods pure — no side effects, no heavy computation
- Extract repeated widget subtrees into named widget classes, not just methods, for better rebuild granularity
- Use `const` constructors wherever possible — compile-time constant widgets skip rebuilds entirely

### State Management
- Do not mix multiple state management approaches in the same feature
- Flag business logic inside `build()` — it belongs in a ViewModel, Notifier, or BLoC
- Prefer `Riverpod` / `provider` / `BLoC` over raw `setState` for anything beyond local UI state

### Modern Dart (3.x)
- Prefer `sealed` classes for exhaustive pattern matching on domain types
- Use records (`(int, String)`) for lightweight multi-value returns instead of ad hoc classes
- Use `switch` expressions with pattern matching instead of long `if/else` chains
- Prefer `final` for local variables — immutability by default
