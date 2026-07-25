---
language: java
extensions: [".java"]
---

# Java — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only Java-specific rules and idioms.

---

## PR Analyzer — Java Risk Signals

- `System.out.println` / `e.printStackTrace()` left in production code
- `@SuppressWarnings` annotations — verify they are justified
- Hardcoded JDBC URLs or credentials in source
- Raw type usage (`List`, `Map` without generics)

---

## Code Quality — Java Checks

- Empty `catch` blocks swallowing exceptions silently
- Checked exceptions caught and not re-thrown with context
- `Closeable` / `AutoCloseable` resources not in try-with-resources
- Raw type usage — defeats generics type safety
- Missing `@Override` on overriding methods
- `InterruptedException` caught without calling `Thread.currentThread().interrupt()`

---

## Security

- Flag JPQL / HQL or native SQL string concatenation — require named parameters or `CriteriaBuilder`
- Flag `@RequestMapping` without explicit HTTP method restriction on state-changing endpoints
- Flag user-controlled input passed to `Runtime.exec()` or `ProcessBuilder` without validation
- Flag `ObjectInputStream.readObject()` on untrusted data — unsafe deserialization
- Flag hardcoded JDBC URLs or credentials — require environment variables or a vault

---

## Async / Concurrency

- Flag `ExecutorService.submit()` return value ignored — exceptions are swallowed
- Flag `Thread.sleep()` used as a synchronization mechanism — use `CountDownLatch`, `CompletableFuture`, or `await()`
- Flag `CompletableFuture` chains with no `.exceptionally()` or `.handle()` terminal handler
- Flag `InterruptedException` caught without calling `Thread.currentThread().interrupt()`
- Flag `synchronized` on a non-final field — the lock object can be replaced
- Flag `HashMap` used in multi-threaded context — use `ConcurrentHashMap`

---

## Resource Management

- Flag `InputStream`, `OutputStream`, `Connection`, `ResultSet`, `PreparedStatement` not wrapped in try-with-resources
- Flag manual `finally { resource.close() }` — replace with try-with-resources
- Flag `HttpURLConnection` not disconnected after use
- Flag JDBC `Connection` obtained from a pool and not returned (missing `close()`) on all paths
- Flag `static` `HttpClient` or `Connection` fields shared across threads without connection pool management

---

## Exception Handling

- Flag empty `catch` blocks — `catch (Exception e) {}`
- Flag `InterruptedException` caught without `Thread.currentThread().interrupt()` — breaks cooperative cancellation
- Flag checked exceptions swallowed in a `catch` and not re-thrown or logged with context
- Flag `throw new RuntimeException(e)` without a descriptive message — loses context
- Flag `printStackTrace()` as the sole error handling — use a proper logger

---

## Performance

- Flag `String` concatenation in loops — use `StringBuilder`
- Flag `List.contains()` / `Map.get()` in a loop on large collections — review data structure choice
- Flag N+1 JPA / Hibernate queries — use `JOIN FETCH` or `@BatchSize`
- Flag `new ObjectMapper()` / `new Gson()` instantiated per-request — share a singleton
- Flag `ResultSet` fully iterated when only the first result is needed — use `LIMIT 1` in the query

---

## Idioms and Best Practices

### Null Safety
- Prefer returning `Optional<T>` over `null` from methods
- Flag unchecked dereferences without a prior null guard
- Do not catch `NullPointerException` — fix the root cause instead

### Collections and Streams
- Flag `==` used to compare `String` or boxed types — use `.equals()`
- Flag `.collect(Collectors.toList())` where `.toList()` (Java 16+) suffices
- Flag premature `.stream().collect()` round-trips that could be a single-pass operation

### Generics
- Flag raw types in any new code — always parameterize (`List<String>`, not `List`)
- Flag unchecked cast warnings suppressed without explanation

### Modern Java (11+)
- Prefer `var` for local variables where the type is obvious from the right-hand side
- Prefer records for pure data carriers over manual POJOs with getters/setters
- Prefer `instanceof` pattern matching (`if (obj instanceof String s)`) over explicit casts
- Prefer `switch` expressions over `switch` statements where a value is returned
