---
language: php
extensions: [".php", ".phtml", ".php3", ".php4", ".php5", ".phps"]
---

# PHP — Language-Specific Review Notes

Load this file alongside `rules/universal.md`. Universal rules are not repeated here — only PHP-specific rules and idioms.

---

## PR Analyzer — PHP Risk Signals

- `var_dump` / `print_r` / `echo` debug statements left in production code
- `@` error suppression operator — masks real errors; verify it is justified
- `// phpcs:ignore` / `// phpstan-ignore` comments — verify they are justified
- Hardcoded credentials, database passwords, or API keys in source
- `eval()` anywhere — almost always a security issue
- `$_GET` / `$_POST` / `$_REQUEST` / `$_COOKIE` used without sanitization

---

## Code Quality — PHP Checks

- Missing type declarations on function parameters and return types
- `mixed` return type used broadly — tighten to specific types
- Global variables (`global $var`) — pass dependencies explicitly
- Long functions (>50 lines) — PHP functions tend to accumulate logic
- `isset()` / `empty()` used to mask type errors instead of fixing the root cause
- Missing `strict_types=1` declaration at the top of the file

---

## Security

- Flag `$_GET` / `$_POST` / `$_REQUEST` used directly in SQL queries — require PDO prepared statements
- Flag `mysqli_query($conn, "SELECT ... WHERE id = " . $_GET['id'])` — SQL injection
- Flag `echo $_GET['name']` or any unescaped output — XSS; use `htmlspecialchars()` with `ENT_QUOTES`
- Flag `include` / `require` with user-controlled paths — local/remote file inclusion
- Flag `eval()` — remote code execution risk; no legitimate use in application code
- Flag `shell_exec` / `exec` / `system` / `passthru` with user-controlled input — command injection
- Flag `unserialize()` on untrusted data — arbitrary object instantiation and code execution
- Flag `move_uploaded_file` without MIME type validation and extension whitelist — file upload attack
- Flag `header("Location: " . $_GET['url'])` without validation — open redirect
- Flag missing CSRF token validation on state-changing form endpoints

---

## Async / Concurrency

- Flag long-running synchronous operations in a request cycle — offload to a queue (Laravel Queue, RabbitMQ)
- Flag `sleep()` used inside a request handler — blocks the PHP-FPM worker
- Flag shared mutable state in `static` properties accessed across requests in long-running processes (Swoole, RoadRunner)
- Flag missing idempotency in queued jobs — jobs can be retried on failure

---

## Resource Management

- Flag database connections not closed or returned to the pool (`$pdo = null` or `$conn->close()`)
- Flag `fopen` / `fwrite` without a matching `fclose` on all paths
- Flag `curl_init` without `curl_close` — leaks the curl handle
- Flag unbounded file uploads with no size or type restriction
- Flag sessions not explicitly closed (`session_write_close()`) before long operations — session locking blocks other requests

---

## Exception Handling

- Flag empty `catch` blocks — swallowed exceptions
- Flag `catch (Exception $e) {}` without logging — silent failure
- Flag `die()` / `exit()` used for error handling in library code — use exceptions
- Flag `@` operator used to suppress errors from functions that can fail — check return values instead
- Flag `trigger_error` used in new code — prefer exceptions

---

## Performance

- Flag N+1 Eloquent / Doctrine queries — use eager loading (`with()`, `load()`, `join`)
- Flag `count($array)` called repeatedly in a loop condition — cache the result
- Flag `array_push($arr, $val)` — use `$arr[] = $val` which is faster
- Flag `in_array` on large arrays without the strict third argument — use `isset` on a flipped array for O(1) lookup
- Flag `file_get_contents` on remote URLs in a request cycle — use an HTTP client with timeout and async where possible
- Flag Eloquent `all()` without pagination — loads entire table into memory

---

## Idioms and Best Practices

### Type Safety
- Always declare `declare(strict_types=1)` at the top of every file
- Use union types (`int|string`) and nullable types (`?string`) rather than `mixed`
- Use typed properties on classes — avoid untyped `public $foo`
- Use constructor promotion for simple value objects

### Modern PHP (8.x)
- Prefer `match` expressions over `switch` — strict comparison, no fall-through
- Use named arguments for functions with many optional parameters
- Use `enum` for fixed sets of values instead of class constants
- Use `readonly` properties for immutable data
- Use nullsafe operator (`?->`) instead of nested `isset` checks
- Use `first-class callable syntax` (`strlen(...)`) instead of string references

### Laravel / Symfony Specific
- Keep controllers thin — logic belongs in service classes or action classes
- Use form requests for validation — never validate in the controller directly
- Prefer Eloquent relationships over manual joins for readability
- Flag raw queries where the ORM can express the same intent safely
