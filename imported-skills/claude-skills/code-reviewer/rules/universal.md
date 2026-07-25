# Universal Rules — All Languages

These rules apply regardless of language. Load this file for every review, alongside the relevant `languages/*.md` file.

---

## Security

- Flag any string interpolation or concatenation used to build SQL, shell, or LDAP queries — require parameterized queries or a safe API
- Flag hardcoded credentials, API keys, tokens, or secrets anywhere in source — require environment variables or a secrets manager
- Flag user-controlled input passed to file system, process execution, or URL redirect APIs without validation
- Flag overly broad CORS or CSP policies

---

## Async / Concurrency

- Flag shared mutable state accessed from multiple threads/coroutines/tasks without synchronization
- Flag fire-and-forget async operations with no error handling path
- Flag timeouts missing on any network or I/O call
- Flag unbounded queues or thread pools with no backpressure mechanism

---

## Resource Management

- Flag any resource (file, socket, DB connection, HTTP connection) acquired without a guaranteed release path
- Flag connection pools not returned to the pool on all code paths (including exceptions)
- Flag unbounded collections that grow without eviction — potential memory leak
- Flag resources held open longer than the operation they serve

---

## Exception Handling

- Flag empty catch/except blocks — swallowed exceptions hide bugs silently
- Flag catching the broadest possible exception type (`Exception`, `Throwable`, `error`) where a specific type is appropriate
- Flag exceptions used for normal control flow (signaling "not found", etc.) — use return values or `Optional`
- Flag error context lost when re-throwing — always wrap with the original cause

---

## Performance

- Flag N+1 query patterns — loading a collection then querying for each item individually
- Flag unbounded queries or API calls with no pagination or limit
- Flag synchronous I/O on a thread or event loop that serves concurrent requests
- Flag large objects serialized/deserialized repeatedly when they could be cached
- Flag string concatenation in tight loops — use a builder or join
