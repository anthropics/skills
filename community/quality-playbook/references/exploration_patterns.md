# Exploration Patterns for Bug Discovery

This reference defines the exploration patterns that Phase 1 applies during codebase exploration. These patterns target bug classes most commonly missed when exploration stays at the subsystem or architecture level.

Requirements problems are the most expensive to fix because they are not caught until after implementation. The exploration phase is requirements elicitation — it determines what the code review and spec audit will look for. A requirement that is never derived is a bug that is never found. These patterns exist to systematically surface requirements that broad exploration misses.

Each pattern includes a definition, the bug class it targets, diverse examples from different domains, and the expected output format for EXPLORATION.md.

**Important: These patterns supplement free exploration — they do not replace it.** Phase 1 begins with open-ended exploration driven by domain knowledge and codebase understanding. After that open exploration, apply the patterns below as a structured second pass to catch specific bug classes. If you find yourself only looking for things the patterns describe, you are using them wrong. The patterns are a checklist to run after you have already formed your own understanding of the codebase's risks.

---

## Pattern 1: Fallback and Degradation Path Parity

### Definition

When code provides multiple strategies for accomplishing the same goal — a primary path and one or more fallback paths — each fallback must preserve the same behavioral invariants as the primary. The fallback may use a different mechanism, but the observable contract must be equivalent.

### Bug class

Fallback paths are written later, tested less, and reviewed with less scrutiny than primary paths. They often omit steps the primary path performs (validation, cleanup, index assignment, resource release) because the developer copied the primary path and simplified it for the "degraded" case. The result is a function that works correctly in the common case but violates its contract when the fallback activates.

### Examples across domains

- **Authentication:** A web service tries OAuth token validation, falls back to API key lookup, falls back to session cookie. Each fallback must enforce the same authorization scope. Bug: the API key fallback skips scope validation and grants full access.
- **Connection pooling:** A database client tries the primary connection pool, falls back to a secondary pool, falls back to creating a one-off connection. Each path must apply the same timeout and transaction isolation settings. Bug: the one-off connection fallback uses the driver default isolation level instead of the configured one.
- **Resource allocation:** A memory allocator tries a fast slab path, falls back to a slow page-level path. Both must zero-initialize sensitive fields. Bug: the slow path returns uninitialized memory because zero-fill was only in the slab fast path.
- **HTTP redirect handling:** A client follows a redirect and must strip security-sensitive headers (Authorization, Proxy-Authorization, cookies) when the redirect crosses an origin boundary. Bug: the redirect path strips Authorization but not Proxy-Authorization, leaking proxy credentials to the redirected origin.
- **Serialization fallback:** A message broker tries binary serialization, falls back to JSON, falls back to string encoding. Each path must preserve the same field ordering and null-handling semantics. Bug: the JSON fallback silently drops null fields that binary serialization preserves.

### How to apply

For each core module, look for: conditional chains that try one approach then fall through to another, strategy/adapter patterns where multiple implementations are selected at runtime, retry logic with different strategies per attempt, feature-negotiation cascades where capabilities determine which code path runs, HTTP redirect/retry logic that must preserve or strip headers.

For each cascade found:
1. List the primary path and every fallback.
2. For each fallback, check whether it performs the same critical operations as the primary (validation, resource setup, index assignment, cleanup, error reporting, header stripping, resource release).
3. Any operation present in the primary but missing in a fallback is a candidate requirement.

### EXPLORATION.md output format

```
## Fallback Path Analysis

### [Name of cascade]
- **Primary path:** [function, file:line] — [what it does]
- **Fallback 1:** [function, file:line] — [what it does, what differs]
- **Fallback 2:** [function, file:line] — [what it does, what differs]
- **Parity gaps:** [specific operations present in primary but missing in fallback]
- **Candidate requirements:** REQ-NNN: [fallback must do X]
```

---

## Pattern 2: Dispatcher Return-Value Correctness

### Definition

When a function dispatches on input type or condition and must return a status value, the return value must be correct for every combination of inputs — not just the primary case. Dispatchers that handle multiple event types, request types, or state transitions are particularly prone to return-value bugs in edge combinations.

### Bug class

Dispatchers are typically written and tested for the common case. The return value is correct when the primary event fires. But when an unusual combination occurs (only a secondary event, no events at all, multiple concurrent events), the return-value logic may be wrong — returning "not handled" for a handled event, returning success for a partial failure, or returning a stale value from a previous iteration.

### Examples across domains

- **HTTP middleware:** A request dispatcher checks for authentication, rate-limiting, and routing. When rate-limiting triggers but authentication was already set, the dispatcher returns the auth status code instead of the rate-limit status code. Bug: rate-limited requests get 401 instead of 429.
- **CORS handler chain:** A CORS preflight handler sets 400 (rejected), then the missing-OPTIONS-handler path sets 404, then an AFTER handler normalizes 404→200 (meant for allowed origins). Bug: rejected preflights get 200 because the status was overwritten by downstream handlers.
- **Event loop:** A poll/select loop handles read-ready, write-ready, and error conditions. When only an error condition fires on a socket with no pending reads, the loop returns "no events" because the read-ready check was false. Bug: connection errors are silently ignored.
- **State machine transition:** A state machine dispatch function handles valid transitions, invalid transitions, and no-op transitions. When a no-op transition occurs (current state == target state), the function returns an error code intended for invalid transitions. Bug: idempotent operations fail when they should succeed.
- **Interrupt handler:** A hardware interrupt handler checks for multiple event types (data-ready, configuration-change, error). When only a secondary event fires (e.g., config change with no data), the handler returns "not mine" because the primary event check failed and the secondary path doesn't set the handled flag. Bug: legitimate secondary events are reported as spurious.

### How to apply

For each core module, look for: functions with switch/case or if-else chains that return a status, interrupt/event handlers that handle multiple event types, request dispatchers that check multiple conditions before returning, state machine transition functions, middleware chains where multiple handlers write to the same response status.

For each dispatcher found:
1. Enumerate all input combinations (not just the ones with explicit case labels — also the implicit "else" and "default" paths).
2. For each combination, trace the return value through the entire handler chain (not just the immediate function).
3. Any combination where the return value doesn't match the expected semantics is a candidate requirement.

### EXPLORATION.md output format

```
## Dispatcher Return-Value Analysis

### [Function name] at [file:line]
- **Input types:** [list of conditions/events the function dispatches on]
- **Combinations checked:**
  - [Condition A only]: returns [X] — correct/incorrect because [reason]
  - [Condition B only]: returns [X] — correct/incorrect because [reason]
  - [Both A and B]: returns [X] — correct/incorrect because [reason]
  - [Neither A nor B]: returns [X] — correct/incorrect because [reason]
- **Candidate requirements:** REQ-NNN: [function must return Y when only B fires]
```

---

## Pattern 3: Cross-Implementation Contract Consistency

### Definition

When multiple functions implement the same logical operation for different contexts (different transports, different backends, different protocol versions), they should all satisfy the same specification requirement. A step that is mandatory in the specification must appear in every implementation — a missing step in one implementation that is present in another is a strong bug signal.

### Bug class

When the same operation is implemented in multiple places, each implementation is typically written by a different developer or at a different time. The specification says "reset must wait for completion," and the developer of implementation A writes the wait loop, but the developer of implementation B writes only the reset trigger and forgets the wait. The bug is invisible when testing implementation B in isolation because it "works" on fast hardware — the race condition only manifests under load or on slow devices.

### Examples across domains

- **Device reset:** A spec says "the driver must write zero and then poll until the status register reads back zero." The PCI implementation includes the poll loop. The MMIO implementation writes zero but does not poll. Bug: MMIO reset can race with reinitialization.
- **Database driver:** A connection-close spec says "the driver must send a termination message, wait for acknowledgment, then release the socket." The PostgreSQL driver does all three. The MySQL driver sends the termination message and releases the socket without waiting for acknowledgment. Bug: the server may process the termination after the socket is reused.
- **HTTP header encoding:** A Headers class constructor decodes raw bytes as Latin-1 per RFC 7230. The mutation method (`__setitem__`) encodes values as UTF-8. Bug: round-tripping a Latin-1 header through get-then-set corrupts the value because the encoding changed.
- **Cache invalidation:** A cache spec says "invalidation must remove the entry and notify all subscribers." The in-memory cache does both. The distributed cache removes the entry but does not broadcast the notification. Bug: other nodes serve stale data.
- **File locking:** A storage spec says "lock acquisition must set a timeout and clean up on failure." The local filesystem implementation sets the timeout. The NFS implementation uses blocking lock with no timeout. Bug: NFS lock contention can hang the process indefinitely.

### How to apply

For each core module, look for: the same operation name implemented in multiple files or classes, interface/trait implementations across different backends, protocol-version-specific implementations of the same message, transport-specific implementations of the same lifecycle operation, constructor vs. mutation implementations of the same logical operation.

For each pair (or set) of implementations:
1. Identify the specification requirement they share.
2. List the mandatory steps from the spec.
3. Check each implementation for each step.
4. Any step present in one but missing in another is a candidate requirement.

**Check every cross-transport operation, not just the most obvious one.** If a codebase has multiple transports (PCI, MMIO, vDPA) or backends (PostgreSQL, MySQL), enumerate all operations that have cross-implementation equivalents — reset, interrupt handling, feature negotiation, queue setup, configuration access — and check each one. The first cross-implementation gap you find is rarely the only one. A common failure mode is analyzing reset thoroughly and then skipping interrupt dispatch, which has the same cross-transport structure.

### EXPLORATION.md output format

```
## Cross-Implementation Consistency

### [Operation name] — [spec reference]
- **Implementation A:** [function, file:line] — performs steps: [1, 2, 3]
- **Implementation B:** [function, file:line] — performs steps: [1, 3] (missing step 2)
- **Gap:** [Implementation B missing step 2: description]
- **Candidate requirements:** REQ-NNN: [all implementations of X must perform step 2]
```

---

## Pattern 4: Enumeration and Representation Completeness

### Definition

When a codebase maintains a closed set of recognized values — a switch/case whitelist, an array of valid constants, an enum/tagged-union definition, a trait/visitor method family, a set of schema keywords, a registry of accepted entries — every value that the specification, upstream definition, or the library's own public API surface says should be accepted must appear in the set. Values not in the set are silently dropped, rejected, or mishandled, and the absence of an entry is invisible at the call site.

### Bug class

Closed sets are written once and rarely revisited. When a new capability is added to the specification or upstream header, the code that defines the capability (the constant, the feature flag, the enum variant) is updated, and the code that uses the capability is updated, but the closed set that gates whether the capability survives a filtering step is forgotten. The feature appears to be supported — it's defined, it's negotiated, it's used — but it's silently stripped by a filter function that nobody remembered to update. The bug is invisible in normal testing because the feature simply doesn't activate, and the absence of activation looks like "the other end doesn't support it."

This pattern also covers **internal representations** that must mirror a public API. If a library's public API accepts i128/u128 integers but an internal buffered representation only has variants for i64/u64, values that pass through the buffer are silently truncated or rejected — even though the public API promises to handle them.

### Examples across domains

- **Feature negotiation filter:** A transport layer maintains a switch/case whitelist of feature bits that should survive filtering. A new feature (`RING_RESET`) is added to the UAPI header and used by higher-level code, but never added to the whitelist. Bug: the feature is silently cleared during negotiation, disabling a capability the driver claims to support.
- **Serialization internal representation:** A serialization library's public `Deserializer` trait supports `deserialize_i128()`/`deserialize_u128()`. An internal buffered representation (`Content` enum) used by untagged and internally-tagged enum deserialization has variants only for `I64`/`U64`. Bug: 128-bit integers that pass through the buffer are rejected with a "no variant for i128" error, even though the public API claims to support them.
- **Schema keyword importer:** A validation library imports JSON Schema documents. The spec defines `uniqueItems`, `contains`, `minContains`, `maxContains` for arrays. The importer recognizes these keywords (no parse error) but doesn't enforce them. Bug: imported schemas silently accept arrays that violate the original constraints.
- **Permission system:** An authorization middleware maintains an array of recognized permission strings. A new permission (`audit:write`) is added to the role definitions but not to the middleware's whitelist. Bug: users with the `audit:write` role are silently denied access because the middleware doesn't recognize the permission.
- **Protocol message types:** A message router maintains a switch/case dispatch for recognized message types. A new message type is added to the protocol spec and the serialization layer, but not to the router. Bug: the new message type is silently dropped by the router's default case, and the sender receives no error.

### How to apply

For each core module, look for: switch/case statements with explicit case labels and a default that drops/clears/rejects, arrays or sets of accepted values used for filtering or validation, registration functions where new entries must be added manually, enum/tagged-union definitions that mirror a specification or public API, trait/visitor method families where each method handles one variant, schema importers that must handle every keyword the spec defines, internal representations (buffers, IR, AST) that must cover the full range of the public interface.

For each closed set found:
1. Identify the authoritative source that defines what values should be valid. This could be: a spec, a header file, an upstream enum, a protocol definition, **or the library's own public API surface** (trait methods, function signatures, type definitions).
2. Extract the closed set mechanically (save the case labels, enum variants, visitor methods, array entries, or schema keywords to a file).
3. Compare the extracted set against the authoritative source. Every value in the authoritative source that is absent from the closed set is a candidate requirement.

**Caller compensation does not excuse a missing entry.** If a closed set in a shared/generic function is missing an entry, that is a bug — even if specific callers compensate by restoring the value after the function runs. The compensation is a workaround, not a fix. Any new caller that doesn't know to compensate silently inherits the bug. Report each missing entry as a finding and note which callers (if any) compensate, but do not dismiss the finding because of compensation.

### EXPLORATION.md output format

```
## Enumeration/Representation Completeness

### [Function/type name] at [file:line]
- **Purpose:** [what this closed set gates — e.g., "feature bits that survive transport filtering" or "integer variants the buffer can hold"]
- **Authoritative source:** [where valid values are defined — e.g., "include/uapi/linux/virtio_config.h" or "public Deserializer trait methods"]
- **Extracted entries:** [list of values in the closed set, or reference to mechanical extraction file]
- **Missing entries:** [values present in the authoritative source but absent from the closed set]
- **Candidate requirements:** REQ-NNN: [closed set must include X]
```

---

## Pattern 5: API Surface Consistency

### Definition

When the same logical operation can be performed through multiple API surfaces — direct method vs. view/wrapper, constructor vs. mutator, sync vs. async variant, primary API vs. convenience alias — all surfaces must produce equivalent observable behavior for the same input. A divergence between two paths to the same operation is a bug, because callers reasonably expect consistent behavior regardless of which surface they use.

### Bug class

Libraries often expose the same underlying data through multiple interfaces: a direct method and a collection view (`add()` vs. `asList().add()`), a constructor and a setter, a sync and async variant. These surfaces are implemented at different times, often by different developers, and their edge-case handling diverges — especially around null/sentinel values, encoding, ordering, and error reporting. The divergence is invisible in normal testing because tests typically exercise only one surface per operation.

### Examples across domains

- **JSON null handling:** `JsonArray.add(null)` converts null to `JsonNull.INSTANCE` and succeeds. `JsonArray.asList().add(null)` throws `NullPointerException` because the view's wrapper unconditionally rejects null. Bug: two methods for the same operation have contradictory null semantics.
- **HTTP header encoding:** `Headers([(b"X-Custom", b"\xe9")])` constructs a header from Latin-1 bytes. `headers["X-Custom"] = b"\xe9"` stores the value as UTF-8. Bug: round-tripping a header through get-then-set changes the encoding silently.
- **WebSocket protocol negotiation:** `WebSocketUpgrade::protocols()` returns a `BTreeSet<HeaderValue>`, which sorts and deduplicates the client's preference-ordered protocol list. Bug: the application sees a different order than the client sent, breaking preference-based negotiation.
- **Configuration option propagation:** `res.sendFile(path, { etag: false })` should disable ETag for this response. But the code converts the option to a boolean before passing to the underlying `send` module, losing the "strong" vs "weak" ETag mode. Bug: per-call ETag configuration is silently ignored or lossy-converted.
- **Map duplicate detection:** `map.put(key, value)` returns the previous value to signal duplicates. When the previous value is legitimately `null`, `put()` returns `null` — the same value it returns for "no previous entry." Bug: duplicate keys go undetected when the first value is null.

### How to apply

For each core module, look for: view/wrapper objects returned by methods like `asList()`, `asMap()`, `unmodifiableView()`, `stream()`, `iterator()`; constructor vs. mutation method pairs; sync vs. async variants of the same operation; convenience aliases that delegate to a primary implementation; methods that accept options/configuration objects.

For each pair of surfaces:
1. Identify the logical operation they share.
2. Test the same edge-case inputs on both surfaces (null, empty, boundary values, special characters, ordering-sensitive data).
3. Any divergence in behavior (different exceptions, different encoding, different ordering, one succeeds and the other fails) is a candidate requirement.

### EXPLORATION.md output format

```
## API Surface Consistency

### [Operation name] — [two surfaces compared]
- **Surface A:** [method, file:line] — [behavior on edge input]
- **Surface B:** [method, file:line] — [behavior on same edge input]
- **Divergence:** [what differs — exception type, encoding, ordering, null handling]
- **Candidate requirements:** REQ-NNN: [both surfaces must behave equivalently for input X]
```

---

## Pattern 6: Spec-Structured Parsing Fidelity

### Definition

When code parses values defined by a formal grammar or specification — HTTP headers, URLs, MIME types, CLI flags, JSON Schema keywords, file paths — the parsing must match the grammar's actual rules. Shortcuts (substring matching, exact equality, wrong delimiter, prefix matching without boundary checks) produce parsers that work for common inputs but fail on valid edge cases or accept invalid inputs.

### Bug class

Developers frequently implement "good enough" parsers that handle the common case: `header.contains("gzip")` instead of tokenizing by comma and trimming whitespace, `url.startsWith("/api")` instead of checking path segment boundaries, `connection == "Upgrade"` instead of case-insensitive token list membership. These shortcuts pass all unit tests because tests use well-formed inputs, but they break on real-world edge cases like `gzip;q=0` (explicitly rejected), `Connection: keep-alive, Upgrade` (token list), or `/api-docs` (prefix match without boundary).

### Examples across domains

- **HTTP Accept-Encoding:** Middleware checks `accept.contains("gzip")` to decide whether to compress. This matches `gzip;q=0` (client explicitly rejects gzip) and `xgzip` (not a valid encoding). Bug: responses are compressed when the client said not to.
- **WebSocket Connection header:** Code checks `connection == "Upgrade"` (exact match). Per RFC 7230, `Connection` is a comma-separated token list; `Connection: keep-alive, Upgrade` is valid but fails exact match. Bug: valid WebSocket upgrades are rejected.
- **SPA fallback routing:** A single-page-app handler matches paths with `path.startsWith("/app")`. This matches both `/app/users` (correct) and `/api-docs` (incorrect sibling route). Bug: API documentation requests are swallowed by the SPA handler.
- **MIME type parameter handling:** Content negotiation compares `text/html;level=1` against handler keys but strips parameters before matching. Bug: the `level=1` parameter selected during negotiation is lost from the response Content-Type.
- **URL host normalization:** Code detects internationalized domain names by checking `host.startsWith("xn--")`. Per IDNA, only individual labels start with `xn--`; `foo.xn--example.com` has the punycode label in the middle. Bug: internationalized subdomains are not decoded.

### How to apply

For each core module, look for: string comparisons on values defined by RFCs or specs (headers, URLs, MIME types, encoding names), `contains()` / `indexOf()` / `startsWith()` / `endsWith()` on structured values, case-sensitive comparisons where the spec requires case-insensitive, splitting on the wrong delimiter or not splitting at all, prefix/suffix matching without path-segment or token boundaries.

For each parser found:
1. Identify the spec that defines the grammar (RFC, ABNF, JSON Schema spec, POSIX, etc.).
2. Check whether the implementation handles: token lists (comma-separated), quoted strings, parameters (semicolon-separated), case folding, whitespace trimming, boundary conditions.
3. Construct an input that is valid per the spec but would fail the implementation's shortcut parser. That input is a candidate test case and the parsing gap is a candidate requirement.

### EXPLORATION.md output format

```
## Spec-Structured Parsing

### [Parser location] at [file:line]
- **Spec:** [which grammar/RFC/standard defines the format]
- **Implementation technique:** [contains/equals/startsWith/split-on-X]
- **Spec-valid input that breaks the parser:** [concrete example]
- **Why it breaks:** [substring match includes invalid case / missing case folding / etc.]
- **Candidate requirements:** REQ-NNN: [parser must tokenize per RFC NNNN §N.N]
```

---

## Pattern 7: Composition and Mount-Context Awareness

### Definition

When code operates inside a composed context — mounted at a sub-route, nested inside a parent module, scoped to a child container, wrapped by a framework adapter — the framework typically maintains a *canonical* representation of the active state (what the active context says is true right now) alongside the *raw* representation from the outer call site (what the outer caller passed in originally). Code that reads or writes the raw representation when canonical was needed (or vice versa) works correctly at the outer level, where they happen to be identical, but fails silently under composition, where they diverge.

### Bug class

Code is written and tested at the outer level — top-level routes, root module, single-tenant deployment, default scope — where canonical and raw state are identical. When the same code runs inside a composed context, the framework updates the canonical state (mounted child path, scoped logger, transaction-scoped connection, locale-aware comparator) but the raw state still reflects the outer call. The defect manifests in two symmetric directions: a function that *reads* raw state where canonical was needed sees stale data and produces silent drift (never matches, leaks parent context, returns the wrong output); a function that *writes* an outward-facing value from canonical state where raw is needed produces output the consumer can't use (drops the mount prefix, returns a child-relative path the parent's clients can't follow). Either way, the test suite typically exercises the outer level only and never sees the divergence.

### Examples across domains

- **HTTP routing middleware (mount-context):** A middleware comparing the request path against a configured endpoint reads `r.URL.Path`. When mounted at a sub-route, the framework's canonical "active routing path" (e.g., `RoutePath` in chi, `req.url` in Express sub-app) is the child-relative path while `r.URL.Path` remains the full URL path. Bug: middleware never matches inside the mounted child because it reads the wrong path representation.
- **Database transaction context:** A repository method opens its own connection via the connection pool. When called inside an explicit transaction, the framework's canonical "current transaction" context is the explicit one, but the method reads from the connection pool directly. Bug: the method's writes don't participate in the surrounding transaction; rollback leaves orphan rows.
- **Logging context propagation:** A library logs via `logging.getLogger(__name__)`. When invoked inside an async task or worker pool that has scoped a contextvar-based correlation ID, the logger doesn't read the contextvar. Bug: the library's log lines lack the correlation ID the framework was propagating, breaking traceability.
- **Locale-sensitive comparison:** A sort function uses `str.lower()` for case-insensitive comparison. When called inside a locale-aware context (Turkish "i" / "İ" / "ı" semantics), the framework's canonical locale is set but `str.lower()` reads the default locale. Bug: equality comparisons silently differ depending on which locale is canonically active.
- **Authorization scope inheritance:** An ACL check reads `request.user` (the raw authenticated principal). When invoked inside an impersonation context, the framework's canonical `request.effective_user` is the impersonated principal but the check still reads the original. Bug: privilege escalation — the check authorizes the wrong principal.

### How to apply

Identify every function or component that reads or writes state that *can be canonical-vs-raw under composition*. The check is: does this code path run unchanged when its caller is composed inside a larger context, and if so, does the state it observes (or produces) change accordingly?

**Disambiguation from Pattern 4.** Pattern 4 (Enumeration and Representation Completeness) is about closed sets of values: the bug is "value missing from the recognizer's closed set." Pattern 7 is about choice of state variable: the bug is "function reads or writes the wrong representation of state under composition." If both frames seem to apply, prefer the one whose REQ is more testable. The two patterns rarely overlap on the same defect; when they do, the canonical-vs-raw framing usually points more directly at the fix.

**Budget.** Cap candidates at 3-5 highest-impact composition seams per pass. If more than 10 candidates emerge from this pattern alone, the net is too wide and the pattern is being over-applied — revisit Step 1 with a tighter "what does this framework actually maintain canonically under composition" filter.

For each candidate found:

1. **Identify the canonical and raw representations, both for reads and writes.** What does the framework maintain as "the active state for this concern" under composition? What does the function actually read? Then ask the symmetric question for outputs: when this function constructs a value that flows outward (a redirect target, a derived path, a logged correlation ID, an authorized resource handle), is that value being built from the right representation for its consumer? Read-side and write-side defects are equally common; check both directions.
2. **Trace the composition seam.** Where does the framework update canonical state? Is the function downstream of that update site? Does it read from the canonical or the raw representation?
3. **Construct the composition test.** What is the smallest example where this code runs inside a composed parent (mounted router, nested transaction, scoped logger, impersonation context)? Does the function's behavior match the outer-level behavior, or does it silently drift?
4. **Record what happens.** A function that drifts under composition is a candidate requirement: "function `<X>` MUST read `<canonical_state>` (not `<raw_state>`) [or write `<raw_state>` for outward-facing output] so that behavior remains correct when composed inside `<parent_context>`."

Common composition seams worth checking explicitly:

- **Routing frameworks:** `RoutePath` / `req.url` / `request.path_info` versus the original URL. Each level of mounting updates the canonical path; raw URLs do not.
- **Transaction managers:** explicit transaction context versus connection pool's auto-commit default. Composed code must read the active transaction.
- **Logging / tracing:** contextvar-scoped correlation IDs versus thread-local or default loggers. Composed code must read the contextvar.
- **Authorization / impersonation:** effective principal versus raw user. Composed code must read the effective principal.

### EXPLORATION.md output format

```
## Composition and Mount-Context Analysis

### [Function/component name] at [file:line]
- **Composes inside:** [parent context — e.g., "any chi router that calls Mount() to attach this middleware"]
- **Canonical representation:** [what the framework maintains under composition — e.g., "rctx.RoutePath, the active mounted path"]
- **Raw representation read by this code:** [what the function actually reads — e.g., "r.URL.Path, the full request URL"]
- **Drift scenario:** [smallest composition example that exposes the divergence — e.g., "router.Mount("/api", child) where child uses this middleware to serve /ping"]
- **Observable failure:** [what wrong behavior results — e.g., "404 instead of the expected response"]
- **Candidate requirements:** REQ-NNN: [function MUST read canonical state under composition]
```

---

## Extending This List

These patterns were derived from analyzing 56 confirmed bugs across 11 open-source repositories spanning 7 languages. Each pattern represents a class of requirements that broad architectural summaries consistently miss.

To add a new pattern:
1. Identify a confirmed bug that was missed by exploration but would have been found with a specific analysis technique.
2. Generalize the technique: what question should the explorer have asked about the code?
3. Provide at least 5 diverse examples from different domains (not all from the same project).
4. Define the expected output format for EXPLORATION.md.
5. Add the pattern to this file and add the corresponding section to the EXPLORATION.md template in SKILL.md.

The goal is a library of systematic exploration techniques that accumulate over time as new bug classes are discovered.
