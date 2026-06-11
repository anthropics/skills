# Seam Heuristics

Reasoning library for greenlight. Part A feeds Phase 2 (blast radius), Part B feeds Phase 3
(constraints), Part C feeds Phase 4 (the verdict). These are triggers to reason from, not a
checklist to tick.

---

## Part A — Coupling taxonomy

The six kinds of connection a change can have. For each, the question to ask and where it tends to
hide. Trace outward from the entry point until new edges stop appearing; if they don't stop, that
unbounded radius is itself a finding.

**1. Call coupling** — who calls this, and what do they assume?
- Where it hides: every call site of the function/method/endpoint. Signature, return shape,
  thrown errors, and *implicit* expectations (sorted output, non-null, a particular unit).
- Tell: changing a return type or raising a new error silently breaks a caller that never updated.

**2. Data coupling** — what state does it share with the rest of the system?
- Where it hides: DB tables/columns read or written, caches, global/singleton state, files,
  environment, shared in-memory structures.
- Tell: two code paths write the same row/key with different assumptions about its meaning.

**3. Temporal / ordering coupling** — does correctness depend on *when* or *in what order* this runs?
- Where it hides: init sequences, migrations, cron/queue ordering, "must run after X", retries,
  idempotency assumptions, race windows.
- Tell: the change is correct in isolation but wrong if it runs before/after/again.

**4. Contract coupling** — what external shape must stay stable?
- Where it hides: public/REST/GraphQL APIs, event/message schemas, serialized formats, stored
  records already on disk, anything another team or a persisted artifact depends on.
- Tell: a "small" field rename breaks a consumer you can't see or a record written last year.

**5. Side-effect coupling** — what does this *cause* beyond returning a value?
- Where it hides: emails, payments, webhooks, analytics events, audit logs, notifications,
  downstream triggers.
- Tell: a refactor that "cleans up" a path quietly stops firing an event something else counts on,
  or double-fires it.

**6. Semantic / convention coupling** — what unwritten rules does the codebase enforce by habit?
- Where it hides: error-handling style, auth/permission checks done a certain way, logging,
  validation placement, naming that carries meaning. Not enforced by the type system.
- Tell: the change compiles and passes tests but violates a pattern every other module follows.

> Dynamic dispatch, reflection, metaprogramming, string-built queries, and config-driven behaviour
> hide all six. When you hit them and can't trace through, **say so and downgrade the verdict** —
> untraceable coupling is still coupling.

---

## Part B — Implicit-constraint catalog

The invariants that are true today and must stay true, expressed as **"must preserve: …"** lines.
These live in the code and the data, not in the prompt — surfacing them is the point.

- **Caller invariants** — properties callers rely on: non-null, sorted, bounded range, idempotent,
  no-throw-on-empty, stable ordering.
- **Data integrity** — referential integrity, uniqueness, a status only moving forward, a balance
  never going negative, a column's domain.
- **Stored-format compatibility** — already-persisted records must stay readable; a schema/format
  change needs a migration or back-compat path, not just new-write code.
- **Edge contracts** — API/event/message shapes consumers depend on; versioning rules; what may be
  added (usually safe) vs. renamed/removed/retyped (usually breaking).
- **Side-effect fidelity** — effects that must keep firing exactly once: the payment, the audit
  entry, the notification. Note both "must still fire" and "must not double-fire."
- **Security/permission invariants** — auth checks, tenant isolation, input validation, secrets
  handling that must remain on every path the change touches.
- **Performance invariants** — a hot path's complexity or a query's index usage that must not
  regress, where the system depends on it.

Only list constraints the blast radius actually implicates. A short, complete list beats a long
speculative one — and completeness matters more than length, because a missed constraint is the
regression.

---

## Part C — Seam-quality rubric

A boundary is only useful if it's **true**: the coupling crossing it is thin and fully captured by
the Part B constraints. Score the candidate seam on these, then map to a verdict.

A true seam tends to have:

- **Thin crossing** — few edges cross it, and each is a simple, nameable contract (a value, a typed
  input/output), not a tangle of shared state.
- **Complete capture** — every crossing edge is covered by a "must preserve" line. Nothing crosses
  that you can't write down.
- **Stable contract** — what crosses is already a real interface or can be stated as one without
  changing behaviour.
- **No hidden channels** — no shared globals, no temporal ordering, no side effects sneaking across
  outside the named contract.

A **false seam** looks clean but leaks: shared mutable state across the line, an ordering dependency
you didn't list, a side effect that crosses silently, or an edge you couldn't trace. A false seam is
worse than honest entanglement, because it produces a confident change that breaks something
invisible.

### Mapping to the verdict

- **`feasible`** — thin crossing, complete capture, no hidden channels. The contract fully replaces
  knowledge of the system. Safe to implement inside the boundary like greenfield.
- **`partial`** — a real boundary exists but at least one edge leaks or stays risky: some shared
  state, an ordering constraint, a side effect that needs watching. Proceed only with those edges
  named as guardrails and a human checkpoint at each. List the specific touch points.
- **`not_feasible`** — crossing is wide, or capture is incomplete (edges you can't trace or can't
  bound), or correctness depends on diffuse system state. No honest boundary. Do not run an
  autonomous agent. Recommend refactor-first (name the seam that *would* need to exist for this to
  become `partial`/`feasible`) or human-paired implementation.

When a seam sits between two levels, choose the more cautious one and state the leak that made you
downgrade. The requester is usually trusting the verdict blind; earn it.