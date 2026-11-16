# Spec Files: requirements.md, design.md, tasks.md

Each feature lives in its own directory (default `.specs/<feature-name>/`). The
directory name becomes the canonical feature identifier used in traceability,
status tracking, and cross-references.

```
.specs/
  <feature-name>/
    requirements.md   — What the system must do (EARS-formatted)
    design.md         — How the system will satisfy the requirements
    tasks.md          — Ordered implementation steps
    traceability.md   — R<n> → test → implementation mapping (created during work)
```

## requirements.md

The authoritative list of functional requirements, EARS-formatted. See
[ears.md](ears.md) for the patterns and hard rules. Minimum structure:

```markdown
# Requirements: <feature-name>

## R1
The system shall reject login attempts after 5 consecutive failures.

## R2
When the user submits a valid credentials pair, the system shall issue an
authentication token.
```

## design.md

Captures **how** the system will satisfy the requirements. Required sections:

- **Files to create or modify**: full paths of every source file that will
  change, with a one-line description of the change per file.
- **Public signatures**: all new or changed function/method signatures,
  including parameter types and return types.
- **Exceptions and error cases**: every error condition the implementation
  must handle, mapped to the requirement(s) that trigger it.
- **Discarded alternatives**: at least one alternative approach that was
  considered and rejected, with a brief explanation of why.

The design does not need to contain full implementation code. It must contain
enough detail that a reviewer can confirm the approach is sound and that all
requirements are covered.

## tasks.md

Breaks the design into discrete, ordered implementation steps:

```markdown
# Tasks: <feature-name>

- [ ] T1: Create the authentication module skeleton
      depends_on: (none)
      refs: R1, R2

- [ ] T2: Implement failure counter logic
      depends_on: T1
      refs: R1

- [ ] T3: Implement token issuance
      depends_on: T1
      refs: R2

- [ ] T4: Write unit tests for failure counter
      depends_on: T2
      refs: R1

- [ ] T5: Write unit tests for token issuance
      depends_on: T3
      refs: R2
```

Rules:

- Each task is a single discrete step that can be completed and verified
  independently.
- **Size for batches**: an implementer works 2–4 consecutive tasks per pass.
  One task = one coherent change **plus** the tests that verify it, and every
  2–4 consecutive tasks must form a batch that lands with green gates on its
  own. Split any task that would create more than ~400 lines or span unrelated
  layers — a batch that cannot finish in one session is a batch that stalls.
- `depends_on` lists the task IDs that must be completed first. Use `(none)`
  for tasks with no dependencies. Keep chains shallow: batch n+1 must be
  startable from the files batch n leaves behind.
- `refs` lists the requirement IDs (R\<n\>) that this task contributes to
  satisfying. Every R\<n\> must be referenced by at least one task.
