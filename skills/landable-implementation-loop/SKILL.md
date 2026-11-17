---
name: landable-implementation-loop
description: Drive coding tasks to a genuinely shippable state through scoped implementation, changed-surface review, adversarial self-critique, packaging checks, and real integration validation. Use this when the user wants a project made usable, deployable, releasable, or truly working instead of merely analyzed.
license: Complete terms in LICENSE.txt
---

# Landable Implementation Loop

Use this skill when a coding task should end in a verified, usable result rather than a plausible first-pass patch.

This is most useful when:

- a repository looks promising but is not yet trustworthy
- CI appears green only because meaningful checks are missing
- the public API, CLI, UI, or tool surface may not match the implemented behavior
- packaging, installation, or runtime integration matters
- the user asks to keep going until the project actually works

## Core principle

Treat "done" as a verified product state, not a code-edit state.

A change is not finished just because code compiles, a narrow test passes, or the README looks convincing. It is finished when the requested behavior is implemented, exposed through the public surface, validated through the right layers, and any remaining caveats are explicit and non-blocking.

## Default workflow

### 1. Scope the user-visible outcome

Before editing, restate what the user should be able to do after the work is complete.

Good examples:

- "The package can build, install, and run its advertised CLI entry point."
- "The MCP server starts, registers tools, and completes at least one representative tool call."
- "The UI flow can be exercised in a browser without layout overlap or broken controls."

### 2. Inventory the real touch points

Identify the minimum surface that must work:

- public entry points
- runtime modules
- packaging metadata
- CI or release workflows
- tests
- integration path
- user-facing documentation

Prefer reading the public-facing layer before assuming an internal helper is enough.

### 3. Decompose by ownership

For broad tasks, split work into independent tracks with clear ownership.

Good splits:

- runtime fixes
- packaging or CI fixes
- integration debugging
- changed-surface review
- documentation updates that match verified behavior

Avoid splitting work in ways that cause multiple workers to edit the same unstable file or repeat the same review.

### 4. Implement the smallest complete slice

Prefer one finished vertical slice over shallow edits across many areas.

Examples:

- a broken CLI entry point is fixed and covered by a focused test
- a path validation contract is fixed and verified through the public command or tool
- package metadata is corrected and validated by building and installing the artifact

Keep public signatures stable unless the requested behavior requires a deliberate API change.

### 5. Review the changed surface for blocking risk

Do not reduce review to style. Look for issues that could stop a real user:

- undefined helper references
- mismatches between public tools and internal operations
- path validation gaps
- broken entry points
- misleading CI gates
- build or install drift
- docs that claim behavior not actually exposed by the product

Turn concrete findings into repair tasks before declaring the work complete.

### 6. Stress-test assumptions

Ask, non-interactively:

- what user-visible path still fails
- what was claimed without direct validation
- what happens with missing, relative, hostile, or blocked inputs
- what only works internally but not through the public surface
- what passes locally but would fail after packaging or installation
- what depends on credentials, machine state, external services, or global configuration

Fix plausible failure modes. Name any remaining external blocker clearly.

### 7. Validate in layers

Run validation from cheapest to most real:

1. focused syntax or correctness checks
2. focused tests
3. build or packaging checks
4. install or entry-point checks
5. real integration checks

Choose commands that match the project. For example:

```bash
python -m pytest tests
python -m build
npm test
npm run build
```

For service-style projects, do not stop before a real client or browser interaction when the user expects actual usability.

### 8. Close only on verified readiness

The task is ready to close when:

- the requested behavior exists
- the public surface exposes it
- focused checks pass
- packaging or install paths work when relevant
- real integration has been exercised when relevant
- remaining caveats are explicit and non-blocking

## Legacy repository guidance

Many repositories contain historical style debt or oversized files. Do not confuse broad cleanup with release readiness.

When a repository is not uniformly clean:

- keep correctness checks blocking
- narrow style gates to realistic hotspots
- avoid claiming the whole repository is clean if it is not
- prefer honest, targeted validation over fake all-or-nothing gates

## Anti-patterns

Avoid these:

- stopping at README edits while runtime behavior is still broken
- claiming support based on internal helpers when public commands still fail
- shipping with a CI gate that cannot pass against the actual repository
- marking work complete without a real integration check when usability was requested
- doing broad refactors when one narrow runtime fix would close the loop

## Suggested trigger phrases

Use this skill when the user says things like:

- "keep going until it really works"
- "do not stop at analysis"
- "make this releasable"
- "ship this properly"
- "connect it and debug it yourself"
- "make this project usable"

## Final response shape

When finishing, report:

- what was implemented
- what was reviewed
- what was repaired after critique
- what validation actually ran
- what still remains, if anything

Keep the report concise and evidence-based.
