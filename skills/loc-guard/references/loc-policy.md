# LOC Guard Policy

This document defines how agents should interpret LOC Guard results.

## Core rule

600 counted LOC is a hard cap unless the user explicitly approves an exception.

400 counted LOC is a review trigger, not an automatic refactor command.

## Warning interpretation

When a changed or new file warns, inspect whether the file is still cohesive and single-responsibility.

Decide whether the extra size is justified by necessary orchestration or simple structure, or whether the file is mixing separable responsibilities.

Consider likely near-term growth from upcoming slices before accepting a warning.

Split only when it improves responsibility boundaries or reduces meaningful complexity.

Do not split purely to satisfy the number if the split adds indirection without design benefit.

## Required report text

For a warning, report either:

```text
warning accepted with justification: ...
```

or:

```text
split performed because: ...
```

For a hard fail, report:

```text
hard cap reached; user approval required
```

unless the file was split below the cap.

## Normal exemptions

These files are usually excluded by config:

- generated files;
- vendored files;
- minified assets;
- designer files;
- compiled output;
- migrations;
- snapshots;
- lock files;
- machine-produced files.

## Test files

Test files may pass the soft cap when the size is caused by clear grouped cases and the file remains easy to navigate.

A test file above the hard cap should still be split unless the user explicitly approves an exception.

## Design preference

Prefer cohesive modules over artificial fragmentation.

The point is maintainability, not numeric purity.
