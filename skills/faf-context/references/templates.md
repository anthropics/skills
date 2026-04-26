# Stack Templates

## TypeScript/React

```yaml
faf_version: "2.0"
project:
  name: # from package.json
  description: # from README
  stack: [typescript, react]

context:
  architecture: |
    React SPA with component-based architecture.
    State: [Redux/Zustand/Context].
  key_files:
    - src/App.tsx: Root component
    - src/components/: Reusable UI
    - src/hooks/: Custom hooks
    - src/api/: API client
  conventions:
    - Functional components with hooks
    - TypeScript strict mode
    - Props interfaces co-located

ai_guidance:
  priorities: [type-safety, component-reuse, a11y]
  avoid: [class-components, any-type, inline-styles]
  testing: Vitest + React Testing Library
```

## Rust

```yaml
faf_version: "2.0"
project:
  name: # from Cargo.toml
  description: # from Cargo.toml
  stack: [rust]

context:
  architecture: |
    [Binary/Library] crate.
    Error handling: thiserror + anyhow.
  key_files:
    - src/main.rs: Entry point
    - src/lib.rs: Public API
    - src/error.rs: Error types
  conventions:
    - No unwrap in library code
    - Prefer &str over String for inputs

ai_guidance:
  priorities: [safety, performance, ergonomic-api]
  avoid: [unwrap, unnecessary-clone, panic-in-lib]
  testing: cargo test, proptest for properties
```

## Python

```yaml
faf_version: "2.0"
project:
  name: # from pyproject.toml
  description: # from README
  stack: [python]

context:
  architecture: |
    [CLI/API/Library] using [framework].
  key_files:
    - src/main.py: Entry point
    - src/core/: Business logic
    - tests/: Test suite
  conventions:
    - Type hints on public functions
    - Google-style docstrings

ai_guidance:
  priorities: [readability, type-safety, testability]
  avoid: [bare-except, mutable-defaults]
  testing: pytest, >80% coverage
```

## Go

```yaml
faf_version: "2.0"
project:
  name: # from go.mod
  description: # from README
  stack: [go]

context:
  architecture: |
    [CLI/API/Library] with standard layout.
  key_files:
    - cmd/: Entry points
    - internal/: Private packages
    - pkg/: Public packages
  conventions:
    - Accept interfaces, return structs
    - Table-driven tests

ai_guidance:
  priorities: [simplicity, performance, explicit-errors]
  avoid: [interface-pollution, panic-for-errors]
  testing: go test with testify
```

## Node.js/Express

```yaml
faf_version: "2.0"
project:
  name: # from package.json
  description: # from README
  stack: [node, express]

context:
  architecture: |
    Express API with [MVC/layered] structure.
  key_files:
    - src/index.js: Server entry
    - src/routes/: Route handlers
    - src/middleware/: Express middleware
  conventions:
    - Async/await for async ops
    - Centralized error handling

ai_guidance:
  priorities: [security, performance, error-handling]
  avoid: [callback-hell, sync-file-ops]
  testing: Jest + supertest
```
