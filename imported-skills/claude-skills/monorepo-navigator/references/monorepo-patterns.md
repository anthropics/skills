# Monorepo Patterns

## Common Layouts

### apps + packages

- `apps/*`: deployable applications
- `packages/*`: shared libraries, UI kits, utilities
- `tooling/*`: lint/build config packages

### domains + shared

- `domains/*`: bounded-context product areas
- `shared/*`: cross-domain code with strict API contracts

### service monorepo

- `services/*`: backend services
- `libs/*`: shared service contracts and SDKs

## Dependency Rules

- Prefer one-way dependencies from apps/services to packages/libs.
- Keep cross-app imports disallowed unless explicitly approved.
- Keep `types` packages runtime-free to avoid unexpected coupling.

## Build/CI Patterns

- Use affected-only CI (`--filter` or equivalent).
- Enable remote cache for build and test tasks.
- Split lint/typecheck/test tasks to isolate failures quickly.

## Release Patterns

- Use Changesets or equivalent for versioning.
- Keep package publishing automated and reproducible.
- Use prerelease channels for unstable shared package changes.
