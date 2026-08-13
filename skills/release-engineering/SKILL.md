---
name: release-engineering
description: Plan, assess, and execute software releases safely. Use when preparing a release, cutting a version, creating release notes, assessing release readiness, reviewing changes since the last release, planning migrations or rollbacks, or verifying a release after deployment.
---

# Release Engineering

Treat a release as a controlled transition from a known source state to a known deployed state. Optimize for correctness, traceability, reversibility, and clear communication.

## Release Assessment

Before recommending or executing a release:

- Identify the project's release mechanism:
  - Git tags
  - GitHub/GitLab releases
  - package publishing
  - container/image publishing
  - deployment pipelines
  - application-specific release tooling
- Identify the current version and the previous release.
- Inspect the repository's release documentation, contribution guidelines, CI configuration, and versioning conventions.
- Determine which branch or commit is intended for release.
- Inspect changes since the previous release using git history and the repository's normal change-tracking conventions.
- Identify user-facing, API-facing, operational, dependency, configuration, and data-model changes.
- Determine whether the project's existing versioning convention implies a major, minor, patch, prerelease, or other version change.

Do not assume a release process that conflicts with repository conventions.

## Release Readiness

Assess the release across these dimensions:

### Code

Check:

- Tests relevant to changed components
- Integration or end-to-end tests when applicable
- Build/package success
- Static analysis and linting when part of the repository workflow
- Known failing tests
- Uncommitted or unexpected changes
- Generated files that must be updated
- Version consistency across manifests, source files, containers, and documentation

Distinguish between:
- verified
- not checked
- failed
- not applicable

Never describe an unexecuted check as passing.

### Changes

Classify important changes as:

- Features
- Bug fixes
- Breaking changes
- Deprecations
- Dependency changes
- Configuration changes
- Database/schema changes
- Infrastructure/deployment changes
- Security-sensitive changes
- Documentation changes

Flag changes that require coordinated work outside the repository.

### Dependencies

For dependency changes:

- Identify direct dependency upgrades and additions.
- Identify potentially significant transitive changes when the package manager exposes them.
- Check for lockfile changes.
- Look for known compatibility or migration requirements when available.
- Identify changes that could affect runtime, build, licensing, or security posture.

Do not claim that dependencies are secure or vulnerability-free without an actual check.

### Configuration and Infrastructure

Check for changes involving:

- Environment variables
- Configuration files
- Secrets or secret references
- Ports and networking
- Deployment manifests
- Containers/images
- Cloud resources
- Feature flags
- Service dependencies
- Runtime requirements

Clearly identify configuration that must be changed by an operator rather than committed to the repository.

### Data and Migrations

For schema, database, storage, or data-format changes:

- Determine whether a migration is required.
- Determine whether the migration is backward compatible.
- Identify ordering constraints between application and migration deployment.
- Identify irreversible operations.
- Identify backup or restore requirements when appropriate.
- Define how rollback behaves if the migration has already executed.

Treat destructive or irreversible migrations as release risks requiring explicit attention.

## Release Notes

Generate release notes from verified repository changes rather than guessing from commit messages alone.

Prioritize:

1. User-visible changes
2. Breaking changes
3. Important fixes
4. Deprecations
5. Operational changes
6. Dependency/runtime requirements

Use the project's established release-note format when one exists.

For breaking changes, state:

- What changed
- Who is affected
- What they must change
- When the old behavior stops working

Avoid exposing internal implementation details unless they matter to users or operators.

## Release Checklist

Produce a concise checklist appropriate to the repository.

At minimum consider:

- [ ] Release target identified
- [ ] Version determined
- [ ] Changes reviewed
- [ ] Breaking changes identified
- [ ] Required tests completed
- [ ] Build/package verified
- [ ] Dependencies reviewed
- [ ] Configuration changes identified
- [ ] Migrations reviewed
- [ ] Documentation updated
- [ ] Release notes prepared
- [ ] Rollback strategy defined
- [ ] Release artifact/version consistency verified
- [ ] CI/release pipeline status verified
- [ ] Release published
- [ ] Post-release verification completed

Remove items that are clearly not applicable.

## Rollback Planning

Every release should have an explicit recovery strategy.

Determine:

- What artifact or version should be restored.
- Whether rollback means redeployment, reverting a commit, disabling a feature flag, or another mechanism.
- Whether database or data changes prevent a simple rollback.
- Which externally visible changes cannot be automatically reversed.
- What signals should trigger rollback.
- Who or what is responsible for initiating recovery when the repository provides that information.

Do not claim rollback is safe when the release contains irreversible changes.

## Release Execution

When the user explicitly asks to perform release actions:

1. Confirm the intended target and current repository state.
2. Re-check release readiness immediately before modifying release state.
3. Follow the repository's established release mechanism.
4. Avoid destructive operations unless explicitly authorized.
5. Verify the resulting tag, artifact, package, or deployment.
6. Record the resulting version and commit/tag relationship.
7. Perform post-release checks appropriate to the project.

Prefer dry-run or inspection commands when the user's intent is unclear.

## Post-Release Verification

After a release, verify the actual resulting state rather than assuming the release succeeded.

Check applicable signals such as:

- Published version
- Git tag
- Package registry artifact
- Container/image availability
- Deployment status
- Health checks
- Smoke tests
- Relevant logs
- Version reported by the running application
- Documentation or release page

Report discrepancies explicitly.

## Output

When assessing a release, structure the result as:

### Release
- Target:
- Current version:
- Proposed version:
- Release mechanism:

### Readiness
- Ready / Ready with risks / Not ready

### Required Actions
Prioritized actions that must be completed before release.

### Risks
Include severity and affected area.

### Release Notes
User-facing summary of verified changes.

### Rollback
Concrete recovery strategy and limitations.

### Checklist
Only applicable release steps.

### Post-Release Verification
Checks to perform after publication or deployment.

Keep conclusions evidence-based. Separate repository facts, command results, inferred risks, and recommendations.
