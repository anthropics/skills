---
name: changelog-curator
description: Generate and maintain changelogs, release notes, and version history documentation. Use when users need to document changes between versions, create release notes, maintain CHANGELOG files, summarize git commits, or track version history. Triggers on requests like "update changelog", "write release notes", "document changes", "version history", "what changed", or "summarize commits".
---

# Changelog Curator

Create clear, useful change documentation that serves both developers and users.

## Changelog Formats

### Keep a Changelog Format (Recommended)

Standard format from keepachangelog.com:

```markdown
# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/),
and this project adheres to [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Added
- New feature description

### Changed
- Modification to existing functionality

### Deprecated
- Features that will be removed in future

### Removed
- Features removed in this release

### Fixed
- Bug fixes

### Security
- Security-related changes

## [1.2.0] - 2024-03-15

### Added
- User profile avatars (#142)
- Export to CSV functionality

### Fixed
- Login timeout issue on slow connections (#138)

## [1.1.0] - 2024-02-01
...

[Unreleased]: https://github.com/user/repo/compare/v1.2.0...HEAD
[1.2.0]: https://github.com/user/repo/compare/v1.1.0...v1.2.0
[1.1.0]: https://github.com/user/repo/releases/tag/v1.1.0
```

### Change Categories

| Category | Use For |
|----------|---------|
| **Added** | New features, capabilities |
| **Changed** | Changes to existing features |
| **Deprecated** | Features marked for removal |
| **Removed** | Deleted features |
| **Fixed** | Bug fixes |
| **Security** | Vulnerability patches |

## Writing Effective Entries

### Good Entry Structure

```markdown
- [Action verb] [what changed] [context/benefit] (#issue)
```

Examples:
```markdown
### Added
- Add dark mode theme with system preference detection (#234)
- Support WebP image uploads alongside PNG and JPEG

### Changed
- Improve search performance by 40% using indexed queries
- Update authentication flow to require email verification

### Fixed
- Fix crash when uploading files larger than 10MB (#189)
- Resolve incorrect timezone display for UTC+12 users
```

### Avoid

```markdown
# Bad examples
- Fixed bug          # Too vague
- Updated stuff      # Meaningless
- v1.2.3 changes     # No information
- Refactored code    # Internal, not user-facing
- Misc improvements  # Says nothing
```

### Audience Awareness

**For Developers (CHANGELOG.md)**:
- Include issue/PR references
- Mention breaking changes prominently
- Note migration steps

**For Users (Release Notes)**:
- Focus on benefits, not implementation
- Use plain language
- Group by user-facing impact

## Generating from Git History

### Extract Commits Since Last Tag

```bash
# Get commits since last tag
git log $(git describe --tags --abbrev=0)..HEAD --oneline

# With more detail
git log $(git describe --tags --abbrev=0)..HEAD --pretty=format:"- %s (%h)"

# Filter by type (if using conventional commits)
git log --oneline | grep -E "^[a-f0-9]+ (feat|fix|docs):"
```

### Conventional Commits Mapping

If project uses conventional commits:

| Prefix | Changelog Category |
|--------|-------------------|
| `feat:` | Added |
| `fix:` | Fixed |
| `docs:` | (Usually skip) |
| `refactor:` | (Usually skip) |
| `perf:` | Changed |
| `security:` | Security |
| `BREAKING CHANGE:` | Changed (highlight!) |

### Processing Commits

1. **Group** commits by category
2. **Filter** out internal changes (refactors, tests, CI)
3. **Summarize** related commits into single entries
4. **Link** to issues/PRs where helpful
5. **Highlight** breaking changes

## Semantic Versioning Reference

```
MAJOR.MINOR.PATCH

MAJOR: Breaking changes (API incompatible)
MINOR: New features (backwards compatible)
PATCH: Bug fixes (backwards compatible)
```

### Version Decision Tree

```
Does this change break existing API/behavior?
├─ YES → Increment MAJOR (reset MINOR, PATCH to 0)
└─ NO → Does this add new functionality?
        ├─ YES → Increment MINOR (reset PATCH to 0)
        └─ NO → Increment PATCH
```

### Pre-release Versions

```
1.0.0-alpha.1    # Early testing
1.0.0-beta.1     # Feature complete, testing
1.0.0-rc.1       # Release candidate
```

## Release Notes Template

For user-facing release communications:

```markdown
# [Product Name] v[X.Y.Z] Release Notes

**Release Date**: [Date]

## Highlights

[2-3 sentence summary of the most important changes]

## What's New

### [Feature Name]
[Description focused on user benefit, not technical implementation]
[Optional: screenshot or example]

### [Feature Name]
...

## Improvements

- [Improvement 1]
- [Improvement 2]

## Bug Fixes

- Fixed [issue description] ([#123])

## Breaking Changes

> **Action Required**: [What users need to do]

[Description of what changed and migration steps]

## Upgrade Instructions

[Steps to upgrade from previous version]

## Known Issues

- [Issue description] - Workaround: [workaround]

---

[Full changelog](link) | [Documentation](link) | [Support](link)
```

## Maintenance Practices

### Continuous Updates

Add entries as changes are merged, not at release time:
```markdown
## [Unreleased]

### Added
- Feature merged today (#456)
```

### Release Checklist

When cutting a release:
1. [ ] Move `[Unreleased]` entries to new version section
2. [ ] Add version number and date
3. [ ] Update comparison links at bottom
4. [ ] Create new empty `[Unreleased]` section
5. [ ] Review entries for clarity and completeness
6. [ ] Verify all breaking changes are prominently noted

### Breaking Change Format

Always make breaking changes obvious:

```markdown
## [2.0.0] - 2024-03-20

### Changed

- **BREAKING**: Rename `getUser()` to `fetchUser()` for consistency

  Migration:
  ```diff
  - const user = api.getUser(id)
  + const user = api.fetchUser(id)
  ```

- **BREAKING**: Remove deprecated `legacy` option from config
```

## Quality Checklist

- [ ] Each entry starts with a verb (Add, Fix, Change, Remove)
- [ ] Entries are user-meaningful, not implementation details
- [ ] Issue/PR links included where helpful
- [ ] Breaking changes clearly marked
- [ ] Version follows semantic versioning
- [ ] Date format consistent (YYYY-MM-DD recommended)
- [ ] Comparison links at bottom are correct
