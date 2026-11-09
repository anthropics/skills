# Open-source readiness checklist

What each item is for, what "good" looks like, and how the audit scores it.
Weights add up to 100.

## Essential (55 points)

### README (20)
A newcomer should be able to answer "what is this, how do I run it, how do I
help?" in under two minutes.

Good README has:
- One-paragraph description of what the project does and who it is for
- Install / setup steps that work on a clean machine
- A minimal usage example (command, code snippet or screenshot)
- A "Contributing" section or link to CONTRIBUTING.md
- A "License" section naming the license

Audit: **pass** if the file exists, is at least 300 characters, and has
install and usage headings; **partial** if it exists but is short or missing
those headings.

### LICENSE (20)
Without a license, nobody can legally use, copy or contribute to the code,
even if it is public. The file must be the full official text.

Audit: **pass** if a LICENSE / LICENCE / COPYING file exists and a known
license is recognised; **partial** if a file exists but the license could not
be identified.

### CONTRIBUTING.md (15)
Tells contributors how to set up, test and submit changes.

Good CONTRIBUTING.md has:
- Prerequisites (language version, tools)
- Exact setup, build and test commands for this project
- Branch / commit conventions, if the project has any
- How to open a pull request and what reviewers check
- Where to ask questions

Audit: **pass** if it exists in root, `.github/` or `docs/` and mentions a
test or build command; **partial** if it exists without commands.

## Community (25 points)

### CODE_OF_CONDUCT.md (7)
Sets expectations for behaviour and names who enforces them. Many projects
adopt the Contributor Covenant (https://www.contributor-covenant.org/); the
bundled template is a short alternative. If the user prefers the Contributor
Covenant, link to or copy the official text unmodified, with its attribution.

### SECURITY.md (7)
Tells people how to report vulnerabilities **privately** instead of in a
public issue. Must contain a real contact route. GitHub's private
vulnerability reporting is a good default when the repo is on GitHub.

### Issue templates (6)
Structured forms make bug reports reproducible. YAML issue forms in
`.github/ISSUE_TEMPLATE/` are preferred on GitHub. Audit: **pass** with at
least one template; `config.yml` alone counts as partial.

### Pull request template (5)
A short checklist (what changed, how it was tested, linked issue).

## Tooling (20 points)

### Continuous integration (8)
Runs tests on every pull request so maintainers can trust contributions.
Audit looks for `.github/workflows/*.yml`, `.gitlab-ci.yml`,
`.circleci/config.yml`, `azure-pipelines.yml`, `.travis.yml`, `Jenkinsfile`.

### .gitignore (4)
Keeps build output, dependencies and secrets out of the repo.

### Tests (5)
Audit looks for a tests directory or test files matching common patterns
(`*_test.go`, `test_*.py`, `*.test.ts`, `*.spec.js`, `tests/`, `__tests__/`,
and inline Rust `#[test]` functions). Missing tests are reported, not
generated: writing tests is outside this skill's scope, but CONTRIBUTING.md
should say honestly that tests are welcome.

### CHANGELOG (3)
`CHANGELOG.md` or `HISTORY.md`, or GitHub releases. Suggest the
https://keepachangelog.com format.

## Warnings (no points, always shown first)

- `.env`, `*.pem`, `id_rsa`, `credentials.json` or similar files that exist
  and are not covered by `.gitignore`
- Very large files (over 10 MB) that probably should not be committed

## Grades

| Score | Grade | Meaning |
|---|---|---|
| 90-100 | A | Ready for contributors |
| 75-89 | B | Nearly there |
| 50-74 | C | Usable, but newcomers will struggle |
| 0-49 | D | Not ready to accept contributions |
