# Contributing to {{PROJECT_NAME}}

Thanks for your interest in contributing! This guide explains how to set up the
project, make a change and get it merged.

## Ways to contribute

- Report a bug or request a feature by [opening an issue]({{REPO_URL}}/issues/new/choose)
- Improve the documentation
- Fix a bug or build a feature. Issues labelled
  [`good first issue`]({{REPO_URL}}/labels/good%20first%20issue) are a good place to start

If you plan a larger change, please open an issue first so we can agree on the
approach before you spend time on it.

## Development setup

### Prerequisites

{{PREREQUISITES}}

### Get the code

```bash
git clone {{REPO_URL}}.git
cd {{REPO_DIR}}
{{INSTALL_COMMAND}}
```

## Making a change

1. Create a branch from `{{DEFAULT_BRANCH}}`:
   ```bash
   git checkout -b my-change
   ```
2. Make your change. Keep pull requests focused on one thing.
3. Build and test:
   ```bash
   {{BUILD_COMMAND}}
   {{TEST_COMMAND}}
   ```
4. Check formatting and lint:
   ```bash
   {{FORMAT_COMMAND}}
   {{LINT_COMMAND}}
   ```
5. Commit with a clear message that says what changed and why.

## Opening a pull request

- Fill in the pull request template.
- Link the issue it fixes, for example `Fixes #123`.
- Make sure CI passes.
- A maintainer will review it. Please be patient, and expect a few rounds of
  feedback on bigger changes.

## Getting help

{{SUPPORT_CHANNEL}}

## Code of conduct

By taking part in this project you agree to follow our
[Code of Conduct](CODE_OF_CONDUCT.md).

## License

By contributing, you agree that your contributions will be licensed under the
project's [{{LICENSE_NAME}}](LICENSE).
