# Contributing to the SDK

The SDK powers every Strands agent—the agent loop, model integrations, tool execution, and streaming. When you fix a bug or improve performance here, you're helping every developer who uses Strands.

This guide walks you through contributing to sdk-python and sdk-typescript. We'll cover what types of contributions we accept, how to set up your development environment, and how to submit your changes for review.

## Find something to work on

Looking for a place to start? Check our issues labeled "ready for contribution"—these are well-defined and ready for community work.

- [Python SDK issues](https://github.com/strands-agents/sdk-python/issues?q=is%3Aissue+state%3Aopen+label%3A%22ready+for+contribution%22)
- [TypeScript SDK issues](https://github.com/strands-agents/sdk-typescript/issues?q=is%3Aissue+state%3Aopen+label%3A%22ready+for+contribution%22)

Before starting work on any issue, check if someone is already assigned or working on it.

## What we accept

We welcome contributions that improve the SDK for everyone. Focus on changes that benefit the entire community rather than solving niche use cases.

- **Bug fixes with tests** that verify the fix and prevent regression
- **Performance improvements with benchmarks** showing measurable gains
- **Documentation improvements** including docstrings, code examples, and guides
- **Features that align with our [roadmap](https://github.com/orgs/strands-agents/projects/8/views/1)** and development tenets
- **Small, focused changes** that solve a specific problem clearly

## What we don't accept

Some contributions don't fit the core SDK. Understanding this upfront saves you time and helps us maintain focus on what matters most.

- **Large refactors without prior discussion** — Major architectural changes require a [feature proposal](./feature-proposals.md)
- **Breaking changes without approval** — We maintain backward compatibility carefully. Breaking changes require a [feature proposal](./feature-proposals.md)
- **External tools** — [Build your own extension](./extensions.md) instead for full ownership
- **Changes without tests** — Tests ensure quality and prevent regressions (documentation changes excepted)
- **Niche features** — Features serving narrow use cases belong in extensions

If you're unsure whether your contribution fits, [open a discussion](https://github.com/strands-agents/sdk-python/discussions) first. We're happy to help you find the right path.

## Set up your development environment

Let's get your local environment ready for development. This process differs slightly between Python and TypeScript.

=== "Python"

    First, we'll clone the repository and set up the virtual environment.

    ```bash
    git clone https://github.com/strands-agents/sdk-python.git
    cd sdk-python
    ```

    We use [hatch](https://hatch.pypa.io/) for Python development. Hatch manages virtual environments, dependencies, testing, and formatting. Enter the virtual environment and install pre-commit hooks.

    ```bash
    hatch shell
    pre-commit install -t pre-commit -t commit-msg
    ```

    The pre-commit hooks automatically run code formatters, linters, tests, and commit message validation before each commit. This ensures code quality and catches issues early.

    Now let's verify everything works by running the tests.

    ```bash
    hatch test                  # Run unit tests
    hatch test -c               # Run with coverage report
    ```

    You can also run linters and formatters manually.

    ```bash
    hatch fmt --linter          # Check for code quality issues
    hatch fmt --formatter       # Auto-format code with ruff
    ```

    To run all quality checks at once (format, lint, and tests across all Python versions), use the prepare script.

    ```bash
    hatch run prepare           # Run all checks before committing
    ```

    **Development tips:**

    - Use `hatch run test-integ` to run integration tests with real model providers
    - Run `hatch test --all` to test across Python 3.10-3.13
    - Check [CONTRIBUTING.md](https://github.com/strands-agents/sdk-python/blob/main/CONTRIBUTING.md) for detailed development workflow

=== "TypeScript"

    First, we'll clone the repository and install dependencies.

    ```bash
    git clone https://github.com/strands-agents/sdk-typescript.git
    cd sdk-typescript
    npm install
    ```

    The TypeScript SDK uses npm for dependency management and includes automated quality checks through git hooks. The `prepare` script builds the project and sets up Husky git hooks.

    ```bash
    npm run prepare
    ```

    Now let's verify everything works by running all quality checks.

    ```bash
    npm run check               # Run all checks (lint, format, type-check, tests)
    ```

    You can also run individual checks.

    ```bash
    npm test                    # Run unit tests
    npm run test:coverage       # Run with coverage (80%+ required)
    npm run lint                # Run ESLint
    npm run format              # Format code with Prettier
    npm run type-check          # TypeScript type checking
    ```

    **Development tips:**

    - Use `npm run test:integ` to run integration tests
    - Run `npm run test:all` to test in both Node.js and browser environments
    - Check [CONTRIBUTING.md](https://github.com/strands-agents/sdk-typescript/blob/main/CONTRIBUTING.md) for detailed requirements

## Submit your contribution

Once you've made your changes, here's how to submit them for review.

1. **Fork and create a branch** with a descriptive name like `fix/session-memory-leak` or `feat/add-hooks-support`
2. **Write tests** for your changes—tests are required for all code changes
3. **Run quality checks** before committing to ensure everything passes:
    - Python: `hatch run prepare`
    - TypeScript: `npm run check`
4. **Use [conventional commits](https://www.conventionalcommits.org/)** like `fix: resolve memory leak in session manager` or `feat: add streaming support to tools`
5. **Submit a pull request** referencing the issue number in the description
6. **Respond to feedback** — we'll review within a few days and may request changes

The pre-commit hooks help catch issues before you push, but you can also run checks manually anytime.

## Related guides

- [Feature proposals](./feature-proposals.md) — For significant features requiring discussion
- [Team documentation](https://github.com/strands-agents/docs/tree/main/team) — Our tenets, decisions, and API review process
