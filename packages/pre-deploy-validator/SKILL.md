---
name: pre-deploy-validator
description: Standardized pre-deployment quality gates for Node.js/Next.js projects. Run lint, type-check, tests, security audits, and builds with detailed reporting and CI/CD integration.
---

# Pre-Deployment Validator

A comprehensive validation tool for Node.js and Next.js projects that ensures code quality through standardized pre-deployment checks. Run multiple quality gates concurrently, skip checks on specific branches, and get detailed reports in console or JSON format.

## Key Features

- **Multi-check validation**: Lint, TypeScript, tests, security audits, and builds
- **Flexible configuration**: JSON-based config with per-check options
- **Parallel execution**: Run checks concurrently to save time
- **Monorepo support**: Validate multiple projects in one go
- **Branch-aware skipping**: Skip checks on specified branches (main, production)
- **Rich reporting**: Console and JSON output formats
- **CI/CD ready**: Exit codes and formatted output for automation

## How to Use

### Installation

```bash
npm install --save-dev @anthropic-community/pre-deploy-validator
```

Or use directly with `npx`:

```bash
npx @anthropic-community/pre-deploy-validator
```

### Basic Setup

Create a `.pdv.json` configuration file in your project root:

```json
{
  "name": "my-validator",
  "version": "1.0.0",
  "description": "Project validation config",
  "checks": {
    "lint": {
      "enabled": true,
      "command": "npm run lint",
      "timeoutMs": 30000,
      "onFail": "block"
    },
    "typescript": {
      "enabled": true,
      "command": "tsc --noEmit",
      "timeoutMs": 60000,
      "onFail": "block"
    },
    "tests": {
      "enabled": true,
      "command": "npm test",
      "timeoutMs": 120000,
      "onFail": "block"
    }
  },
  "parallel": true,
  "reportFormat": "console"
}
```

### Running Validation

```bash
# Use default config (.pdv.json)
npx pre-deploy-validator

# Use custom config
npx pre-deploy-validator --config=.pdv.advanced.json

# Output as JSON for CI integration
npx pre-deploy-validator --format=json > report.json

# Skip specific checks
npx pre-deploy-validator --skip=lint,tests
```

## Available Checks

### lint
Run ESLint or other linters to ensure code style compliance.

```json
{
  "lint": {
    "enabled": true,
    "command": "npm run lint",
    "timeoutMs": 30000,
    "onFail": "block"
  }
}
```

### typescript
Type-check your TypeScript code without emitting output.

```json
{
  "typescript": {
    "enabled": true,
    "command": "tsc --noEmit",
    "timeoutMs": 60000,
    "onFail": "block"
  }
}
```

### tests
Run your test suite with optional coverage validation.

```json
{
  "tests": {
    "enabled": true,
    "command": "npm test",
    "coverageThreshold": {
      "lines": 80,
      "functions": 80,
      "branches": 70
    },
    "timeoutMs": 120000,
    "onFail": "block"
  }
}
```

### security-audit
Run `npm audit` to check for dependency vulnerabilities.

```json
{
  "security-audit": {
    "enabled": true,
    "command": "npm audit --audit-level=moderate",
    "timeoutMs": 45000,
    "onFail": "warn"
  }
}
```

### build
Build single or multiple projects (useful for monorepos).

```json
{
  "build": {
    "enabled": true,
    "command": "npm run build",
    "projects": [".", "./apps/web", "./apps/api"],
    "timeoutMs": 180000,
    "onFail": "block"
  }
}
```

## Configuration Options

| Option | Type | Default | Description |
|--------|------|---------|-------------|
| `name` | string | - | Validator name |
| `version` | string | - | Config version |
| `description` | string | - | What this config validates |
| `checks` | object | - | Check definitions |
| `skipOnBranches` | string[] | [] | Branches to skip validation on |
| `parallel` | boolean | false | Run checks concurrently |
| `reportFormat` | 'console' \| 'json' | 'console' | Output format |
| `exitCode` | number | 1 | Exit code on failure |

## Examples

### Minimal Configuration
See `examples/.pdv.json` for a basic setup with just lint and tests.

```bash
npx pre-deploy-validator --config=examples/.pdv.json
```

### Advanced Configuration
See `examples/.pdv.advanced.json` for all quality gates with parallel execution.

```bash
npx pre-deploy-validator --config=examples/.pdv.advanced.json
```

### Monorepo Configuration
See `examples/monorepo.json` for validating multiple packages.

```bash
npx pre-deploy-validator --config=examples/monorepo.json
```

## Integration with CI/CD

### GitHub Actions

```yaml
name: Validate
on: [push, pull_request]

jobs:
  validate:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-node@v4
      - run: npm install
      - run: npx pre-deploy-validator --config=.pdv.json --format=json > report.json
      - name: Check validation
        if: failure()
        run: cat report.json
```

### Pre-commit Hook

Add to `.husky/pre-commit`:

```bash
#!/bin/sh
npx pre-deploy-validator
```

## Output Format

### Console Output
Human-readable terminal output with colors and status symbols.

```
📋 Pre-Deployment Validation Report

✓ Status: PASSED
⏱️  Duration: 45.23s
📅 Timestamp: 2024-01-15T10:30:45.123Z

Checks:

  ✓ lint                 (2.34s)
  ✓ typescript           (8.45s)
  ✓ tests                (32.12s)
  ✓ security-audit       (1.34s)
  ✓ build                (0.98s)

✅ All checks passed - ready to deploy!
```

### JSON Output
Machine-readable JSON for CI/CD integration and automation.

```json
{
  "success": true,
  "checks": [
    {
      "name": "lint",
      "success": true,
      "duration": 2340,
      "output": "Linting passed",
      "severity": "error"
    }
  ],
  "duration": 45230,
  "errors": [],
  "timestamp": "2024-01-15T10:30:45.123Z"
}
```

## CLI Reference

```
Usage: pre-deploy-validator [options]

Options:
  -c, --config <path>    Path to config file (.pdv.json)
  -f, --format <format>  Output format (console|json) [default: console]
  -s, --skip <checks>    Comma-separated checks to skip
  -h, --help             Display help
  -v, --version          Display version
```

## Troubleshooting

### Config file not found
Ensure `.pdv.json` exists in your project root or specify the path with `--config`.

### Timeout errors
Increase `timeoutMs` for slow operations. Consider running checks sequentially with `"parallel": false`.

### Coverage threshold not met
Check your test coverage output and adjust `coverageThreshold` values or improve test coverage.

### Build fails for monorepo
Verify all project paths in `projects` array are correct and relative to the current directory.

## When to Use

Use pre-deploy-validator when:
- You want standardized quality gates across multiple projects
- You need branch-aware skipping for production branches
- You want parallel execution to save CI/CD time
- You manage a monorepo with multiple packages
- You need both console and JSON output for different contexts
- You want to enforce coverage thresholds automatically

## Guidelines

- **Configure per-project**: Create `.pdv.json` in each project root
- **Use coverage thresholds wisely**: Balance coverage targets with practical testing
- **Skip strategically**: Use `skipOnBranches` for protected branches where validation isn't needed
- **Parallel execution**: Enable for faster CI/CD, disable for debugging
- **Custom commands**: Adapt the `command` field to match your linting, testing, and build setup

## License

MIT - See LICENSE file for details
