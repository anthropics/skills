# Pre-Deployment Validator

Standardized pre-deployment quality gates for Node.js/Next.js projects. Run lint, type-check, tests, security audits, and builds in a single command with detailed reporting.

## Features

- ✅ **Multi-check validation**: Lint, TypeScript, tests, security audits, and builds
- ✅ **Flexible configuration**: JSON-based config with per-check options
- ✅ **Parallel execution**: Run checks concurrently to save time
- ✅ **Monorepo support**: Validate multiple projects in one go
- ✅ **Branch-aware skipping**: Skip checks on specified branches (main, production)
- ✅ **Rich reporting**: Console and JSON output formats
- ✅ **CI/CD ready**: Exit codes and formatted output for automation

## Installation

```bash
npm install --save-dev @anthropic-community/pre-deploy-validator
```

Or use directly with `npx`:

```bash
npx @anthropic-community/pre-deploy-validator
```

## Quick Start

### 1. Create a `.pdv.json` config file

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
    }
  },
  "parallel": false,
  "reportFormat": "console",
  "exitCode": 1
}
```

### 2. Run the validator

```bash
# Using default config (.pdv.json)
npx pre-deploy-validator

# Using custom config
npx pre-deploy-validator --config=.pdv.advanced.json

# Output as JSON for CI integration
npx pre-deploy-validator --format=json > /tmp/report.json

# Skip specific checks
npx pre-deploy-validator --skip=lint,tests
```

## Configuration

### Config Schema

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `name` | string | - | Validator name |
| `version` | string | - | Config version |
| `description` | string | - | What this config validates |
| `checks` | object | - | Check definitions (see below) |
| `skipOnBranches` | string[] | [] | Branches to skip validation on |
| `parallel` | boolean | false | Run checks concurrently |
| `reportFormat` | 'console' \| 'json' | 'console' | Output format |
| `exitCode` | number | 1 | Exit code on failure |

### Check Configuration

Each check in the `checks` object supports:

| Field | Type | Default | Description |
|-------|------|---------|-------------|
| `enabled` | boolean | - | Enable/disable this check |
| `command` | string | - | Command to run |
| `timeoutMs` | number | - | Timeout in milliseconds |
| `onFail` | 'block' \| 'warn' | - | Fail behavior |
| `coverageThreshold` | object | - | Coverage targets (tests only) |
| `projects` | string[] | ['.'] | Projects to validate (build only) |

## Available Checks

### lint
Run ESLint or other linters.

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
Type-check with tsc.

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
Run test suite with optional coverage validation.

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
Run `npm audit` with a severity threshold.

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
Build single or multiple projects (monorepo support).

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

## Examples

### Minimal Config
See [`examples/.pdv.json`](examples/.pdv.json)

```bash
npx pre-deploy-validator --config=examples/.pdv.json
```

### Advanced Config
See [`examples/.pdv.advanced.json`](examples/.pdv.advanced.json)

All quality gates with parallel execution.

```bash
npx pre-deploy-validator --config=examples/.pdv.advanced.json
```

### Monorepo Config
See [`examples/monorepo.json`](examples/monorepo.json)

Validate multiple packages in a monorepo.

```bash
npx pre-deploy-validator --config=examples/monorepo.json
```

## API Usage

```typescript
import { PreDeployValidator, formatConsoleReport } from '@anthropic-community/pre-deploy-validator';
import { readFileSync } from 'fs';

const config = JSON.parse(readFileSync('.pdv.json', 'utf-8'));
const validator = new PreDeployValidator(config);

const result = await validator.runChecks();
console.log(formatConsoleReport(result));

if (!result.success) {
  process.exit(1);
}
```

## CI/CD Integration

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

## Output

### Console Format
Human-readable terminal output with colors and symbols.

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

### JSON Format
Machine-readable JSON for CI/CD integration.

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
Increase `timeoutMs` for slow operations. Default is 30s for lint, 60s for TypeScript, 120s for tests.

### Coverage threshold not met
Check your test coverage output and adjust `coverageThreshold` values or improve test coverage.

### Build fails for monorepo
Verify all project paths in `projects` array are correct and relative to the current directory.

## Contributing

Contributions are welcome! Please open issues and PRs on [GitHub](https://github.com/TrystPilot/skills).

## License

MIT - See [LICENSE](LICENSE)
