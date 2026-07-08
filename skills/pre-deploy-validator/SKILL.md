---
name: pre-deploy-validator
description: "Conducts comprehensive pre-deployment flight checks for agent ability verification"
license: MIT
---

<!--
  pre-deploy-validator — Pre-Deployment Flight Check Skill
  =========================================================
  Runs a suite of automated checks before code is deployed, blocking releases
  that don't meet quality, security, or completeness standards.

  What it checks (all toggleable via config):
    • Code Quality    — runs `npm run lint`; flags linting errors
    • Security        — scans files for hardcoded secrets (API keys, tokens,
                        passwords) using regex patterns
    • Tests           — runs `npm test`; fails if the test suite exits non-zero
    • Dependencies    — runs `npm audit --audit-level=moderate`; warns on
                        known vulnerabilities
    • Documentation   — verifies README.md and LICENSE.txt are present

  Output categories:
    ✅ Passed | ⚠️ Warnings | ❌ Failures | 🔥 Errors

  Exit codes:  0 = all clear  |  1 = failures  |  2 = config error  |  3 = skipped

  Deliverable:
    A structured validation report (console and/or JSON) with:
      - List of passed checks
      - List of warnings (non-blocking issues)
      - List of failures (blocking issues)
      - List of errors (execution errors)
      - Overall status: "READY FOR DEPLOYMENT ✅" or "DEPLOYMENT BLOCKED ❌"
      - Exit code indicating result

  Success metrics:
    - Zero failures and zero errors in the validation report
    - All configured checks complete without throwing
    - Exit code 0 returned by the process
    - Security scan finds no sensitive patterns in tracked files
    - Test suite exits 0
    - No moderate-or-higher vulnerabilities in npm audit

  Quick start (CLI):
    node index.js

  Quick start (programmatic):
    const PreDeployValidator = require('./index');
    const v = new PreDeployValidator({ failOnWarnings: true });
    const { success, results } = await v.validate();

  Config file (.pre-deploy-config.json in repo root):
    { "checks": { "codeQuality": true, "security": true, "tests": true,
                  "dependencies": true, "documentation": true },
      "failOn": ["critical", "high"] }

  Requires: Node.js >= 14

  ── PR / Merge Checklist ──────────────────────────────────────────────────────
  Every PR that modifies this skill MUST complete the following before merging:

  Documentation
    [ ] CHANGELOG.md updated with all changes under the correct version heading
    [ ] RELEASE_NOTES.md updated if this is a version bump
    [ ] README.md (skill-level) reflects any new flags, config options, or behaviour

  Versioning
    [ ] package.json `version` bumped (patch / minor / major per semver)
    [ ] Version in CHANGELOG.md matches package.json

  Tests
    [ ] test.js exists and covers all check types (code quality, security,
        tests, dependencies, documentation)
    [ ] `npm test` passes with exit code 0
    [ ] No test files skipped or commented out

  Roadmap / Planning
    [ ] RELEASE_NOTES.md "What's next" section reviewed and updated
    [ ] Any completed roadmap items marked done; new items added if applicable

  Marketplace & Integration
    [ ] .claude-plugin/marketplace.json still references this skill correctly
    [ ] Root README.md skill table entry is accurate

  Final gate
    [ ] All items above checked off
    [ ] PR comment updated to reflect resolved status
    [ ] No merge until all ❌ items in the PR review comment are cleared
  ──────────────────────────────────────────────────────────────────────────────
-->

# Pre-Deploy Validator

A comprehensive skill for public agents to conduct pre-deployment flight checks, ensuring code quality, security, and deployment readiness.

## Features

### Core Validation Checks
- **Code Quality Analysis**: Lint checks, syntax validation, and code standards
- **Security Scanning**: Detect sensitive patterns, vulnerabilities, and secret leaks
- **Dependency Verification**: Check for vulnerable or outdated dependencies
- **Build Validation**: Verify builds complete successfully with no errors
- **Test Suite Status**: Run and validate all test suites
- **Documentation Completeness**: Ensure proper documentation exists

### Agent-Specific Validations
- **Skill Completeness**: Verify required skill files and structure
- **Marketplace Consistency**: Validate marketplace.json references
- **YAML Frontmatter**: Check skill metadata structure
- **License Compliance**: Verify all required license files

### Deployment Readiness
- **Branch Protection**: Validate against protected branch rules
- **CI/CD Pipeline**: Confirm all checks pass
- **Approval Status**: Track review and approval state
- **Merge Conflicts**: Detect and report merge conflict states

## Usage

### With GitHub Actions
```yaml
- name: Run Pre-Deploy Validator
  uses: pre-deploy-validator@v1
  with:
    check-code-quality: true
    check-security: true
    check-tests: true
    fail-on-warnings: false
```

### With Claude Code Agents
Agents can invoke this skill to:
1. Validate code changes before submission
2. Check deployment prerequisites
3. Generate pre-flight check reports
4. Block deployments on validation failures

## Configuration

Create a `.pre-deploy-config.json` in your repository root:

```json
{
  "checks": {
    "codeQuality": true,
    "security": true,
    "tests": true,
    "dependencies": true,
    "documentation": true
  },
  "failOn": ["critical", "high"],
  "ignorePatterns": [],
  "customValidations": []
}
```

## Validation Rules

### Code Quality
- No linting errors (eslint, pylint, etc.)
- Consistent formatting
- Proper type annotations where applicable

### Security
- No hardcoded secrets or API keys
- No vulnerable dependency versions
- No deprecated security practices

### Tests
- All tests pass
- Minimum code coverage threshold met
- No flaky or skipped tests

### Dependencies
- No known vulnerabilities
- All dependencies up to date
- License compliance verified

## Exit Codes

- `0`: All validations passed
- `1`: Validation failures detected
- `2`: Configuration error
- `3`: Check skipped or not applicable

## Related Skills

- `skill-creator`: Create and validate new skills
- `web-artifacts-builder`: Build and validate web artifacts
- `webapp-testing`: Run comprehensive test suites

## License

See LICENSE.txt for details.
