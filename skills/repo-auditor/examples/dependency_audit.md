# Example: Dependency Security Audit

This example demonstrates a focused dependency audit for security vulnerabilities and outdated packages.

## Scenario

Your security team requires a dependency audit before a production release.

## Step 1: Run Dependency Audit

```bash
$ python scripts/audit_dependencies.py /path/to/repo

============================================================
DEPENDENCY AUDIT REPORT
============================================================

Repository: /path/to/repo

----------------------------------------
SUMMARY
----------------------------------------
  Total Dependencies: 89
  Ecosystems: nodejs
  Risk Count: 3
  Critical Risks: 1
  High Risks: 1

----------------------------------------
NPM SECURITY VULNERABILITIES
----------------------------------------
  Total: 12
  Critical: 2
  High: 4
  Moderate: 6

----------------------------------------
RISKS IDENTIFIED
----------------------------------------
  [CRITICAL] Critical npm vulnerabilities found: 2
  [HIGH] High severity npm vulnerabilities found: 4
  [MEDIUM] 15 outdated packages. Consider updating dependencies.
```

## Step 2: Get Detailed Vulnerability Information

```bash
$ npm audit

# npm audit report

lodash  <4.17.21
Severity: critical
Prototype Pollution - https://github.com/advisories/GHSA-jf85-cpcp-j695
fix available via `npm audit fix --force`

minimist  <1.2.6
Severity: critical
Prototype Pollution - https://github.com/advisories/GHSA-xvch-5gv4-984h
fix available via `npm audit fix`

axios  <0.21.2
Severity: high
Server-Side Request Forgery - https://github.com/advisories/GHSA-4w2v-q235-vp99
fix available via `npm audit fix`

... more vulnerabilities ...

12 vulnerabilities (6 moderate, 4 high, 2 critical)
```

## Step 3: Analyze Vulnerability Impact

For each critical/high vulnerability, assess:

1. **Is the vulnerable code path used?**
   ```bash
   # Check if lodash is directly used
   grep -r "require.*lodash\|from.*lodash" src/
   
   # Check specific vulnerable functions
   grep -r "\.template\|\.merge\|\.set" src/ | grep lodash
   ```

2. **Is it a direct or transitive dependency?**
   ```bash
   npm ls lodash
   # Shows dependency tree
   ```

3. **What's the fix complexity?**
   ```bash
   npm audit fix --dry-run
   # Shows what would be changed
   ```

## Step 4: Create Remediation Plan

Based on the audit, prioritize fixes:

### Critical (Fix Immediately)

| Package | Vulnerability | Current | Fixed | Action |
|---------|--------------|---------|-------|--------|
| lodash | Prototype Pollution | 4.17.15 | 4.17.21 | `npm update lodash` |
| minimist | Prototype Pollution | 1.2.0 | 1.2.6 | `npm update minimist` |

### High (Fix This Sprint)

| Package | Vulnerability | Current | Fixed | Action |
|---------|--------------|---------|-------|--------|
| axios | SSRF | 0.19.0 | 0.21.2 | `npm update axios` |
| node-fetch | Header Leak | 2.6.0 | 2.6.7 | `npm update node-fetch` |

### Moderate (Fix Next Sprint)

| Package | Vulnerability | Current | Fixed | Action |
|---------|--------------|---------|-------|--------|
| glob-parent | ReDoS | 5.1.0 | 5.1.2 | `npm update glob-parent` |

## Step 5: Apply Fixes

```bash
# Automatic fix for compatible updates
npm audit fix

# Check remaining issues
npm audit

# For breaking changes, update manually
npm install lodash@latest
npm install axios@latest

# Run tests to verify nothing broke
npm test

# Re-run audit
npm audit
```

## Step 6: Verify Fixes

```bash
$ python scripts/audit_dependencies.py /path/to/repo

============================================================
DEPENDENCY AUDIT REPORT
============================================================

----------------------------------------
SUMMARY
----------------------------------------
  Total Dependencies: 87
  Ecosystems: nodejs
  Risk Count: 0
  Critical Risks: 0
  High Risks: 0

----------------------------------------
NPM SECURITY VULNERABILITIES
----------------------------------------
  Total: 0
```

## Step 7: Document for Security Team

```markdown
# Dependency Security Audit Report

**Date:** 2024-01-15
**Auditor:** DevOps Team
**Status:** PASSED

## Summary
- Initial vulnerabilities: 12
- Remaining vulnerabilities: 0
- All critical and high issues resolved

## Actions Taken
1. Updated lodash 4.17.15 -> 4.17.21 (critical)
2. Updated minimist 1.2.0 -> 1.2.6 (critical)
3. Updated axios 0.19.0 -> 0.21.2 (high)
4. Updated node-fetch 2.6.0 -> 2.6.7 (high)
5. Ran `npm audit fix` for moderate issues

## Testing
- All unit tests passing
- Integration tests passing
- No breaking changes detected

## Recommendations
1. Enable Dependabot for automatic security updates
2. Add `npm audit` to CI pipeline
3. Schedule monthly dependency reviews
```

## Automation: Add to CI Pipeline

```yaml
# .github/workflows/security.yml
name: Security Audit

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]
  schedule:
    - cron: '0 0 * * 1'  # Weekly on Monday

jobs:
  audit:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Setup Node.js
        uses: actions/setup-node@v3
        with:
          node-version: '18'
          
      - name: Install dependencies
        run: npm ci
        
      - name: Run security audit
        run: npm audit --audit-level=high
        
      - name: Check for outdated packages
        run: npm outdated || true
```

## Python Dependency Audit

For Python projects, use similar approach:

```bash
# Install audit tools
pip install pip-audit safety

# Run pip-audit
pip-audit

# Run safety check
safety check -r requirements.txt

# Update vulnerable packages
pip install --upgrade <package>

# Regenerate requirements
pip freeze > requirements.txt
```
