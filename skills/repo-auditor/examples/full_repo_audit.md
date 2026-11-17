# Example: Full Repository Audit

This example demonstrates a complete repository audit covering tech stack, dependencies, risks, dead code, and unused assets.

## Scenario

You've inherited a legacy codebase and need to understand its health before making changes.

## Step 1: Analyze Tech Stack

```bash
$ python scripts/analyze_tech_stack.py /path/to/repo

============================================================
TECH STACK ANALYSIS REPORT
============================================================

Repository: /path/to/repo

----------------------------------------
LANGUAGES
----------------------------------------
  TypeScript: 245 files
  JavaScript: 52 files
  Python: 18 files
  CSS: 34 files

  Primary Language: TypeScript

----------------------------------------
PACKAGE MANAGERS
----------------------------------------
  Node.js/npm (package.json)
  Python/pip (requirements.txt)

----------------------------------------
FRAMEWORKS
----------------------------------------
  React (from package.json)
  Next.js (from package.json)
  FastAPI (from requirements.txt)

----------------------------------------
BUILD TOOLS
----------------------------------------
  TypeScript Compiler (tsconfig.json)
  Webpack (webpack.config.js)

----------------------------------------
CI/CD
----------------------------------------
  GitHub Actions (.github/workflows)

----------------------------------------
INFRASTRUCTURE
----------------------------------------
  Docker (Dockerfile)
  Docker Compose (docker-compose.yml)

----------------------------------------
CODE QUALITY TOOLS
----------------------------------------
  ESLint (.eslintrc.js)
  Prettier (.prettierrc)
  mypy (mypy.ini)
```

**Key Findings:**
- Full-stack application with TypeScript frontend and Python backend
- Uses Next.js for React SSR
- FastAPI for backend API
- Docker-based deployment
- Good code quality tooling in place

## Step 2: Audit Dependencies

```bash
$ python scripts/audit_dependencies.py /path/to/repo

============================================================
DEPENDENCY AUDIT REPORT
============================================================

Repository: /path/to/repo

----------------------------------------
SUMMARY
----------------------------------------
  Total Dependencies: 156
  Ecosystems: nodejs, python
  Risk Count: 4
  Critical Risks: 1
  High Risks: 2

----------------------------------------
DEPENDENCIES BY ECOSYSTEM
----------------------------------------
  nodejs: 142 packages
  python: 14 packages

----------------------------------------
OUTDATED NPM PACKAGES
----------------------------------------
  Count: 23
  react: 17.0.2 -> 18.2.0 (wanted: 17.0.2)
  next: 12.3.4 -> 14.0.0 (wanted: 12.3.4)
  webpack: 4.46.0 -> 5.89.0 (wanted: 4.46.0)
  ... and 20 more

----------------------------------------
NPM SECURITY VULNERABILITIES
----------------------------------------
  Total: 8
  Critical: 1
  High: 3
  Moderate: 4

----------------------------------------
RISKS IDENTIFIED
----------------------------------------
  [CRITICAL] Critical npm vulnerabilities found: 1
  [HIGH] High severity npm vulnerabilities found: 3
  [MEDIUM] 23 outdated packages. Consider updating dependencies.
  [MEDIUM] High number of dependencies (156). Consider auditing for unused packages.

----------------------------------------
RECOMMENDATIONS
----------------------------------------
  1. Run 'npm audit fix' to fix vulnerabilities automatically
  2. Run 'npm update' to update packages to wanted versions
```

**Key Findings:**
- Critical security vulnerability needs immediate attention
- Many outdated packages (React 17 vs 18, Next.js 12 vs 14)
- High dependency count suggests potential bloat

## Step 3: Find Dead Code

```bash
$ python scripts/find_dead_code.py /path/to/repo

============================================================
DEAD CODE ANALYSIS REPORT
============================================================

Repository: /path/to/repo

----------------------------------------
SUMMARY
----------------------------------------
  Potentially Unused Functions: 12
  Potentially Unused Classes: 3
  Commented Code Blocks: 7
  Languages Analyzed: python, javascript

----------------------------------------
PYTHON ANALYSIS
----------------------------------------

  Potentially Unused Functions:
    - calculate_legacy_price (utils/pricing.py:45)
    - send_old_notification (services/notifications.py:123)
    - validate_v1_token (auth/validators.py:67)

  Potentially Unused Classes:
    - LegacyUserSerializer (serializers/user.py:89)

  Commented Code Blocks:
    - utils/helpers.py:34 (15 lines)
    - services/email.py:78 (8 lines)

----------------------------------------
JAVASCRIPT ANALYSIS
----------------------------------------

  Potentially Unused Functions:
    - formatLegacyDate (src/utils/date.js:23)
    - OldButton (src/components/Button.jsx:45)
    - useDeprecatedHook (src/hooks/legacy.js:12)
    ... and 6 more

----------------------------------------
RECOMMENDATIONS
----------------------------------------
  1. Review each potentially unused item before removing
  2. Check for dynamic usage (reflection, getattr, eval)
  3. Check if functions are called from external packages
  4. Remove commented-out code (use version control instead)
  5. Run tests after removing any code
```

**Key Findings:**
- Several legacy functions that appear unused
- Commented-out code blocks should be removed
- Some "v1" and "legacy" named functions suggest old API versions

## Step 4: Find Unused Assets

```bash
$ python scripts/find_unused_assets.py /path/to/repo

============================================================
UNUSED ASSETS REPORT
============================================================

Repository: /path/to/repo

----------------------------------------
SUMMARY
----------------------------------------
  Unused Images: 8
  Unused Fonts: 2
  Unused npm Dependencies: 5
  Unused pip Dependencies: 2
  Stale Git Branches: 12
  Unused Environment Variables: 3
  Orphaned Config Files: 1
  Wasted Space: 2.4 MB

----------------------------------------
UNUSED IMAGES
----------------------------------------
  public/images/old-logo.png (156.2 KB)
  public/images/banner-v1.jpg (423.8 KB)
  src/assets/unused-icon.svg (12.4 KB)
  ... and 5 more

----------------------------------------
UNUSED NPM DEPENDENCIES
----------------------------------------
  moment
  lodash
  axios
  classnames
  prop-types

  Note: Manual analysis may have false positives.

----------------------------------------
STALE GIT BRANCHES
----------------------------------------
  feature/old-checkout (merged)
  fix/legacy-bug (merged)
  experiment/new-ui (stale, 180 days old)
  ... and 9 more

----------------------------------------
UNUSED ENVIRONMENT VARIABLES
----------------------------------------
  From: .env.example
  OLD_API_KEY
  LEGACY_DATABASE_URL
  DEPRECATED_SERVICE_URL

----------------------------------------
RECOMMENDATIONS
----------------------------------------
  1. Review unused images before deleting
  2. Run 'npm uninstall moment lodash' for unused dependencies
  3. Delete merged branches: git branch -d feature/old-checkout
  4. Clean up unused environment variables from templates
```

**Key Findings:**
- 2.4 MB of wasted space from unused assets
- `moment` and `lodash` can likely be replaced with native JS
- 12 stale branches need cleanup
- Legacy environment variables should be removed

## Step 5: Generate Audit Report

Based on the analysis, create a summary report:

```markdown
# Repository Audit Report

**Repository:** my-legacy-app
**Date:** 2024-01-15
**Auditor:** AI Assistant

## Executive Summary
- Overall health score: 5/10
- Critical issues: 1 (security vulnerability)
- High priority issues: 5
- Recommendations: 12

## Tech Stack
- Primary language: TypeScript
- Framework: Next.js + FastAPI
- Build tool: Webpack
- CI/CD: GitHub Actions
- Infrastructure: Docker

## Dependency Health
- Total dependencies: 156
- Outdated: 23
- Vulnerable: 8 (Critical: 1, High: 3, Moderate: 4)
- License issues: 0

## Code Quality
- Test coverage: Unknown (no coverage reports found)
- Code complexity: Medium
- Documentation: Poor (no README updates in 6 months)

## Dead Code & Unused Assets
- Unused functions: 12
- Unused classes: 3
- Commented code blocks: 7
- Orphaned images: 8 (2.4 MB)
- Unused dependencies: 7

## Risk Assessment
### Security Risks
- Critical npm vulnerability (immediate action required)
- 3 high-severity vulnerabilities

### Maintainability Risks
- Large number of outdated dependencies
- Legacy code patterns (v1, old, deprecated naming)
- 12 stale git branches

### Operational Risks
- No test coverage metrics
- Outdated documentation

## Priority Recommendations
1. **CRITICAL**: Run `npm audit fix --force` to address security vulnerabilities
2. **HIGH**: Update React 17 to 18 and Next.js 12 to 14
3. **HIGH**: Remove unused dependencies (moment, lodash)
4. **MEDIUM**: Delete 12 stale git branches
5. **MEDIUM**: Remove 12 potentially unused functions after verification
6. **MEDIUM**: Clean up 2.4 MB of unused images
7. **LOW**: Remove commented-out code blocks
8. **LOW**: Update .env.example to remove legacy variables
```

## Cleanup Commands

After review, execute cleanup:

```bash
# Fix security vulnerabilities
npm audit fix

# Remove unused npm dependencies
npm uninstall moment lodash axios classnames prop-types

# Delete merged branches
git branch --merged main | grep -v "main\|master" | xargs git branch -d

# Remove unused images (after verification)
rm public/images/old-logo.png
rm public/images/banner-v1.jpg

# Update dependencies
npm update
```

## Verification

After cleanup, re-run the audit:

```bash
python scripts/audit_dependencies.py /path/to/repo
python scripts/find_unused_assets.py /path/to/repo
```

Verify:
- Security vulnerabilities resolved
- Dependency count reduced
- Wasted space reclaimed
- All tests still pass
