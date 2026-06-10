---
name: repo-auditor
description: Comprehensive repository audit skill for analyzing tech stack, dependencies, security risks, code quality, and identifying dead code and unused assets. Provides systematic workflows for dependency audits, vulnerability detection, license compliance, unused code cleanup, and orphaned asset identification.
license: Complete terms in LICENSE.txt
---

# Repository Auditor

This skill provides systematic approaches to audit repositories for tech stack analysis, dependency health, security risks, and code cleanliness. Use the decision trees and scripts to perform comprehensive repository audits.

## Diagnostic Scripts

This skill includes helper scripts for automated analysis:

| Script | Purpose | Usage |
|--------|---------|-------|
| `analyze_tech_stack.py` | Detect languages, frameworks, and build tools | `python scripts/analyze_tech_stack.py <repo-path>` |
| `audit_dependencies.py` | Check for outdated/vulnerable dependencies | `python scripts/audit_dependencies.py <repo-path>` |
| `find_dead_code.py` | Identify unused functions, classes, imports | `python scripts/find_dead_code.py <repo-path>` |
| `find_unused_assets.py` | Find orphaned files and unused assets | `python scripts/find_unused_assets.py <repo-path>` |

**Quick Start:**
```bash
# Full repository audit
python scripts/analyze_tech_stack.py /path/to/repo
python scripts/audit_dependencies.py /path/to/repo
python scripts/find_dead_code.py /path/to/repo
python scripts/find_unused_assets.py /path/to/repo

# With JSON output for programmatic use
python scripts/analyze_tech_stack.py /path/to/repo --json
```

## Example Walkthroughs

See the `examples/` folder for detailed audit scenarios:

- `full_repo_audit.md` - Complete repository audit walkthrough
- `dependency_audit.md` - Dependency-focused security audit
- `dead_code_cleanup.md` - Dead code identification and removal

---

## Part 1: Tech Stack Analysis

### Decision Tree: Identify Tech Stack

```
Repository Analysis
├─ Languages
│   ├─ Check file extensions (.py, .js, .ts, .go, .rs, .java, etc.)
│   ├─ Check shebang lines (#!/usr/bin/env python)
│   └─ Check language-specific configs (.python-version, .nvmrc, .ruby-version)
│
├─ Package Managers & Dependencies
│   ├─ Python: requirements.txt, setup.py, pyproject.toml, Pipfile, poetry.lock
│   ├─ JavaScript/Node: package.json, package-lock.json, yarn.lock, pnpm-lock.yaml
│   ├─ Go: go.mod, go.sum
│   ├─ Rust: Cargo.toml, Cargo.lock
│   ├─ Java: pom.xml, build.gradle, build.gradle.kts
│   ├─ Ruby: Gemfile, Gemfile.lock
│   ├─ PHP: composer.json, composer.lock
│   └─ .NET: *.csproj, packages.config, *.sln
│
├─ Frameworks (check dependencies and config files)
│   ├─ Web: React, Vue, Angular, Svelte, Next.js, Nuxt, Django, Flask, FastAPI, Express, Rails
│   ├─ Mobile: React Native, Flutter, Swift, Kotlin
│   └─ Backend: Spring Boot, .NET Core, Laravel, Gin, Echo
│
├─ Build Tools
│   ├─ JavaScript: webpack.config.js, vite.config.js, rollup.config.js, esbuild
│   ├─ Python: setup.py, pyproject.toml (build-system)
│   ├─ Java: Maven (pom.xml), Gradle (build.gradle)
│   └─ General: Makefile, Taskfile.yml, justfile
│
├─ CI/CD
│   ├─ GitHub Actions: .github/workflows/*.yml
│   ├─ GitLab CI: .gitlab-ci.yml
│   ├─ Jenkins: Jenkinsfile
│   ├─ CircleCI: .circleci/config.yml
│   └─ Travis: .travis.yml
│
├─ Infrastructure
│   ├─ Docker: Dockerfile, docker-compose.yml
│   ├─ Kubernetes: k8s/, kubernetes/, *.yaml with kind: Deployment
│   ├─ Terraform: *.tf, terraform/
│   └─ Serverless: serverless.yml, sam.yaml
│
└─ Code Quality Tools
    ├─ Linters: .eslintrc, .pylintrc, .rubocop.yml, golangci.yml
    ├─ Formatters: .prettierrc, .editorconfig, pyproject.toml [tool.black]
    └─ Type Checkers: tsconfig.json, mypy.ini, pyrightconfig.json
```

### Quick Commands: Tech Stack Detection

```bash
# Find all unique file extensions
find . -type f -name "*.*" | sed 's/.*\.//' | sort | uniq -c | sort -rn | head -20

# List package manager files
find . -name "package.json" -o -name "requirements.txt" -o -name "go.mod" \
       -o -name "Cargo.toml" -o -name "pom.xml" -o -name "Gemfile" 2>/dev/null

# Check for CI/CD configs
ls -la .github/workflows/ .gitlab-ci.yml Jenkinsfile .circleci/ 2>/dev/null

# Check for containerization
ls -la Dockerfile docker-compose.yml k8s/ kubernetes/ 2>/dev/null
```

---

## Part 2: Dependency Analysis

### Decision Tree: Dependency Audit

```
Dependency Health Check
├─ Outdated Dependencies
│   ├─ npm: npm outdated
│   ├─ pip: pip list --outdated
│   ├─ go: go list -u -m all
│   ├─ cargo: cargo outdated
│   └─ maven: mvn versions:display-dependency-updates
│
├─ Security Vulnerabilities
│   ├─ npm: npm audit
│   ├─ pip: pip-audit, safety check
│   ├─ go: govulncheck ./...
│   ├─ cargo: cargo audit
│   ├─ maven: mvn dependency-check:check
│   └─ General: snyk test, trivy fs .
│
├─ License Compliance
│   ├─ npm: license-checker
│   ├─ pip: pip-licenses
│   ├─ go: go-licenses
│   └─ General: fossa analyze, licensee
│
├─ Dependency Size/Bloat
│   ├─ npm: npm ls --all | wc -l (count deps)
│   ├─ Check for duplicate dependencies
│   └─ Identify heavy dependencies (bundle analysis)
│
└─ Dependency Freshness
    ├─ Check last update dates
    ├─ Check if dependencies are maintained
    └─ Check for deprecated packages
```

### Quick Commands: Dependency Audit

```bash
# JavaScript/Node
npm outdated                    # Check outdated packages
npm audit                       # Security vulnerabilities
npm ls --all | wc -l           # Count all dependencies
npx depcheck                    # Find unused dependencies

# Python
pip list --outdated            # Check outdated packages
pip-audit                      # Security vulnerabilities (install: pip install pip-audit)
pipdeptree                     # Dependency tree visualization

# Go
go list -u -m all              # Check for updates
govulncheck ./...              # Security vulnerabilities
go mod why <package>           # Why is this dependency needed?

# Rust
cargo outdated                 # Check outdated packages
cargo audit                    # Security vulnerabilities
cargo tree                     # Dependency tree

# General (requires installation)
snyk test                      # Multi-language vulnerability scanner
trivy fs .                     # Filesystem vulnerability scanner
```

---

## Part 3: Risk Assessment

### Decision Tree: Risk Identification

```
Risk Categories
├─ Security Risks
│   ├─ Hardcoded secrets → Check for API keys, passwords, tokens
│   │   └─ Tools: git-secrets, trufflehog, gitleaks
│   ├─ Vulnerable dependencies → Run security scanners
│   ├─ Insecure configurations → Check for debug mode, weak crypto
│   └─ Missing security headers → Check web configs
│
├─ Code Quality Risks
│   ├─ High complexity → Check cyclomatic complexity
│   │   └─ Tools: radon (Python), complexity-report (JS), gocyclo (Go)
│   ├─ Low test coverage → Check coverage reports
│   │   └─ Tools: coverage.py, nyc/istanbul, go test -cover
│   ├─ Code duplication → Find copy-pasted code
│   │   └─ Tools: jscpd, PMD CPD, flay (Ruby)
│   └─ Missing documentation → Check doc coverage
│
├─ Maintainability Risks
│   ├─ Large files (>500 lines) → Hard to maintain
│   ├─ Deep nesting (>4 levels) → Hard to understand
│   ├─ Long functions (>50 lines) → Should be split
│   └─ Too many parameters (>5) → Consider refactoring
│
├─ Operational Risks
│   ├─ No CI/CD → Manual deployments are error-prone
│   ├─ No monitoring/logging → Hard to debug production issues
│   ├─ No backup strategy → Data loss risk
│   └─ Single points of failure → Availability risk
│
└─ Dependency Risks
    ├─ Unmaintained dependencies → Check last commit date
    ├─ Single-maintainer dependencies → Bus factor risk
    ├─ Copyleft licenses → May require source disclosure
    └─ Transitive vulnerabilities → Deep dependency issues
```

### Quick Commands: Risk Detection

```bash
# Find potential secrets
grep -rn "password\|secret\|api_key\|token" --include="*.py" --include="*.js" --include="*.env"
git log -p | grep -i "password\|secret\|api_key" | head -20

# Find large files
find . -name "*.py" -o -name "*.js" -o -name "*.ts" | xargs wc -l | sort -rn | head -20

# Find TODO/FIXME comments (technical debt)
grep -rn "TODO\|FIXME\|HACK\|XXX" --include="*.py" --include="*.js" --include="*.ts"

# Check for debug/development settings
grep -rn "DEBUG.*=.*True\|debug.*:.*true" --include="*.py" --include="*.js" --include="*.json"
```

---

## Part 4: Dead Code Detection

### Decision Tree: Find Dead Code

```
Dead Code Types
├─ Unused Imports
│   ├─ Python: pylint --disable=all --enable=W0611
│   ├─ JavaScript: eslint --rule 'no-unused-vars: error'
│   ├─ Go: go vet (built-in, errors on unused imports)
│   └─ TypeScript: tsc --noUnusedLocals
│
├─ Unused Functions/Methods
│   ├─ Search for function definitions
│   ├─ Search for function calls
│   ├─ Compare: defined but never called = potentially dead
│   └─ Caution: May be called dynamically or via reflection
│
├─ Unused Variables
│   ├─ Python: pylint --disable=all --enable=W0612
│   ├─ JavaScript: eslint --rule 'no-unused-vars: error'
│   ├─ Go: go vet (built-in, errors on unused variables)
│   └─ TypeScript: tsc --noUnusedLocals --noUnusedParameters
│
├─ Unused Classes/Types
│   ├─ Search for class definitions
│   ├─ Search for instantiations and type references
│   └─ Compare: defined but never used = potentially dead
│
├─ Unreachable Code
│   ├─ Code after return/throw/break/continue
│   ├─ Conditions that are always true/false
│   └─ Tools: Most linters detect this automatically
│
└─ Commented-Out Code
    ├─ Large blocks of commented code
    ├─ Should be removed (use version control instead)
    └─ Pattern: Multi-line comments containing code syntax
```

### Quick Commands: Dead Code Detection

```bash
# Python - Find unused imports and variables
pylint --disable=all --enable=W0611,W0612 *.py
vulture .                      # Finds unused code (install: pip install vulture)

# JavaScript/TypeScript
npx eslint . --rule 'no-unused-vars: error'
npx ts-prune                   # Find unused exports (TypeScript)

# Go (built-in strict checking)
go vet ./...                   # Errors on unused imports/variables
staticcheck ./...              # Additional static analysis

# Find potentially unused functions (manual search)
# List all function definitions
grep -rn "^def \|^async def " --include="*.py" | cut -d: -f3 | sed 's/def //' | sed 's/(.*$//'

# Find commented-out code blocks
grep -rn "^#.*def \|^#.*class \|^#.*function\|^//.*function" --include="*.py" --include="*.js"
```

---

## Part 5: Unused Asset Detection

### Decision Tree: Find Unused Assets

```
Unused Asset Types
├─ Orphaned Files
│   ├─ Images not referenced in code/HTML/CSS
│   ├─ Config files for removed features
│   ├─ Test fixtures no longer used
│   └─ Documentation for deleted code
│
├─ Unused Dependencies
│   ├─ npm: npx depcheck
│   ├─ pip: pip-extra-reqs (check for unused requirements)
│   ├─ Manually: Search for import statements
│   └─ Compare: installed but never imported = unused
│
├─ Stale Branches
│   ├─ Merged but not deleted
│   ├─ Abandoned (no commits in 6+ months)
│   └─ Command: git branch --merged | grep -v main
│
├─ Unused Environment Variables
│   ├─ Defined in .env but not used in code
│   ├─ Search: grep for each env var name
│   └─ Compare: defined but not referenced = unused
│
├─ Orphaned Database Migrations
│   ├─ Migration files for dropped tables
│   ├─ Rollback migrations never used
│   └─ Check migration history vs current schema
│
└─ Unused Static Assets
    ├─ CSS classes not used in HTML/JSX
    ├─ JavaScript files not imported
    ├─ Images not referenced anywhere
    └─ Fonts not used in stylesheets
```

### Quick Commands: Unused Asset Detection

```bash
# Find unused npm dependencies
npx depcheck

# Find unused images (check if referenced)
for img in $(find . -name "*.png" -o -name "*.jpg" -o -name "*.svg"); do
  basename=$(basename "$img")
  if ! grep -rq "$basename" --include="*.html" --include="*.js" --include="*.jsx" --include="*.tsx" --include="*.css" .; then
    echo "Potentially unused: $img"
  fi
done

# Find stale git branches
git branch --merged main | grep -v "main\|master"  # Merged branches
git for-each-ref --sort=-committerdate refs/heads/ --format='%(committerdate:short) %(refname:short)' | tail -20  # Old branches

# Find unused environment variables
for var in $(grep -oP '^\w+(?==)' .env 2>/dev/null); do
  if ! grep -rq "$var" --include="*.py" --include="*.js" --include="*.ts" .; then
    echo "Potentially unused env var: $var"
  fi
done

# Find unused CSS classes (basic check)
npx purgecss --css src/**/*.css --content src/**/*.html src/**/*.jsx --output unused-css-report
```

---

## Audit Report Template

When performing a repository audit, document findings in this format:

```markdown
# Repository Audit Report

**Repository:** [name]
**Date:** [date]
**Auditor:** [name/agent]

## Executive Summary
- Overall health score: [1-10]
- Critical issues: [count]
- Recommendations: [count]

## Tech Stack
- Primary language: [language]
- Framework: [framework]
- Build tool: [tool]
- CI/CD: [platform]

## Dependency Health
- Total dependencies: [count]
- Outdated: [count]
- Vulnerable: [count] (Critical: X, High: Y, Medium: Z)
- License issues: [count]

## Code Quality
- Test coverage: [percentage]
- Code complexity: [low/medium/high]
- Documentation: [poor/fair/good]

## Dead Code & Unused Assets
- Unused imports: [count]
- Unused functions: [count]
- Orphaned files: [count]
- Unused dependencies: [count]

## Risk Assessment
- Security risks: [list]
- Maintainability risks: [list]
- Operational risks: [list]

## Recommendations
1. [Priority 1 recommendation]
2. [Priority 2 recommendation]
3. [Priority 3 recommendation]
```

---

## Best Practices

1. **Start with automated tools** - Run linters and scanners before manual review to catch obvious issues quickly.

2. **Verify before deleting** - Dead code detection has false positives. Check for dynamic usage, reflection, and external callers before removing code.

3. **Check git history** - Before removing "unused" code, check when it was last modified and why it might exist.

4. **Document findings** - Create an audit report even for small repos. It helps track improvements over time.

5. **Prioritize by risk** - Fix security vulnerabilities and critical bugs before cosmetic issues.

6. **Automate recurring audits** - Set up CI jobs to run dependency audits and linting on every PR.

7. **Consider backwards compatibility** - Unused exports might be used by external consumers. Check before removing.

8. **Test after cleanup** - After removing dead code, run the full test suite to catch any missed dependencies.
