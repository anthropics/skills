---
name: flyai-env-guardian
description: "Protect sensitive environment variables from accidental exposure in commits, logs, and CI pipelines with automated scanning and pre-commit validation."
version: 1.0.0
author: dingtom336-gif
license: MIT
tags: [security, environment, secrets, ci-cd, devops]
allowedTools: [Bash, Read, Grep, Glob]
---

# FlyAI Env Guardian

Automated environment variable protection for development teams. Scans codebases for exposed secrets, validates .env file hygiene, and prevents accidental credential leaks before they reach version control.

## When to use

Activate this skill when:
- A developer is about to commit changes that may contain secrets or API keys
- Setting up a new project and need to establish .env security patterns
- Auditing an existing codebase for exposed credentials
- Configuring CI/CD pipelines that handle sensitive environment variables
- Reviewing pull requests for potential secret exposure

## Threat Model

### High Risk Patterns

| Pattern | Example | Risk Level |
|---------|---------|------------|
| Hardcoded API keys | const KEY = sk-proj-abc123 | Critical |
| Database URLs with passwords | postgres://user:pass@host/db | Critical |
| AWS credentials in code | AWS_SECRET_ACCESS_KEY = ... | Critical |
| JWT secrets | JWT_SECRET = mysecret | High |
| Private keys | BEGIN RSA PRIVATE KEY | Critical |
| OAuth tokens | github_pat_..., ghp_..., gho_... | High |

### Medium Risk Patterns

| Pattern | Example | Risk Level |
|---------|---------|------------|
| Internal URLs | http://internal-api.corp:8080 | Medium |
| IP addresses with ports | 192.168.1.100:3306 | Medium |
| Email addresses in config | admin@company.com | Low |

## Scanning Process

1. Pre-commit scan: Check staged files for secret patterns using regex matching
2. File extension filter: Focus on source code files (.ts, .js, .py, .go, .rs, .java, .env*)
3. Entropy analysis: Flag high-entropy strings (potential random tokens) in non-test files
4. Known pattern matching: Check against 40+ known secret formats (AWS, GCP, Azure, Stripe, Twilio, etc.)
5. .gitignore validation: Ensure .env files are properly ignored
6. History scan: Optional deep scan of git history for previously committed secrets

## Remediation Actions

When secrets are found:

### Immediate
- Block the commit with a clear error message
- Show exactly which file and line contains the secret
- Suggest moving the value to .env and using process.env

### Follow-up
- If a secret was already committed, recommend rotating the credential immediately
- Generate a .env.example file with placeholder values
- Add missing entries to .gitignore
- Set up git-secrets or pre-commit hooks for ongoing protection

## Environment File Standards

### Required Structure
- .env: Local development values (never committed)
- .env.example: Template with placeholder values (committed)
- .env.test: Test environment values (committed, no real secrets)
- .env.production: Production values (never committed, managed by CI/CD)

### Naming Conventions
- Use UPPER_SNAKE_CASE for all variable names
- Prefix with service name: DATABASE_URL, REDIS_HOST, STRIPE_SECRET_KEY
- Document each variable with inline comments
- Group related variables with section headers

## CI/CD Integration

### GitHub Actions
- Validate that no .env files are included in the build artifact
- Check that all required env vars are set in the workflow
- Scan PR diffs for new secret introductions

### Docker
- Never use ENV for secrets in Dockerfiles
- Use Docker secrets or mount .env at runtime
- Scan built images for embedded credentials

## Configuration

The skill respects a .envguardian.json config file:
- customPatterns: Additional regex patterns to scan for
- ignoreFiles: Paths to exclude from scanning
- severityThreshold: Minimum severity to report (low, medium, high, critical)
- autoFix: Whether to automatically add .gitignore entries
