---
name: security-scanning
description: Scan code for security vulnerabilities including SQL injection, XSS, secrets exposure, prompt injection, and AI-hallucinated package dependencies using agent-security-scanner-mcp. Use when writing code that handles user input, during code review, before deploying to production, or when adding new package dependencies.
---

# Security Scanning

Scan project code for security vulnerabilities before deployment or during code review.

## When to Use

- After writing new code that handles user input, authentication, or data storage
- During code review to catch vulnerabilities
- Before deploying to production
- When adding new package dependencies (to verify they exist and aren't hallucinated)

## How to Scan

Run the security scanner via npx:

```bash
npx agent-security-scanner-mcp@latest
```

This starts an MCP server that provides these scanning tools:

- **scan_code** - Scan source files for SQL injection, XSS, secrets, and other OWASP Top 10 vulnerabilities
- **check_prompt_security** - Detect prompt injection patterns in LLM-facing code
- **verify_packages** - Check if package dependencies actually exist on npm (catches AI-hallucinated packages)

## Interpreting Results

- **CRITICAL/HIGH** - Fix before merging. These are exploitable vulnerabilities.
- **MEDIUM** - Review and fix if feasible. May require context to assess risk.
- **LOW/INFO** - Informational. Address in follow-up if desired.

## Examples

After implementing an API endpoint:
> "Scan the new /api/users endpoint for SQL injection and XSS vulnerabilities"

Before committing dependency changes:
> "Verify all new packages in package.json are real and not hallucinated"

During code review:
> "Scan the changes in this PR for security issues including secrets exposure"

## Guidelines

- Always scan code that handles user input or sensitive data
- Verify new dependencies before committing
- Treat CRITICAL/HIGH findings as blockers
- Re-scan after fixing to confirm resolution
