---
name: security-audit
description: Perform comprehensive security audits on codebases, identifying vulnerabilities, dependency risks, and secrets exposure. Use when asked to review code for security issues, check for vulnerabilities, audit dependencies, scan for hardcoded secrets, assess OWASP Top 10 compliance, or evaluate the security posture of an application. Trigger on security review, vulnerability scan, security audit, pentest prep, OWASP check, dependency audit, secrets scan, threat modeling, or when the user mentions security concerns about their code.
license: Complete terms in LICENSE.txt
---

# Security Audit

Perform structured security audits on codebases to identify vulnerabilities, supply chain risks, exposed secrets, and common security anti-patterns. The audit produces actionable findings with severity ratings, file locations, and remediation guidance.

A security audit is not a penetration test -- it is a systematic review of source code and configuration to surface risks before they reach production. The value comes from being thorough and methodical rather than rushing to report the first issue found.

## Audit Workflow

The audit follows four phases. Each phase builds on the previous one, so work through them in order. Depending on the scope the user requests, some phases may be abbreviated -- a "quick scan for secrets" does not need a full dependency audit, for example. Use judgment about what the user actually needs.

---

### Phase 1: Reconnaissance

Before looking for specific vulnerabilities, understand what the codebase does and where its attack surface lies. This context prevents false positives and helps prioritize findings by actual risk rather than theoretical severity.

**Map the technology stack:**
- Identify languages, frameworks, and build systems in use
- Check for manifest files: `package.json`, `requirements.txt`, `Cargo.toml`, `go.mod`, `Gemfile`, `pom.xml`, `build.gradle`, etc.
- Note which web frameworks are present (Express, Django, Rails, Spring, etc.) since each has framework-specific security patterns

**Identify entry points and trust boundaries:**
- API route definitions and endpoint handlers
- CLI argument parsers and stdin readers
- File upload handlers and file system interactions
- Database query construction points
- WebSocket handlers and real-time endpoints
- Message queue consumers and event handlers
- Cron jobs and scheduled tasks

**Trace data flows:**
- Follow user-controlled input from entry points through to sensitive operations (database writes, shell commands, file system access, outbound HTTP requests)
- Identify where input validation and sanitization occur -- or where they are missing
- Note any trust boundary crossings (e.g., client-to-server, server-to-database, service-to-service)

**Document authentication and authorization:**
- How are users authenticated? (session cookies, JWTs, API keys, OAuth)
- Where are authorization checks enforced? (middleware, per-route, per-function)
- Are there admin or elevated-privilege endpoints?
- Is there multi-tenancy? How is tenant isolation enforced?

Record findings from this phase as context for the subsequent phases. Even if no vulnerabilities are found during reconnaissance, the mapping work makes the rest of the audit far more efficient.

---

### Phase 2: Dependency Audit

Third-party dependencies are one of the most common vectors for supply chain attacks. Audit them before diving into first-party code, since a vulnerable dependency can undermine even well-written application code.

**Check for known vulnerabilities:**

Use the package manager's built-in audit tool when available:

```bash
# Node.js / npm
npm audit

# Node.js / yarn
yarn audit

# Python
pip audit

# Ruby
bundle audit check --update

# Go
govulncheck ./...

# Rust
cargo audit

# PHP
composer audit
```

If the project uses a language without a built-in audit command, check the lock file against public vulnerability databases (NVD, GitHub Advisory Database, OSV) by searching for the dependency names and versions.

**Evaluate dependency hygiene:**
- Flag unpinned or loosely pinned versions (`*`, `latest`, `>=` without upper bound) -- these can silently pull in breaking or malicious updates
- Check whether lock files (`package-lock.json`, `yarn.lock`, `Pipfile.lock`, `Cargo.lock`, `go.sum`) exist and are committed -- missing lock files mean builds are not reproducible
- Look for vendored dependencies and verify they match their upstream sources
- Identify dependencies that appear abandoned (no commits in 2+ years, unaddressed security issues, archived repositories)

**Assess supply chain risk:**
- Flag dependencies with very low download counts combined with broad permissions -- potential typosquatting targets
- Note dependencies that request unusual system-level access for their stated purpose
- Check for post-install scripts that execute arbitrary code during installation

Summarize dependency findings separately from code findings. Dependency vulnerabilities often have straightforward remediations (version bumps) and can be addressed quickly.

---

### Phase 3: Code Analysis

This is the core of the audit. Systematically examine the codebase for vulnerability classes, working through each category rather than doing a single unstructured pass. The categories below cover the OWASP Top 10 and additional common vulnerability classes.

**Injection (SQL, NoSQL, Command, LDAP, XPath):**
- Search for string concatenation or template literals in database queries
- Look for raw SQL queries that embed user input directly
- Check for ORM methods that accept raw query fragments
- Find shell command construction using functions that invoke a shell interpreter with user-influenced arguments
- Search for dynamic code evaluation (`eval()`, `Function()`, Python `exec()`, Ruby `instance_eval`) with user-influenced arguments
- Verify that parameterized queries or prepared statements are used consistently

**Cross-Site Scripting (XSS):**
- Identify where user input is rendered in HTML responses
- Check whether the templating engine auto-escapes output (Jinja2, React JSX, and Go html/template do by default; EJS, Pug, and raw string templates do not)
- Search for explicit bypass of escaping: `| safe` in Jinja2, `dangerouslySetInnerHTML` in React, `{!! !!}` in Blade, `v-html` in Vue
- Look for user input reflected in JavaScript contexts, HTML attributes, URLs, and CSS values -- each requires different encoding
- Check Content Security Policy headers if applicable

**Authentication and Session Management:**
- Verify passwords are hashed with a modern algorithm (bcrypt, scrypt, Argon2) -- not MD5, SHA-1, or plain SHA-256
- Check for timing-safe comparison on authentication tokens
- Look for session fixation vulnerabilities (session ID not regenerated after login)
- Verify session tokens have appropriate expiry, and that logout actually invalidates server-side state
- Check for credential exposure in logs, error messages, or URL parameters
- Verify rate limiting on authentication endpoints

**Broken Access Control:**
- Look for authorization checks that rely solely on client-side enforcement
- Check for Insecure Direct Object References (IDOR): can a user access another user's resources by changing an ID in the URL or request body?
- Verify that role-based or attribute-based access control is enforced consistently, not just on some endpoints
- Check for path traversal in file serving: `../../etc/passwd` patterns
- Look for missing authorization checks on state-changing operations (PUT, POST, DELETE)

**Secrets and Credential Exposure:**
- Search for hardcoded API keys, tokens, passwords, and connection strings in source code
- Common patterns to look for:
  - `password = "..."`, `api_key = "..."`, `secret = "..."`
  - `Authorization: Bearer ...` with a literal token value
  - AWS access keys: strings matching `AKIA[0-9A-Z]{16}`
  - Private keys: `-----BEGIN RSA PRIVATE KEY-----` and similar PEM headers
  - Connection strings with embedded credentials: `://user:password@host`
  - Base64-encoded JWT tokens: strings starting with `eyJ`
- Check `.env` files, configuration files, and CI/CD definitions for committed secrets
- Verify that `.gitignore` excludes sensitive files (`.env`, `*.pem`, `*.key`, credentials files)
- Check git history for secrets that were committed and then removed -- they are still in the repository

**Cryptography:**
- Flag use of deprecated algorithms: MD5, SHA-1 for security purposes, DES, 3DES, RC4, ECB mode
- Check that random number generation uses cryptographically secure sources (`crypto.randomBytes`, `secrets` module, `/dev/urandom`) rather than `Math.random()` or language-level `random` for security-sensitive values
- Verify TLS configuration: minimum version, cipher suites, certificate validation
- Check for hardcoded encryption keys or initialization vectors

**Insecure Deserialization:**
- Search for deserialization of untrusted data: `pickle.loads()`, `yaml.load()` (without `SafeLoader`), Java `ObjectInputStream`, PHP `unserialize()`
- Check for prototype pollution in JavaScript (deep merge of user-controlled objects)

**Server-Side Request Forgery (SSRF):**
- Find places where the server makes HTTP requests to URLs influenced by user input
- Check for URL validation: is it allowlist-based? Blocklist approaches (blocking `localhost`, `127.0.0.1`) are typically bypassable
- Look for internal service URLs or cloud metadata endpoints (`169.254.169.254`) that could be reached through SSRF

**Race Conditions and TOCTOU:**
- Identify check-then-act patterns where the check and the action are not atomic
- Look for financial operations (balance checks, inventory counts) without proper locking
- Check for file system operations where existence checks are separate from file operations
- Note any shared mutable state accessed from concurrent handlers without synchronization

**Security Misconfiguration:**
- Check for debug mode enabled in production configurations
- Look for overly permissive CORS settings (`Access-Control-Allow-Origin: *` with credentials)
- Verify that error responses do not leak stack traces, internal paths, or database schema details
- Check for missing security headers: `Strict-Transport-Security`, `X-Content-Type-Options`, `X-Frame-Options`
- Review Dockerfile or container configurations for running as root, exposed ports, or unnecessary packages

**Logging and Monitoring:**
- Check whether authentication events (login, logout, failed attempts) are logged
- Verify that sensitive data (passwords, tokens, PII) is not written to logs
- Look for log injection vulnerabilities (user input written to logs without sanitization)

---

### Phase 4: Report

Present findings in a structured format that makes it easy to prioritize and act on them. The report has two parts: a summary table for quick triage and detailed findings for remediation.

**Summary Table:**

Start the report with a severity breakdown:

```
| Severity | Count |
|----------|-------|
| Critical |     X |
| High     |     X |
| Medium   |     X |
| Low      |     X |
| Info     |     X |
```

**Detailed Findings:**

Group findings by severity (critical first), then by category within each severity level. For each finding, include:

```
### [SEVERITY] Category: Short Title

**File:** `path/to/file.ext` (line N)
**Confidence:** High | Medium
**Category:** Injection | XSS | Auth | Access Control | Secrets | Crypto | Deserialization | SSRF | Race Condition | Misconfiguration | Dependency | ...

**Description:**
What the vulnerability is and why it matters in this specific codebase. Reference the actual code pattern found, not a generic description.

**Evidence:**
The specific code snippet or pattern that triggered this finding.

**Remediation:**
Concrete steps to fix this specific instance. Include a code example of the fix when practical.
```

**Confidence threshold:** Only include findings where you are reasonably confident the issue is real. If something looks suspicious but you cannot confirm it is exploitable from the source code alone, note it as an informational finding rather than inflating severity. False positives erode trust in the audit.

**Severity definitions:**
- **Critical**: Directly exploitable for remote code execution, authentication bypass, or mass data exposure. Fix immediately.
- **High**: Exploitable vulnerability that requires some preconditions (e.g., authenticated attacker, specific configuration). Fix before next release.
- **Medium**: Vulnerability that requires significant preconditions to exploit, or a security weakness that increases risk without being directly exploitable. Plan remediation.
- **Low**: Minor security concern, defense-in-depth improvement, or best practice violation. Address when convenient.
- **Info**: Observation about security posture that does not represent a specific vulnerability. No action required.

**Closing the report:**

End with a brief summary paragraph noting the overall security posture, the most significant risks found, and any areas that could not be fully assessed from source code alone (e.g., runtime configuration, infrastructure, or network-level controls).

---

## Scope Adjustments

Not every audit needs all four phases at full depth. Adjust based on what the user requests:

- **"Quick security scan"** -- Focus on Phase 3 (secrets, injection, and obvious misconfigurations). Skip deep dependency analysis.
- **"Dependency audit"** -- Focus on Phase 2. Briefly scan Phase 3 for secrets.
- **"Check for secrets"** -- Search for credential patterns in Phase 3. Report findings directly.
- **"Full security audit"** -- All four phases at full depth.
- **"OWASP Top 10 review"** -- Phase 1 for context, then Phase 3 covering all OWASP categories. Include Phase 2 for "Vulnerable and Outdated Components" (A06:2021).

When in doubt about scope, start with the full workflow and let the size of the codebase and the user's time constraints guide how deep to go.

## Tips for Effective Audits

- **Read configuration files early.** Framework configuration (Django `settings.py`, Express middleware setup, Spring `application.properties`) often reveals security posture faster than scanning individual source files.
- **Follow the data.** The most impactful vulnerabilities sit along data flow paths from user input to sensitive operations. Trace these paths rather than scanning files alphabetically.
- **Check tests for security assumptions.** Test files sometimes reveal security expectations that are not enforced in the main code. They also sometimes contain hardcoded credentials used for test fixtures.
- **Look at error handling.** Poor error handling (catching all exceptions silently, returning stack traces, inconsistent error responses) is a strong signal of broader security issues.
- **Consider the deployment context.** A vulnerability in a local-only CLI tool has different impact than the same pattern in a public-facing web service. Adjust severity accordingly.
