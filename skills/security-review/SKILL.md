---
name: security-review
description: "AI-powered code security scanner that traces data flows, audits dependencies, detects exposed secrets, and finds vulnerabilities across your codebase. TRIGGER when: user asks to scan code for security issues, vulnerabilities, exposed secrets, insecure dependencies, or runs /security-review. Also trigger for: SQL injection, XSS, auth bypass, IDOR, CSRF, command injection, SSRF checks, or any phrasing like 'is my code secure?' or 'audit this repo'. DO NOT TRIGGER when: general code review without security focus, or performance optimization."
license: Complete terms in LICENSE.txt
---

# Security Review

An AI-native security scanner that reasons about your codebase the way a human security
researcher would — tracing data flows, understanding component interactions, and catching
vulnerabilities that pattern-matching tools miss.

---

## Scanning Philosophy

Unlike traditional static analysis tools that match patterns, this skill:
1. **Reads code like a security researcher** — understanding context, intent, and data flow
2. **Traces across files** — following how user input moves through your application
3. **Self-verifies findings** — re-examines each result to filter false positives
4. **Assigns severity ratings** — CRITICAL / HIGH / MEDIUM / LOW / INFO
5. **Proposes targeted patches** — every finding includes a concrete fix
6. **Requires human approval** — nothing is auto-applied; you always review first

---

## Execution Workflow

Follow these steps **in order** every time:

### Step 1 — Scope Resolution
Determine what to scan:
- If a path was provided (`/security-review src/auth/`), scan only that scope
- If no path given, scan the **entire project** starting from the root
- Identify the language(s) and framework(s) in use (check package.json, requirements.txt,
  go.mod, Cargo.toml, pom.xml, Gemfile, composer.json, etc.)
- Read `reference/language-patterns.md` to load language-specific vulnerability patterns

### Step 2 — Dependency Audit
Before scanning source code, audit dependencies first (fast wins):
- **Node.js**: Check `package.json` + `package-lock.json` for known vulnerable packages
- **Python**: Check `requirements.txt` / `pyproject.toml` / `Pipfile`
- **Java**: Check `pom.xml` / `build.gradle`
- **Ruby**: Check `Gemfile.lock`
- **Rust**: Check `Cargo.toml`
- **Go**: Check `go.sum`
- Flag packages with known CVEs, deprecated crypto libs, or suspiciously old pinned versions
- Read `reference/vulnerable-packages.md` for a curated watchlist

### Step 3 — Secrets & Exposure Scan
Scan ALL files (including config, env, CI/CD, Dockerfiles, IaC) for:
- Hardcoded API keys, tokens, passwords, private keys
- `.env` files accidentally committed
- Secrets in comments or debug logs
- Cloud credentials (AWS, GCP, Azure, Stripe, Twilio, etc.)
- Database connection strings with credentials embedded
- Read `reference/secret-patterns.md` for regex patterns and entropy heuristics to apply

### Step 4 — Vulnerability Deep Scan
This is the core scan. Reason about the code — don't just pattern-match.
Read `reference/vuln-categories.md` for full details on each category.

**Injection Flaws**
- SQL Injection: raw queries with string interpolation, ORM misuse, second-order SQLi
- XSS: unescaped output, dangerouslySetInnerHTML, innerHTML, template injection
- Command Injection: exec/spawn/system with user input
- LDAP, XPath, Header, Log injection

**Authentication & Access Control**
- Missing authentication on sensitive endpoints
- Broken object-level authorization (BOLA/IDOR)
- JWT weaknesses (alg:none, weak secrets, no expiry validation)
- Session fixation, missing CSRF protection
- Privilege escalation paths
- Mass assignment / parameter pollution

**Data Handling**
- Sensitive data in logs, error messages, or API responses
- Missing encryption at rest or in transit
- Insecure deserialization
- Path traversal / directory traversal
- XXE (XML External Entity) processing
- SSRF (Server-Side Request Forgery)

**Cryptography**
- Use of MD5, SHA1, DES for security purposes
- Hardcoded IVs or salts
- Weak random number generation (Math.random() for tokens)
- Missing TLS certificate validation

**Business Logic**
- Race conditions (TOCTOU)
- Integer overflow in financial calculations
- Missing rate limiting on sensitive endpoints
- Predictable resource identifiers

### Step 5 — Cross-File Data Flow Analysis
After the per-file scan, perform a **holistic review**:
- Trace user-controlled input from entry points (HTTP params, headers, body, file uploads)
  all the way to sinks (DB queries, exec calls, HTML output, file writes)
- Identify vulnerabilities that only appear when looking at multiple files together
- Check for insecure trust boundaries between services or modules

### Step 6 — Self-Verification Pass
For EACH finding:
1. Re-read the relevant code with fresh eyes
2. Ask: "Is this actually exploitable, or is there sanitization I missed?"
3. Check if a framework or middleware already handles this upstream
4. Downgrade or discard findings that aren't genuine vulnerabilities
5. Assign final severity: CRITICAL / HIGH / MEDIUM / LOW / INFO

### Step 7 — Generate Security Report
Output the full report in the format defined in `reference/report-format.md`.

### Step 8 — Propose Patches
For every CRITICAL and HIGH finding, generate a concrete patch:
- Show the vulnerable code (before)
- Show the fixed code (after)
- Explain what changed and why
- Preserve the original code style, variable names, and structure
- Add a comment explaining the fix inline

Explicitly state: **"Review each patch before applying. Nothing has been changed yet."**

---

## Severity Guide

| Severity | Meaning | Example |
|----------|---------|---------|
| CRITICAL | Immediate exploitation risk, data breach likely | SQLi, RCE, auth bypass |
| HIGH | Serious vulnerability, exploit path exists | XSS, IDOR, hardcoded secrets |
| MEDIUM | Exploitable with conditions or chaining | CSRF, open redirect, weak crypto |
| LOW | Best practice violation, low direct risk | Verbose errors, missing headers |
| INFO | Observation worth noting, not a vulnerability | Outdated dependency (no CVE) |

---

## Guidelines

- **Always** produce a findings summary table first (counts by severity)
- **Never** auto-apply any patch — present patches for human review only
- **Always** include a confidence rating per finding (High / Medium / Low)
- **Group findings** by category, not by file
- **Be specific** — include file path, line number, and the exact vulnerable code snippet
- **Explain the risk** in plain English — what could an attacker do with this?
- If the codebase is clean, say so clearly: "No vulnerabilities found" with what was scanned

---

## Reference Files

- **reference/vuln-categories.md** — Detection guidance for every vulnerability category (injection, auth, data handling, crypto, business logic, path traversal)
- **reference/secret-patterns.md** — Regex patterns and entropy heuristics for detecting API keys, tokens, passwords, private keys, and credentials
- **reference/language-patterns.md** — Framework-specific vulnerability patterns for JavaScript, Python, Java, PHP, Go, Ruby, and Rust
- **reference/vulnerable-packages.md** — CVE watchlist for npm, pip, Maven, Gems, Cargo, and Go packages with safe versions
- **reference/report-format.md** — Structured output template for security scan reports including finding cards, dependency audit, and patch proposals
