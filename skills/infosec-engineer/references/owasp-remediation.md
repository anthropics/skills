# OWASP Top 10 Detailed Remediation Guide

## Table of Contents
- [A01: Broken Access Control](#a01-broken-access-control)
- [A02: Cryptographic Failures](#a02-cryptographic-failures)
- [A03: Injection](#a03-injection)
- [A04: Insecure Design](#a04-insecure-design)
- [A05: Security Misconfiguration](#a05-security-misconfiguration)
- [A06: Vulnerable and Outdated Components](#a06-vulnerable-and-outdated-components)
- [A07: Identification and Authentication Failures](#a07-identification-and-authentication-failures)
- [A08: Software and Data Integrity Failures](#a08-software-and-data-integrity-failures)
- [A09: Security Logging and Monitoring Failures](#a09-security-logging-and-monitoring-failures)
- [A10: Server-Side Request Forgery (SSRF)](#a10-server-side-request-forgery-ssrf)

---

## A01: Broken Access Control

### Vulnerabilities
- Missing authorization checks on API endpoints
- IDOR (Insecure Direct Object Reference) — accessing other users' data by changing IDs
- Privilege escalation — normal user performing admin actions
- CORS misconfiguration allowing unauthorized origins
- Metadata manipulation (JWT tampering, cookie modification)

### Remediation

**Server-side enforcement (mandatory):**
```
Every API endpoint MUST check:
1. Is the user authenticated?
2. Is the user authorized for THIS specific resource?
3. Is the user authorized for THIS specific action?
```

**Implementation patterns:**
- Deny by default — explicitly grant access, don't explicitly deny
- Use RBAC (Role-Based Access Control) or ABAC (Attribute-Based Access Control)
- Validate resource ownership server-side: `WHERE user_id = current_user.id`
- Disable directory listing on web servers
- Rate-limit API endpoints to slow enumeration attacks
- Log all access control failures for monitoring

**CORS configuration:**
- Never use `Access-Control-Allow-Origin: *` with credentials
- Allowlist specific trusted origins
- Validate the `Origin` header server-side

---

## A02: Cryptographic Failures

### Vulnerabilities
- Sensitive data transmitted over HTTP (not HTTPS)
- Weak algorithms: MD5, SHA1, DES, RC4
- Passwords stored as plaintext or with weak hashing
- Hardcoded encryption keys
- Missing encryption for data at rest

### Remediation

**Data in transit:**
- TLS 1.2+ for all connections (disable TLS 1.0, 1.1, SSL)
- HSTS header: `Strict-Transport-Security: max-age=31536000; includeSubDomains`
- Certificate pinning for mobile apps (optional, high security)

**Data at rest:**
- AES-256-GCM or ChaCha20-Poly1305 for symmetric encryption
- RSA-2048+ or Ed25519 for asymmetric operations
- Encrypt database columns containing PII or sensitive data
- Use envelope encryption: data key encrypts data, master key encrypts data key

**Password storage:**
- Use Argon2id (preferred), bcrypt, or scrypt
- Never MD5, SHA1, SHA256, or plain SHA512 for passwords
- Salt is automatically handled by bcrypt/Argon2
- Minimum parameters: bcrypt cost factor 12+, Argon2id memory 64MB+

**Key management:**
- Use cloud KMS (AWS KMS, GCP Cloud KMS, Azure Key Vault)
- Rotate keys periodically (at least annually)
- Never hardcode keys in source code
- Separate key management from data storage

---

## A03: Injection

### Vulnerabilities
- SQL injection via string concatenation in queries
- NoSQL injection via unsanitized operators
- Command injection via shell execution with user input
- LDAP injection, XPath injection
- XSS (Cross-Site Scripting) via unescaped output

### Remediation

**SQL Injection:**
```
NEVER: query = "SELECT * FROM users WHERE id = " + user_input
ALWAYS: query = "SELECT * FROM users WHERE id = ?", [user_input]
```
- Use parameterized queries / prepared statements
- Use an ORM (adds a layer of protection, but not foolproof)
- Validate input types (if expecting an integer, parse as integer)

**XSS Prevention:**
- Escape all output by default (most frameworks do this)
- Use Content-Security-Policy header to restrict script sources
- Use `HttpOnly` and `Secure` flags on cookies
- Sanitize HTML input with an allowlist-based sanitizer (not a blocklist)
- Avoid `innerHTML`, `eval()`, `document.write()`

**Command Injection:**
- Avoid executing shell commands with user input
- If necessary, use parameterized APIs (not string interpolation)
- Validate input against a strict allowlist
- Use language-native libraries instead of shell commands

---

## A04: Insecure Design

### Vulnerabilities
- Missing threat model
- No abuse case testing
- Business logic flaws (e.g., negative quantities in shopping cart)
- Missing rate limiting on sensitive operations
- No security requirements in design phase

### Remediation
- Perform threat modeling during design (STRIDE framework)
- Write abuse cases alongside use cases
- Implement business logic validation server-side
- Design for least privilege from the start
- Conduct security design reviews before implementation
- Use secure design patterns (e.g., input validation, output encoding, parameterized queries)

---

## A05: Security Misconfiguration

### Vulnerabilities
- Default credentials left active
- Unnecessary features enabled (directory listing, admin consoles)
- Verbose error messages exposing stack traces
- Missing security headers
- Cloud storage with public access
- Outdated software with known vulnerabilities

### Remediation
- Automate configuration with IaC (Terraform, Ansible)
- Hardened baseline configurations for each component
- Remove all default accounts and passwords
- Disable unused features, ports, and services
- Configure security headers (CSP, HSTS, X-Content-Type-Options, X-Frame-Options)
- Regular configuration audits (automated scanning)
- Separate development, staging, and production configurations

---

## A06: Vulnerable and Outdated Components

### Vulnerabilities
- Dependencies with known CVEs
- Unmaintained or abandoned libraries
- Using components without understanding their security posture

### Remediation
- Maintain a Software Bill of Materials (SBOM)
- Run SCA (Software Composition Analysis) in CI/CD
- Subscribe to CVE feeds for critical dependencies
- Pin dependency versions in lockfiles
- Schedule regular dependency updates (weekly automated PRs)
- Remove unused dependencies
- Evaluate new dependencies before adoption (maintenance status, security track record)

---

## A07: Identification and Authentication Failures

### Vulnerabilities
- Brute force attacks on login endpoints
- Credential stuffing from breached databases
- Weak password requirements
- Missing MFA
- Session fixation or poor session management

### Remediation
- Implement rate limiting on authentication endpoints
- Account lockout after N failed attempts (with progressive delays)
- Require MFA for sensitive operations and admin access
- Use secure session management (random IDs, short TTL, invalidate on logout)
- Check passwords against known breached password lists (HaveIBeenPwned API)
- Don't reveal whether username or password was incorrect ("Invalid credentials")
- Implement secure password reset (time-limited tokens, invalidate after use)

---

## A08: Software and Data Integrity Failures

### Vulnerabilities
- Unsigned updates or packages
- CI/CD pipeline tampering
- Deserialization of untrusted data
- Dependencies from untrusted sources

### Remediation
- Verify digital signatures on all software updates
- Use lockfiles and verify checksums for dependencies
- Implement CI/CD integrity controls (signed commits, protected branches)
- Avoid deserializing untrusted data; if necessary, use safe deserialization libraries
- Use Subresource Integrity (SRI) for CDN-hosted scripts
- Implement code review requirements for all changes to CI/CD pipelines

---

## A09: Security Logging and Monitoring Failures

### Vulnerabilities
- Login failures not logged
- Authorization failures not logged
- Logs not monitored or alerted on
- Logs stored only locally (lost if server compromised)
- Sensitive data in logs

### Remediation
- Log all authentication events (success and failure)
- Log all authorization failures
- Log all input validation failures
- Centralize logs (ELK, Splunk, CloudWatch, Datadog)
- Set up alerts for suspicious patterns (multiple failed logins, privilege escalation attempts)
- Protect log integrity (append-only, tamper-evident)
- Never log passwords, tokens, session IDs, or PII
- Retain logs per compliance requirements (typically 90 days to 1 year)

---

## A10: Server-Side Request Forgery (SSRF)

### Vulnerabilities
- Application fetches URLs provided by users without validation
- Internal services accessible via crafted URLs
- Cloud metadata endpoints accessible (169.254.169.254)

### Remediation
- Validate and sanitize all user-supplied URLs
- Allowlist permitted destinations (domains and IP ranges)
- Block requests to internal/private IP ranges (10.x, 172.16-31.x, 192.168.x, 169.254.x)
- Block requests to cloud metadata endpoints
- Use a URL parser to prevent bypass techniques (URL encoding, DNS rebinding)
- Run URL-fetching services in isolated network segments
- Disable HTTP redirects in server-side HTTP clients (or re-validate after redirect)
