# OWASP Top 10 (2021) — Detailed Security Checklist

Comprehensive reference for each OWASP Top 10 category with descriptions, test procedures, code patterns to detect, remediation steps, and CVSS scoring guidance.

---

## A01:2021 — Broken Access Control

**CWEs Covered:** CWE-200, CWE-201, CWE-352, CWE-639, CWE-862, CWE-863

### Description

Access control enforces policy so users cannot act outside their intended permissions. Failures typically lead to unauthorized disclosure, modification, or destruction of data, or performing business functions outside the user's limits.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | Horizontal privilege escalation | Change user ID in API requests (`/users/123` to `/users/124`) | 403 Forbidden |
| 2 | Vertical privilege escalation | Access admin endpoints with regular user token | 403 Forbidden |
| 3 | CORS validation | Send request with `Origin: https://evil.com` | `Access-Control-Allow-Origin` must not reflect arbitrary origins |
| 4 | Forced browsing | Request `/admin`, `/debug`, `/api/internal`, `/.env`, `/swagger.json` | 403 or 404 |
| 5 | Method-based bypass | Try POST instead of GET, or PUT instead of PATCH | Authorization checks apply regardless of HTTP method |
| 6 | JWT claim manipulation | Modify `role`, `is_admin`, `user_id` claims, re-sign with weak secret | 401 Unauthorized |
| 7 | Path traversal in authorization | Request `/api/users/../admin/settings` | Canonical path check must reject traversal |
| 8 | API endpoint enumeration | Fuzz API paths with wordlists | Only documented endpoints should respond |

### Code Patterns to Detect

```python
# BAD: No authorization check on resource access
@app.route("/api/documents/<doc_id>")
def get_document(doc_id):
    return Document.query.get(doc_id).to_json()  # No ownership check!

# GOOD: Verify ownership
@app.route("/api/documents/<doc_id>")
@login_required
def get_document(doc_id):
    doc = Document.query.get_or_404(doc_id)
    if doc.owner_id != current_user.id:
        abort(403)
    return doc.to_json()
```

```javascript
// BAD: Client-side only access control
{isAdmin && <AdminPanel />}  // Hidden but still accessible via API

// GOOD: Server-side middleware
app.use('/admin/*', requireRole('admin'));
```

### Remediation

1. Deny by default — require explicit authorization for every endpoint
2. Implement server-side access control, never rely on client-side checks
3. Use UUIDs instead of sequential IDs for resource identifiers
4. Log and alert on access control failures
5. Rate limit API requests to minimize automated enumeration
6. Disable CORS or restrict to specific trusted origins
7. Invalidate server-side sessions on logout

### CVSS Scoring Guidance

- **Horizontal escalation (read):** CVSS 6.5 — AV:N/AC:L/PR:L/UI:N/S:U/C:H/I:N/A:N
- **Horizontal escalation (write):** CVSS 8.1 — AV:N/AC:L/PR:L/UI:N/S:U/C:H/I:H/A:N
- **Vertical escalation to admin:** CVSS 8.8 — AV:N/AC:L/PR:L/UI:N/S:U/C:H/I:H/A:H
- **Unauthenticated admin access:** CVSS 9.8 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H

---

## A02:2021 — Cryptographic Failures

**CWEs Covered:** CWE-259, CWE-327, CWE-328, CWE-330, CWE-331

### Description

Failures related to cryptography that often lead to sensitive data exposure. This includes using weak algorithms, improper key management, and transmitting data in cleartext.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | TLS version | `nmap --script ssl-enum-ciphers -p 443 target` | Only TLS 1.2+ accepted |
| 2 | Certificate validity | `openssl s_client -connect target:443` | Valid cert, not self-signed |
| 3 | HSTS header | Check response headers | `Strict-Transport-Security: max-age=31536000` |
| 4 | Password storage | Review auth code | bcrypt/scrypt/argon2 with cost >= 10 |
| 5 | Sensitive data in URLs | Review access logs | No tokens, passwords, or PII in query params |
| 6 | Encryption at rest | Check database/storage config | Sensitive fields encrypted (AES-256-GCM) |
| 7 | Key management | Review key storage | Keys in secrets manager, not in code/env files |
| 8 | Random number generation | Review token generation code | Uses crypto-grade PRNG (secrets module, crypto.randomBytes) |

### Code Patterns to Detect

```python
# BAD: MD5 for password hashing
password_hash = hashlib.md5(password.encode()).hexdigest()

# BAD: Hardcoded encryption key
cipher = AES.new(b"mysecretkey12345", AES.MODE_GCM)

# BAD: Weak random for tokens
token = str(random.randint(100000, 999999))

# GOOD: bcrypt for passwords
password_hash = bcrypt.hashpw(password.encode(), bcrypt.gensalt(rounds=12))

# GOOD: Secrets module for tokens
token = secrets.token_urlsafe(32)
```

### Remediation

1. Use TLS 1.2+ for all data in transit; redirect HTTP to HTTPS
2. Use bcrypt (cost 12+), scrypt, or argon2id for password hashing
3. Use AES-256-GCM for encryption at rest
4. Store keys in a secrets manager (Vault, AWS Secrets Manager, GCP Secret Manager)
5. Use `secrets` (Python) or `crypto.randomBytes` (Node.js) for token generation
6. Enable HSTS with preload
7. Never store sensitive data in URLs or logs

### CVSS Scoring Guidance

- **Cleartext transmission of passwords:** CVSS 7.5 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:N/A:N
- **Weak password hashing (MD5):** CVSS 7.5 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:N/A:N
- **Hardcoded encryption key:** CVSS 7.2 — AV:N/AC:L/PR:H/UI:N/S:U/C:H/I:H/A:H

---

## A03:2021 — Injection

**CWEs Covered:** CWE-20, CWE-74, CWE-75, CWE-77, CWE-78, CWE-79, CWE-89

### Description

Injection flaws occur when untrusted data is sent to an interpreter as part of a command or query. Includes SQL, NoSQL, OS command, LDAP, XPath, and template injection.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | SQL injection | Submit `' OR 1=1--` in input fields | No data leakage, proper error handling |
| 2 | Blind SQL injection | Submit `' AND SLEEP(5)--` | No 5-second delay in response |
| 3 | NoSQL injection | Submit `{"$gt":""}` in JSON fields | No data leakage |
| 4 | XSS (reflected) | Submit `<script>alert(1)</script>` | Input is escaped/encoded in response |
| 5 | XSS (stored) | Submit payload in persistent fields | Payload is sanitized before storage |
| 6 | Command injection | Submit `; whoami` in fields | No command execution |
| 7 | Template injection | Submit `{{7*7}}` | No "49" in response |
| 8 | LDAP injection | Submit `*)(uid=*))(|(uid=*` | No directory enumeration |

### Code Patterns to Detect

```python
# BAD: String concatenation in SQL
cursor.execute("SELECT * FROM users WHERE email = '" + email + "'")
cursor.execute(f"SELECT * FROM users WHERE email = '{email}'")

# GOOD: Parameterized query
cursor.execute("SELECT * FROM users WHERE email = %s", (email,))
```

```javascript
// BAD: Template literal in SQL
db.query(`SELECT * FROM users WHERE id = ${userId}`);

// GOOD: Parameterized query
db.query('SELECT * FROM users WHERE id = $1', [userId]);
```

### Remediation

1. Use parameterized queries / prepared statements for ALL database operations
2. Use ORM methods with bound parameters (not raw queries)
3. Validate and sanitize all input on the server side
4. Use Content-Security-Policy to mitigate XSS impact
5. Escape output based on context (HTML, JS, URL, CSS)
6. Never pass user input to eval(), exec(), os.system(), or child_process
7. Use allowlists for expected input formats

### CVSS Scoring Guidance

- **SQL injection (unauthenticated):** CVSS 9.8 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H
- **Stored XSS:** CVSS 7.1 — AV:N/AC:L/PR:L/UI:R/S:C/C:L/I:L/A:N
- **Reflected XSS:** CVSS 6.1 — AV:N/AC:L/PR:N/UI:R/S:C/C:L/I:L/A:N
- **Command injection:** CVSS 9.8 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H

---

## A04:2021 — Insecure Design

**CWEs Covered:** CWE-209, CWE-256, CWE-501, CWE-522

### Description

Insecure design represents weaknesses in the design and architecture of the application, distinct from implementation bugs. This includes missing or ineffective security controls.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | Rate limiting | Send 100 rapid requests to login | 429 after threshold (5-10 attempts) |
| 2 | Business logic abuse | Submit negative quantities, skip payment | All calculations server-side |
| 3 | Account lockout | 10+ failed login attempts | Account locked or CAPTCHA triggered |
| 4 | Multi-step flow bypass | Skip steps via direct URL access | Server validates state at each step |
| 5 | Password reset abuse | Request multiple reset tokens | Previous tokens invalidated |

### Remediation

1. Use threat modeling during design phase (STRIDE, PASTA)
2. Implement rate limiting on all sensitive endpoints
3. Validate business logic on the server, never trust client calculations
4. Use state machines for multi-step workflows
5. Implement CAPTCHA for public-facing forms after threshold

### CVSS Scoring Guidance

- **Missing rate limit on auth:** CVSS 7.5 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:N/A:N
- **Business logic bypass (financial):** CVSS 8.1 — AV:N/AC:L/PR:L/UI:N/S:U/C:N/I:H/A:H

---

## A05:2021 — Security Misconfiguration

**CWEs Covered:** CWE-2, CWE-11, CWE-13, CWE-15, CWE-16, CWE-388

### Description

The application is improperly configured, with default settings, unnecessary features enabled, verbose error messages, or missing security hardening.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | Default credentials | Try admin:admin, root:root | Rejected |
| 2 | Debug mode | Trigger application errors | No stack traces in response |
| 3 | Security headers | Check response headers | CSP, X-Frame-Options, XCTO, HSTS present |
| 4 | HTTP methods | Send OPTIONS request | Only required methods allowed |
| 5 | Directory listing | Request directory without index | Listing disabled (403 or redirect) |
| 6 | Server version disclosure | Check Server and X-Powered-By headers | Version info removed |
| 7 | Error messages | Submit invalid data | Generic error messages, no internal details |

### Remediation

1. Disable debug mode in production
2. Remove default credentials and accounts
3. Add all security headers (CSP, HSTS, X-Frame-Options, XCTO, Referrer-Policy)
4. Remove Server and X-Powered-By headers
5. Disable directory listing
6. Implement generic error pages

### CVSS Scoring Guidance

- **Debug mode in production:** CVSS 5.3 — AV:N/AC:L/PR:N/UI:N/S:U/C:L/I:N/A:N
- **Default admin credentials:** CVSS 9.8 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H
- **Missing security headers:** CVSS 4.3 — AV:N/AC:L/PR:N/UI:R/S:U/C:N/I:L/A:N

---

## A06:2021 — Vulnerable and Outdated Components

**CWEs Covered:** CWE-1035, CWE-1104

### Description

Components (libraries, frameworks, software modules) with known vulnerabilities that can undermine application defenses.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | npm audit | `npm audit --json` | No critical or high vulnerabilities |
| 2 | pip audit | `pip audit --desc` | No known CVEs |
| 3 | Go vulncheck | `govulncheck ./...` | No reachable vulnerabilities |
| 4 | EOL check | Compare framework versions to vendor EOL dates | No EOL components |
| 5 | License audit | Check dependency licenses | No copyleft licenses in proprietary code |

### Remediation

1. Run dependency audits in CI/CD (block merges on critical/high)
2. Set up automated dependency update PRs (Dependabot, Renovate)
3. Pin dependency versions in lock files
4. Remove unused dependencies
5. Subscribe to security advisories for key dependencies

### CVSS Scoring Guidance

Inherit the CVSS score from the upstream CVE. Add environmental metrics based on reachability.

---

## A07:2021 — Identification and Authentication Failures

**CWEs Covered:** CWE-255, CWE-259, CWE-287, CWE-288, CWE-384, CWE-798

### Description

Weaknesses in authentication mechanisms that allow attackers to compromise passwords, keys, session tokens, or exploit implementation flaws to assume other users' identities.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | Brute force | 100 rapid login attempts | Account lockout or exponential backoff |
| 2 | Session cookie flags | Inspect cookies in browser | HttpOnly, Secure, SameSite set |
| 3 | Session invalidation | Logout, replay session cookie | 401 Unauthorized |
| 4 | Username enumeration | Submit valid/invalid usernames | Identical error messages |
| 5 | Password policy | Submit "12345" as password | Rejected (min 8 chars, complexity) |
| 6 | Password reset token | Request reset, check token expiry | Token expires in 15-60 minutes |
| 7 | MFA bypass | Skip MFA step via direct API call | Requires MFA completion |

### Remediation

1. Implement multi-factor authentication
2. Set session cookies with HttpOnly, Secure, SameSite=Strict
3. Invalidate sessions on logout and password change
4. Use generic error messages ("Invalid credentials" not "User not found")
5. Enforce strong password policy (NIST SP 800-63B)
6. Expire password reset tokens within 15-60 minutes

### CVSS Scoring Guidance

- **Authentication bypass:** CVSS 9.8 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H
- **Session fixation:** CVSS 7.5 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:N/A:N
- **Username enumeration:** CVSS 5.3 — AV:N/AC:L/PR:N/UI:N/S:U/C:L/I:N/A:N

---

## A08:2021 — Software and Data Integrity Failures

**CWEs Covered:** CWE-345, CWE-353, CWE-426, CWE-494, CWE-502, CWE-565, CWE-829

### Description

Code and infrastructure that does not protect against integrity violations, including unsafe deserialization, unsigned updates, and CI/CD pipeline manipulation.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | Unsafe deserialization | Send crafted serialized objects | Rejected or safely handled |
| 2 | SRI on CDN resources | Check script/link tags | Integrity attribute present |
| 3 | CI/CD pipeline | Review pipeline config | Signed commits, protected branches |
| 4 | Update integrity | Check update mechanism | Signed artifacts, hash verification |

### Remediation

1. Use `yaml.safe_load()` instead of `yaml.load()`
2. Avoid `pickle.loads()` on untrusted data
3. Add SRI hashes to all CDN-loaded scripts
4. Sign all deployment artifacts
5. Protect CI/CD pipeline with branch protection and signed commits

### CVSS Scoring Guidance

- **Unsafe deserialization (RCE):** CVSS 9.8 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:H
- **Missing SRI on CDN scripts:** CVSS 6.1 — AV:N/AC:L/PR:N/UI:R/S:C/C:L/I:L/A:N

---

## A09:2021 — Security Logging and Monitoring Failures

**CWEs Covered:** CWE-117, CWE-223, CWE-532, CWE-778

### Description

Without sufficient logging and monitoring, breaches cannot be detected. Logging too little means missed attacks; logging too much (sensitive data) creates new risks.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | Auth event logging | Attempt valid/invalid logins | Both logged with timestamp and IP |
| 2 | Sensitive data in logs | Review log output | No passwords, tokens, PII, credit cards |
| 3 | Alert thresholds | Trigger 50 failed logins | Alert generated |
| 4 | Log integrity | Check log storage | Append-only or integrity-protected storage |
| 5 | Admin action audit trail | Perform admin actions | All actions logged with user identity |

### Remediation

1. Log all authentication events (success and failure)
2. Sanitize logs — strip passwords, tokens, PII before writing
3. Set up alerting on anomalous patterns (SIEM integration)
4. Use append-only log storage (CloudWatch, Splunk, immutable S3)
5. Maintain audit trail for all admin and data-modifying actions

### CVSS Scoring Guidance

Logging failures are typically scored as contributing factors rather than standalone vulnerabilities. When combined with other findings, they increase the overall risk level.

---

## A10:2021 — Server-Side Request Forgery (SSRF)

**CWEs Covered:** CWE-918

### Description

SSRF occurs when a web application fetches a remote resource without validating the user-supplied URL, allowing attackers to reach internal services, cloud metadata endpoints, or other protected resources.

### Test Procedures

| # | Test | Method | Expected Result |
|---|------|--------|-----------------|
| 1 | Internal IP access | Submit `http://127.0.0.1` in URL fields | Request blocked |
| 2 | Cloud metadata | Submit `http://169.254.169.254/latest/meta-data/` | Request blocked |
| 3 | IPv6 localhost | Submit `http://[::1]` | Request blocked |
| 4 | DNS rebinding | Use DNS rebinding service | Request blocked after resolution |
| 5 | URL encoding bypass | Submit `http://0x7f000001` (hex localhost) | Request blocked |
| 6 | Open redirect chain | Find open redirect, chain to internal URL | Request blocked |

### Code Patterns to Detect

```python
# BAD: User-controlled URL without validation
url = request.args.get("url")
response = requests.get(url)  # SSRF!

# GOOD: URL allowlist validation
ALLOWED_HOSTS = {"api.example.com", "cdn.example.com"}
parsed = urlparse(url)
if parsed.hostname not in ALLOWED_HOSTS:
    abort(403, "URL not in allowlist")
response = requests.get(url)
```

### Remediation

1. Validate and allowlist outbound URLs (domain, scheme, port)
2. Block requests to private IP ranges (10.x, 172.16-31.x, 192.168.x, 127.x, 169.254.x)
3. Block requests to cloud metadata endpoints
4. Use a dedicated egress proxy for outbound requests
5. Disable unnecessary URL-fetching features
6. Resolve DNS and validate the IP address before making the request

### CVSS Scoring Guidance

- **SSRF to cloud metadata (credential theft):** CVSS 9.1 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:H/A:N
- **SSRF to internal service (read):** CVSS 7.5 — AV:N/AC:L/PR:N/UI:N/S:U/C:H/I:N/A:N
- **Blind SSRF (no response data):** CVSS 5.3 — AV:N/AC:L/PR:N/UI:N/S:U/C:L/I:N/A:N
