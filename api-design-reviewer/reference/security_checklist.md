# API Security Checklist

Comprehensive security checklist based on OWASP API Security Top 10 and production best practices.

## Table of Contents
1. [OWASP API Security Top 10](#owasp-api-security-top-10)
2. [Authentication](#authentication)
3. [Authorization](#authorization)
4. [Input Validation](#input-validation)
5. [Data Protection](#data-protection)
6. [Rate Limiting](#rate-limiting)
7. [Monitoring & Logging](#monitoring--logging)

---

## OWASP API Security Top 10

### API1:2023 - Broken Object Level Authorization (BOLA)

**Vulnerability:**
```python
# ❌ VULNERABLE: No authorization check
@app.get("/api/users/{user_id}/orders")
def get_user_orders(user_id: int):
    return db.query(Order).filter(Order.user_id == user_id).all()

# Attacker can access any user's orders by changing user_id
```

**Fix:**
```python
# ✅ SECURE: Verify ownership
@app.get("/api/users/{user_id}/orders")
def get_user_orders(user_id: int, current_user: User = Depends(get_current_user)):
    if current_user.id != user_id and not current_user.is_admin:
        raise HTTPException(status_code=403, detail="Access denied")
    return db.query(Order).filter(Order.user_id == user_id).all()
```

**Checklist:**
- [ ] Every resource access checks ownership or permissions
- [ ] Authorization happens on the server, never client-side
- [ ] Default deny (require explicit permission grants)
- [ ] Test with different users to ensure isolation

---

### API2:2023 - Broken Authentication

**Common Issues:**
- Weak password requirements
- No rate limiting on auth endpoints
- Tokens without expiration
- Predictable tokens (sequential, timestamp-based)
- Credentials in URLs

**Secure Authentication:**
```python
# Password requirements
MIN_PASSWORD_LENGTH = 12
REQUIRE_UPPERCASE = True
REQUIRE_LOWERCASE = True
REQUIRE_DIGITS = True
REQUIRE_SPECIAL_CHARS = True

# JWT configuration
JWT_EXPIRATION = 3600  # 1 hour
REFRESH_TOKEN_EXPIRATION = 2592000  # 30 days

# Token generation
import secrets
api_key = secrets.token_urlsafe(32)  # Cryptographically secure
```

**Checklist:**
- [ ] Passwords hashed with bcrypt/argon2 (never plaintext)
- [ ] Minimum password length (12+ characters)
- [ ] Rate limiting on login/signup endpoints
- [ ] JWT tokens have expiration (`exp` claim)
- [ ] Refresh token rotation implemented
- [ ] MFA supported for sensitive operations
- [ ] No credentials in URLs (use headers)
- [ ] Session timeout after inactivity

---

### API3:2023 - Broken Object Property Level Authorization

**Vulnerability: Mass Assignment**
```python
# ❌ VULNERABLE: User can set any field
@app.patch("/api/users/{id}")
def update_user(id: int, user_data: dict):
    user = db.query(User).get(id)
    for key, value in user_data.items():
        setattr(user, key, value)  # Dangerous!
    db.commit()

# Attacker sends: {"is_admin": true, "balance": 1000000}
```

**Fix:**
```python
# ✅ SECURE: Whitelist allowed fields
class UserUpdateSchema(BaseModel):
    name: Optional[str]
    email: Optional[EmailStr]
    # is_admin NOT included (can't be set via API)

@app.patch("/api/users/{id}")
def update_user(id: int, user_data: UserUpdateSchema):
    user = db.query(User).get(id)
    user.name = user_data.name
    user.email = user_data.email
    db.commit()
```

**Checklist:**
- [ ] Use DTOs/schemas to whitelist allowed fields
- [ ] Separate read vs write schemas
- [ ] Admin-only fields not settable by normal users
- [ ] Sensitive fields excluded from responses (passwords, tokens)
- [ ] Test: Try sending extra fields (should be ignored)

---

### API4:2023 - Unrestricted Resource Consumption

**Vulnerability: No Limits**
```python
# ❌ VULNERABLE: Unbounded query
@app.get("/api/users")
def get_users(limit: int = 100):  # User can request 1 million
    return db.query(User).limit(limit).all()
```

**Fix:**
```python
# ✅ SECURE: Enforce maximum
MAX_PAGE_SIZE = 100

@app.get("/api/users")
def get_users(limit: int = 20):
    if limit > MAX_PAGE_SIZE:
        raise HTTPException(400, f"Maximum limit is {MAX_PAGE_SIZE}")
    return db.query(User).limit(limit).all()
```

**Checklist:**
- [ ] Maximum page size enforced (50-100 typical)
- [ ] Request timeout configured (5-30s)
- [ ] Request body size limit (1-10MB)
- [ ] File upload size limit (10-100MB)
- [ ] Rate limiting per IP/user
- [ ] Expensive operations require authentication
- [ ] No unbounded collections

---

### API5:2023 - Broken Function Level Authorization

**Vulnerability: Missing Role Check**
```python
# ❌ VULNERABLE: Any authenticated user can delete
@app.delete("/api/users/{id}")
def delete_user(id: int, current_user: User = Depends(get_current_user)):
    db.query(User).filter(User.id == id).delete()
    db.commit()
```

**Fix:**
```python
# ✅ SECURE: Check admin role
@app.delete("/api/users/{id}")
@require_role("admin")
def delete_user(id: int, current_user: User = Depends(get_current_user)):
    if not current_user.is_admin:
        raise HTTPException(403, "Admin access required")
    db.query(User).filter(User.id == id).delete()
    db.commit()
```

**Checklist:**
- [ ] Admin operations require admin role check
- [ ] Role/permission checks in every sensitive endpoint
- [ ] Least privilege principle (minimum permissions needed)
- [ ] Test with different user roles
- [ ] Authorization middleware at application level

---

### API6:2023 - Unrestricted Access to Sensitive Business Flows

**Vulnerability: No Anti-Automation**
```python
# ❌ VULNERABLE: Can be automated
@app.post("/api/tickets/purchase")
def purchase_ticket(ticket_id: int):
    # Bots can buy all tickets instantly
    return process_purchase(ticket_id)
```

**Fix:**
```python
# ✅ SECURE: Rate limiting + CAPTCHA
from slowapi import Limiter
limiter = Limiter(key_func=get_remote_address)

@app.post("/api/tickets/purchase")
@limiter.limit("3/minute")
def purchase_ticket(ticket_id: int, captcha_token: str):
    if not verify_captcha(captcha_token):
        raise HTTPException(400, "Invalid CAPTCHA")
    return process_purchase(ticket_id)
```

**Checklist:**
- [ ] CAPTCHA on sensitive operations (signup, purchase)
- [ ] Rate limiting on critical endpoints
- [ ] Anomaly detection for unusual patterns
- [ ] Device fingerprinting for fraud detection
- [ ] Require email/phone verification
- [ ] Implement waiting rooms for high-demand events

---

### API7:2023 - Server Side Request Forgery (SSRF)

**Vulnerability: Unvalidated URL**
```python
# ❌ VULNERABLE: Can access internal services
@app.post("/api/fetch")
def fetch_url(url: str):
    response = requests.get(url)  # Dangerous!
    return response.text

# Attacker sends: "http://localhost:6379/admin"
# or "http://169.254.169.254/latest/meta-data/" (AWS metadata)
```

**Fix:**
```python
# ✅ SECURE: Whitelist allowed domains
ALLOWED_DOMAINS = ["example.com", "api.partner.com"]

@app.post("/api/fetch")
def fetch_url(url: str):
    parsed = urlparse(url)
    if parsed.hostname not in ALLOWED_DOMAINS:
        raise HTTPException(400, "Domain not allowed")
    if parsed.hostname in ["localhost", "127.0.0.1", "0.0.0.0"]:
        raise HTTPException(400, "Cannot access local resources")
    # Also block private IP ranges (10.x, 192.168.x, 169.254.x)
    response = requests.get(url, timeout=5)
    return response.text
```

**Checklist:**
- [ ] Whitelist allowed domains/protocols
- [ ] Block localhost and private IP ranges
- [ ] Disable redirects or validate redirect targets
- [ ] Use network segmentation (API can't access internal services)
- [ ] Timeout on external requests

---

### API8:2023 - Security Misconfiguration

**Common Misconfigurations:**
```yaml
# ❌ BAD: Development settings in production
DEBUG = True
CORS_ALLOW_ALL_ORIGINS = True
SSL_VERIFY = False
SECRET_KEY = "default-secret-key"

# ✅ GOOD: Production settings
DEBUG = False
CORS_ALLOWED_ORIGINS = ["https://example.com"]
SSL_VERIFY = True
SECRET_KEY = os.environ["SECRET_KEY"]  # From environment
```

**Checklist:**
- [ ] Debug mode disabled in production
- [ ] CORS properly configured (not `*`)
- [ ] HTTPS enforced (HSTS header)
- [ ] Security headers configured
- [ ] Default credentials changed
- [ ] Error messages don't expose internals
- [ ] Stack traces not sent to clients
- [ ] Unnecessary HTTP methods disabled

**Security Headers:**
```python
response.headers["Strict-Transport-Security"] = "max-age=31536000; includeSubDomains"
response.headers["X-Content-Type-Options"] = "nosniff"
response.headers["X-Frame-Options"] = "DENY"
response.headers["Content-Security-Policy"] = "default-src 'self'"
response.headers["X-XSS-Protection"] = "1; mode=block"
```

---

### API9:2023 - Improper Inventory Management

**Checklist:**
- [ ] API documentation complete and up-to-date
- [ ] All endpoints documented (including deprecated)
- [ ] API versioning strategy in place
- [ ] Deprecated endpoints have sunset dates
- [ ] Non-production environments secured
- [ ] Test/staging APIs not accessible publicly
- [ ] API gateway/proxy for centralized control
- [ ] Inventory of all API endpoints maintained

**Tools:**
- OpenAPI/Swagger spec generation
- API gateway (Kong, Apigee, AWS API Gateway)
- Security scanning (OWASP ZAP, Burp Suite)

---

### API10:2023 - Unsafe Consumption of APIs

**Vulnerability: Trusting External Data**
```python
# ❌ VULNERABLE: No validation of external API data
@app.get("/api/weather")
def get_weather(city: str):
    external_data = requests.get(f"https://weather-api.com/data?city={city}").json()
    # Directly using external data without validation
    return external_data
```

**Fix:**
```python
# ✅ SECURE: Validate and sanitize
from pydantic import BaseModel, validator

class WeatherResponse(BaseModel):
    temperature: float
    humidity: int
    conditions: str

    @validator('temperature')
    def temp_must_be_reasonable(cls, v):
        if not -100 <= v <= 100:
            raise ValueError('Temperature out of range')
        return v

@app.get("/api/weather")
def get_weather(city: str):
    external_data = requests.get(
        f"https://weather-api.com/data",
        params={"city": city},
        timeout=5
    ).json()
    # Validate before returning
    validated = WeatherResponse(**external_data)
    return validated
```

**Checklist:**
- [ ] Validate all external API responses
- [ ] Timeouts on external requests
- [ ] Certificate verification enabled
- [ ] Sanitize data before storing/displaying
- [ ] Rate limiting on external API calls
- [ ] Circuit breaker for unreliable services
- [ ] Don't trust external redirects

---

## Authentication

### Password Security

**Hashing:**
```python
import bcrypt

# Hashing password
password_hash = bcrypt.hashpw(password.encode(), bcrypt.gensalt(rounds=12))

# Verifying password
is_valid = bcrypt.checkpw(password.encode(), stored_hash)
```

**Requirements:**
- [ ] Minimum 12 characters
- [ ] Complexity requirements (upper, lower, digit, special)
- [ ] No common passwords (use blocklist)
- [ ] No user info in password (name, email)
- [ ] Password history (can't reuse last 5)

### Token Security

**JWT Best Practices:**
```python
import jwt
from datetime import datetime, timedelta

# Generate JWT
payload = {
    "user_id": 123,
    "exp": datetime.utcnow() + timedelta(hours=1),
    "iat": datetime.utcnow(),
    "jti": secrets.token_urlsafe(16)  # Unique token ID
}
token = jwt.encode(payload, SECRET_KEY, algorithm="HS256")

# Verify JWT
try:
    decoded = jwt.decode(token, SECRET_KEY, algorithms=["HS256"])
except jwt.ExpiredSignatureError:
    raise HTTPException(401, "Token expired")
except jwt.InvalidTokenError:
    raise HTTPException(401, "Invalid token")
```

**Checklist:**
- [ ] Short expiration (1 hour for access tokens)
- [ ] Refresh token rotation
- [ ] Token revocation mechanism
- [ ] Unique token ID (`jti` claim) for blacklisting
- [ ] Signed with strong algorithm (HS256, RS256)
- [ ] Secret key stored securely (not in code)

---

## Authorization

### Role-Based Access Control (RBAC)

```python
from enum import Enum

class Role(Enum):
    USER = "user"
    MODERATOR = "moderator"
    ADMIN = "admin"

def require_role(required_role: Role):
    def decorator(func):
        def wrapper(*args, current_user: User, **kwargs):
            if current_user.role.value < required_role.value:
                raise HTTPException(403, "Insufficient permissions")
            return func(*args, current_user=current_user, **kwargs)
        return wrapper
    return decorator

@app.delete("/api/users/{id}")
@require_role(Role.ADMIN)
def delete_user(id: int, current_user: User):
    # Only admins can delete users
    pass
```

### Attribute-Based Access Control (ABAC)

```python
def can_edit_post(user: User, post: Post) -> bool:
    # Post author can edit
    if post.author_id == user.id:
        return True
    # Moderators can edit any post
    if user.role == Role.MODERATOR:
        return True
    # Admins can edit everything
    if user.role == Role.ADMIN:
        return True
    return False
```

**Checklist:**
- [ ] Authorization checks on every sensitive operation
- [ ] Principle of least privilege
- [ ] Separate read/write permissions
- [ ] Resource-level permissions (not just endpoint-level)
- [ ] Test with different user roles and scenarios

---

## Input Validation

### SQL Injection Prevention

```python
# ❌ NEVER: String concatenation
query = f"SELECT * FROM users WHERE id = {user_id}"  # VULNERABLE!

# ✅ ALWAYS: Parameterized queries
query = "SELECT * FROM users WHERE id = ?"
cursor.execute(query, (user_id,))

# ✅ OR: Use ORM
user = db.query(User).filter(User.id == user_id).first()
```

### Input Validation

```python
from pydantic import BaseModel, EmailStr, validator, constr

class UserCreate(BaseModel):
    email: EmailStr  # Validates email format
    username: constr(min_length=3, max_length=30, regex="^[a-zA-Z0-9_]+$")
    age: int

    @validator('age')
    def age_must_be_valid(cls, v):
        if not 0 <= v <= 150:
            raise ValueError('Age must be between 0 and 150')
        return v

    @validator('username')
    def username_no_profanity(cls, v):
        if contains_profanity(v):
            raise ValueError('Username contains inappropriate content')
        return v
```

**Validation Checklist:**
- [ ] Type validation (string, int, email, UUID)
- [ ] Length limits (min/max)
- [ ] Format validation (regex patterns)
- [ ] Range validation (min/max values)
- [ ] Enum validation (allowed values)
- [ ] Business rule validation
- [ ] Sanitization (remove/escape dangerous characters)

### File Upload Security

```python
ALLOWED_EXTENSIONS = {'png', 'jpg', 'jpeg', 'pdf'}
MAX_FILE_SIZE = 10 * 1024 * 1024  # 10 MB

def validate_file_upload(file):
    # Check extension
    ext = file.filename.split('.')[-1].lower()
    if ext not in ALLOWED_EXTENSIONS:
        raise HTTPException(400, "File type not allowed")

    # Check size
    file.seek(0, 2)  # Seek to end
    size = file.tell()
    file.seek(0)  # Reset
    if size > MAX_FILE_SIZE:
        raise HTTPException(400, "File too large")

    # Check content type (don't trust client)
    import magic
    mime = magic.from_buffer(file.read(2048), mime=True)
    file.seek(0)
    if mime not in ['image/png', 'image/jpeg', 'application/pdf']:
        raise HTTPException(400, "Invalid file content")

    # Virus scan (in production)
    # scan_result = antivirus.scan(file)

    return True
```

**File Upload Checklist:**
- [ ] File type whitelist (not blacklist)
- [ ] File size limit
- [ ] Content-type verification (check actual content)
- [ ] Virus scanning
- [ ] Store outside web root
- [ ] Randomize filenames (prevent overwrite)
- [ ] Serve files with correct Content-Type
- [ ] Set Content-Disposition: attachment for downloads

---

## Data Protection

### Encryption

**At Rest:**
- [ ] Database encryption enabled
- [ ] Sensitive fields encrypted (SSN, credit cards)
- [ ] Encryption keys rotated regularly
- [ ] Keys stored in vault (AWS KMS, HashiCorp Vault)

**In Transit:**
- [ ] HTTPS enforced everywhere
- [ ] TLS 1.2+ only (disable SSL, TLS 1.0/1.1)
- [ ] Strong cipher suites
- [ ] Certificate pinning (mobile apps)

### Sensitive Data Handling

```python
# ❌ BAD: Sensitive data in logs/URLs
logger.info(f"User {user.email} logged in with password {password}")
url = f"/reset-password?token={reset_token}"

# ✅ GOOD: Redacted logs, tokens in body/headers
logger.info(f"User ***@{user.email.split('@')[1]} logged in")
# POST /reset-password with token in body

# ✅ GOOD: Exclude from responses
class UserResponse(BaseModel):
    id: int
    email: str
    name: str
    # password NOT included

    class Config:
        exclude = {'password', 'password_hash'}
```

**Sensitive Data Checklist:**
- [ ] PII identified and protected
- [ ] Passwords never stored in plaintext
- [ ] Credit cards tokenized (don't store)
- [ ] API keys/secrets in environment variables
- [ ] Secrets not in version control
- [ ] Sensitive data redacted from logs
- [ ] Data retention policy (delete old data)
- [ ] GDPR compliance (right to deletion)

---

## Rate Limiting

### Implementation

```python
from slowapi import Limiter
from slowapi.util import get_remote_address

limiter = Limiter(key_func=get_remote_address)

# Per IP address
@app.get("/api/public")
@limiter.limit("100/minute")
def public_endpoint():
    pass

# Per authenticated user
@app.get("/api/data")
@limiter.limit("1000/hour", key_func=lambda: current_user.id)
def data_endpoint(current_user: User):
    pass

# Expensive operation
@app.post("/api/reports/generate")
@limiter.limit("5/hour")
def generate_report():
    pass
```

### Rate Limit Response

```http
HTTP/1.1 429 Too Many Requests
X-RateLimit-Limit: 100
X-RateLimit-Remaining: 0
X-RateLimit-Reset: 1635724860
Retry-After: 45

{
  "error": {
    "code": "RATE_LIMIT_EXCEEDED",
    "message": "Rate limit exceeded. Try again in 45 seconds."
  }
}
```

**Rate Limiting Checklist:**
- [ ] Per IP address limits (prevent abuse)
- [ ] Per user limits (authenticated)
- [ ] Different limits for different endpoints
- [ ] Stricter limits on auth endpoints (prevent brute force)
- [ ] Stricter limits on expensive operations
- [ ] Rate limit info in response headers
- [ ] Retry-After header when limited

---

## Monitoring & Logging

### Security Logging

```python
import logging

logger = logging.getLogger(__name__)

# Log security events
def log_auth_failure(username: str, ip: str, reason: str):
    logger.warning(
        "Authentication failed",
        extra={
            "event": "auth_failure",
            "username": username,  # Don't log if PII concern
            "ip": ip,
            "reason": reason,
            "timestamp": datetime.utcnow().isoformat()
        }
    )

# Log suspicious activity
def log_suspicious_activity(user_id: int, action: str, details: dict):
    logger.warning(
        "Suspicious activity detected",
        extra={
            "event": "suspicious_activity",
            "user_id": user_id,
            "action": action,
            "details": details,
            "timestamp": datetime.utcnow().isoformat()
        }
    )
```

**Events to Log:**
- [ ] Authentication attempts (success/failure)
- [ ] Authorization failures
- [ ] Input validation failures
- [ ] Rate limit violations
- [ ] Suspicious patterns (rapid changes, unusual access)
- [ ] Admin actions
- [ ] Data access (especially sensitive data)
- [ ] Configuration changes

**What NOT to Log:**
- [ ] Passwords (even hashed)
- [ ] API keys/tokens
- [ ] Credit card numbers
- [ ] SSNs or other PII (unless required)

### Alerting

**Alert On:**
- [ ] Repeated authentication failures
- [ ] Privilege escalation attempts
- [ ] Unusual data access patterns
- [ ] Configuration changes
- [ ] Error rate spikes
- [ ] Latency increases
- [ ] Security scan attempts

---

## Security Testing

### Automated Scanning

**Tools:**
- OWASP ZAP (API security scanner)
- Burp Suite (web vulnerability scanner)
- Nikto (web server scanner)
- SQLMap (SQL injection testing)

### Manual Testing

**Test Cases:**
- [ ] Authentication bypass
- [ ] Authorization bypass (BOLA)
- [ ] SQL injection (all inputs)
- [ ] XSS (if returning HTML)
- [ ] SSRF (URL parameters)
- [ ] Mass assignment
- [ ] Rate limit enforcement
- [ ] Token expiration
- [ ] CORS misconfiguration
- [ ] Information disclosure

---

## Security Checklist Summary

**Critical (Block Launch):**
- [ ] All endpoints require authentication (except public ones)
- [ ] Authorization checks on all resources
- [ ] No SQL injection vulnerabilities
- [ ] Passwords hashed with bcrypt/argon2
- [ ] HTTPS enforced everywhere
- [ ] Rate limiting on auth endpoints
- [ ] Input validation on all endpoints
- [ ] Security headers configured

**High Priority (Fix Soon):**
- [ ] JWT tokens expire within 1 hour
- [ ] Rate limiting on all endpoints
- [ ] File upload validation
- [ ] CORS properly configured
- [ ] Error messages don't expose internals
- [ ] Sensitive data excluded from logs
- [ ] Monitoring and alerting configured

**Medium Priority:**
- [ ] Refresh token rotation
- [ ] Circuit breakers on external APIs
- [ ] Security logging comprehensive
- [ ] GDPR compliance (data retention)
- [ ] API documentation complete
- [ ] Deprecation strategy for old endpoints

---

**Remember:** Security is not a one-time task. Regularly audit your APIs, stay updated on vulnerabilities, and always assume attackers are probing for weaknesses.
