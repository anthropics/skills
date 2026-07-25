# Security Standards Reference

Comprehensive security standards and secure coding practices for application security.

---

## Table of Contents

- [OWASP Top 10](#owasp-top-10)
- [Secure Coding Practices](#secure-coding-practices)
- [Authentication Standards](#authentication-standards)
- [API Security](#api-security)
- [Secrets Management](#secrets-management)
- [Security Headers](#security-headers)

---

## OWASP Top 10

### A01:2021 - Broken Access Control

**Description:** Access control enforces policy such that users cannot act outside of their intended permissions.

**Prevention:**

```python
# BAD - No authorization check
@app.route('/admin/users/<user_id>')
def get_user(user_id):
    return User.query.get(user_id).to_dict()

# GOOD - Authorization enforced
@app.route('/admin/users/<user_id>')
@requires_role('admin')
def get_user(user_id):
    user = User.query.get_or_404(user_id)
    if not current_user.can_access(user):
        abort(403)
    return user.to_dict()
```

**Checklist:**
- [ ] Deny access by default (allowlist approach)
- [ ] Implement RBAC or ABAC consistently
- [ ] Validate object-level authorization (IDOR prevention)
- [ ] Disable directory listing
- [ ] Log access control failures and alert on repeated failures

### A02:2021 - Cryptographic Failures

**Description:** Failures related to cryptography which often lead to exposure of sensitive data.

**Prevention:**

```python
# BAD - Weak hashing
import hashlib
password_hash = hashlib.md5(password.encode()).hexdigest()

# GOOD - Strong password hashing
from argon2 import PasswordHasher
ph = PasswordHasher(
    time_cost=3,
    memory_cost=65536,
    parallelism=4
)
password_hash = ph.hash(password)

# Verify password
try:
    ph.verify(stored_hash, password)
except argon2.exceptions.VerifyMismatchError:
    raise InvalidCredentials()
```

**Checklist:**
- [ ] Use TLS 1.2+ for all data in transit
- [ ] Use AES-256-GCM for encryption at rest
- [ ] Use Argon2id, bcrypt, or scrypt for passwords
- [ ] Never use MD5, SHA1 for security purposes
- [ ] Rotate encryption keys regularly

### A03:2021 - Injection

**Description:** Untrusted data sent to an interpreter as part of a command or query.

**SQL Injection Prevention:**

```python
# BAD - String concatenation (VULNERABLE)
query = f"SELECT * FROM users WHERE id = {user_id}"
cursor.execute(query)

# GOOD - Parameterized queries
cursor.execute("SELECT * FROM users WHERE id = %s", (user_id,))

# GOOD - ORM with parameter binding
user = User.query.filter_by(id=user_id).first()
```

**Command Injection Prevention:**

```python
# BAD - Shell execution with user input (VULNERABLE)
# NEVER use: os.system(f"ping {user_input}")

# GOOD - Use subprocess with shell=False and validated input
import subprocess

def safe_ping(hostname: str) -> str:
    # Validate hostname format first
    if not is_valid_hostname(hostname):
        raise ValueError("Invalid hostname")
    result = subprocess.run(
        ["ping", "-c", "4", hostname],
        shell=False,
        capture_output=True,
        text=True
    )
    return result.stdout
```

**XSS Prevention:**

```python
# BAD - Direct HTML insertion (VULNERABLE)
return f"<div>Welcome, {username}</div>"

# GOOD - HTML escaping
from markupsafe import escape
return f"<div>Welcome, {escape(username)}</div>"

# GOOD - Template auto-escaping (Jinja2)
# {{ username }} is auto-escaped by default
```

### A04:2021 - Insecure Design

**Description:** Risks related to design and architectural flaws.

**Prevention Patterns:**

```python
# Threat modeling categories (STRIDE)
THREATS = {
    'Spoofing': 'Authentication controls',
    'Tampering': 'Integrity controls',
    'Repudiation': 'Audit logging',
    'Information Disclosure': 'Encryption, access control',
    'Denial of Service': 'Rate limiting, resource limits',
    'Elevation of Privilege': 'Authorization controls'
}

# Defense in depth - multiple layers
class SecurePaymentFlow:
    def process_payment(self, payment_data):
        # Layer 1: Input validation
        self.validate_input(payment_data)

        # Layer 2: Authentication check
        self.verify_user_authenticated()

        # Layer 3: Authorization check
        self.verify_user_can_pay(payment_data.amount)

        # Layer 4: Rate limiting
        self.check_rate_limit()

        # Layer 5: Fraud detection
        self.check_fraud_signals(payment_data)

        # Layer 6: Secure processing
        return self.execute_payment(payment_data)
```

### A05:2021 - Security Misconfiguration

**Description:** Missing or incorrect security hardening.

**Prevention:**

```yaml
# Kubernetes pod security
apiVersion: v1
kind: Pod
spec:
  securityContext:
    runAsNonRoot: true
    runAsUser: 1000
    fsGroup: 1000
  containers:
  - name: app
    securityContext:
      allowPrivilegeEscalation: false
      readOnlyRootFilesystem: true
      capabilities:
        drop:
          - ALL
```

```python
# Flask security configuration
app.config.update(
    SESSION_COOKIE_SECURE=True,
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE='Lax',
    PERMANENT_SESSION_LIFETIME=timedelta(hours=1),
)
```

---

## Secure Coding Practices

### Input Validation

```python
from pydantic import BaseModel, validator, constr
from typing import Optional
import re

class UserInput(BaseModel):
    username: constr(min_length=3, max_length=50, regex=r'^[a-zA-Z0-9_]+$')
    email: str
    age: Optional[int] = None

    @validator('email')
    def validate_email(cls, v):
        # Use proper email validation
        pattern = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        if not re.match(pattern, v):
            raise ValueError('Invalid email format')
        return v.lower()

    @validator('age')
    def validate_age(cls, v):
        if v is not None and (v < 0 or v > 150):
            raise ValueError('Age must be between 0 and 150')
        return v
```

### Output Encoding

```python
import html
import json
from urllib.parse import quote

def encode_for_html(data: str) -> str:
    """Encode data for safe HTML output."""
    return html.escape(data)

def encode_for_javascript(data: str) -> str:
    """Encode data for safe JavaScript string."""
    return json.dumps(data)

def encode_for_url(data: str) -> str:
    """Encode data for safe URL parameter."""
    return quote(data, safe='')

def encode_for_css(data: str) -> str:
    """Encode data for safe CSS value."""
    return ''.join(
        c if c.isalnum() else f'\\{ord(c):06x}'
        for c in data
    )
```

### Error Handling

```python
import logging
from typing import Dict, Any

logger = logging.getLogger(__name__)

class SecurityException(Exception):
    """Base exception for security-related errors."""

    def __init__(self, message: str, internal_details: str = None):
        # User-facing message (safe to display)
        self.message = message
        # Internal details (for logging only)
        self.internal_details = internal_details
        super().__init__(message)

def handle_request():
    try:
        process_sensitive_data()
    except DatabaseError as e:
        # Log full details internally
        logger.error(f"Database error: {e}", exc_info=True)
        # Return generic message to user
        raise SecurityException(
            "An error occurred processing your request",
            internal_details=str(e)
        )
    except Exception as e:
        logger.error(f"Unexpected error: {e}", exc_info=True)
        raise SecurityException("An unexpected error occurred")
```

---

## Authentication Standards

### Password Requirements

```python
import re
from typing import Tuple

def validate_password(password: str) -> Tuple[bool, str]:
    """
    Validate password against security requirements.

    Requirements:
    - Minimum 12 characters
    - At least one uppercase letter
    - At least one lowercase letter
    - At least one digit
    - At least one special character
    - Not in common password list
    """
    if len(password) < 12:
        return False, "Password must be at least 12 characters"

    if not re.search(r'[A-Z]', password):
        return False, "Password must contain uppercase letter"

    if not re.search(r'[a-z]', password):
        return False, "Password must contain lowercase letter"

    if not re.search(r'\d', password):
        return False, "Password must contain a digit"

    if not re.search(r'[!@#$%^&*(),.?":{}|<>]', password):
        return False, "Password must contain special character"

    # Check against common passwords (use haveibeenpwned API in production)
    common_passwords = {'password123', 'qwerty123456', 'admin123456'}
    if password.lower() in common_passwords:
        return False, "Password is too common"

    return True, "Password meets requirements"
```

### JWT Best Practices

```python
import jwt
from datetime import datetime, timedelta
from typing import Dict, Optional

class JWTManager:
    def __init__(self, secret_key: str, algorithm: str = 'HS256'):
        self.secret_key = secret_key
        self.algorithm = algorithm
        self.access_token_expiry = timedelta(minutes=15)
        self.refresh_token_expiry = timedelta(days=7)

    def create_access_token(self, user_id: str, roles: list) -> str:
        payload = {
            'sub': user_id,
            'roles': roles,
            'type': 'access',
            'iat': datetime.utcnow(),
            'exp': datetime.utcnow() + self.access_token_expiry,
            'jti': self._generate_jti()  # Unique token ID for revocation
        }
        return jwt.encode(payload, self.secret_key, algorithm=self.algorithm)

    def verify_token(self, token: str) -> Optional[Dict]:
        try:
            payload = jwt.decode(
                token,
                self.secret_key,
                algorithms=[self.algorithm],
                options={
                    'require': ['exp', 'iat', 'sub', 'jti'],
                    'verify_exp': True
                }
            )

            # Check if token is revoked
            if self._is_token_revoked(payload['jti']):
                return None

            return payload
        except jwt.ExpiredSignatureError:
            return None
        except jwt.InvalidTokenError:
            return None
```

### MFA Implementation

```python
import pyotp
import qrcode
from io import BytesIO
import base64

class TOTPManager:
    def __init__(self, issuer: str = "MyApp"):
        self.issuer = issuer

    def generate_secret(self) -> str:
        """Generate a new TOTP secret for a user."""
        return pyotp.random_base32()

    def get_provisioning_uri(self, secret: str, email: str) -> str:
        """Generate URI for QR code."""
        totp = pyotp.TOTP(secret)
        return totp.provisioning_uri(name=email, issuer_name=self.issuer)

    def generate_qr_code(self, provisioning_uri: str) -> str:
        """Generate base64-encoded QR code image."""
        qr = qrcode.QRCode(version=1, box_size=10, border=5)
        qr.add_data(provisioning_uri)
        qr.make(fit=True)

        img = qr.make_image(fill_color="black", back_color="white")
        buffer = BytesIO()
        img.save(buffer, format='PNG')
        return base64.b64encode(buffer.getvalue()).decode()

    def verify_totp(self, secret: str, code: str) -> bool:
        """Verify TOTP code with time window tolerance."""
        totp = pyotp.TOTP(secret)
        # Allow 1 period before/after for clock skew
        return totp.verify(code, valid_window=1)
```

---

## API Security

### Rate Limiting

```python
from functools import wraps
from flask import request, jsonify
import time
from collections import defaultdict
import threading

class RateLimiter:
    def __init__(self, requests_per_minute: int = 60):
        self.requests_per_minute = requests_per_minute
        self.requests = defaultdict(list)
        self.lock = threading.Lock()

    def is_rate_limited(self, identifier: str) -> bool:
        with self.lock:
            now = time.time()
            minute_ago = now - 60

            # Clean old requests
            self.requests[identifier] = [
                req_time for req_time in self.requests[identifier]
                if req_time > minute_ago
            ]

            if len(self.requests[identifier]) >= self.requests_per_minute:
                return True

            self.requests[identifier].append(now)
            return False

rate_limiter = RateLimiter(requests_per_minute=100)

def rate_limit(f):
    @wraps(f)
    def decorated_function(*args, **kwargs):
        identifier = request.remote_addr

        if rate_limiter.is_rate_limited(identifier):
            return jsonify({
                'error': 'Rate limit exceeded',
                'retry_after': 60
            }), 429

        return f(*args, **kwargs)
    return decorated_function
```

### API Key Validation

```python
import hashlib
import secrets
from datetime import datetime
from typing import Optional, Dict

class APIKeyManager:
    def __init__(self, db):
        self.db = db

    def generate_api_key(self, user_id: str, name: str, scopes: list) -> Dict:
        """Generate a new API key."""
        # Generate key with prefix for identification
        raw_key = f"sk_live_{secrets.token_urlsafe(32)}"

        # Store hash only
        key_hash = hashlib.sha256(raw_key.encode()).hexdigest()

        api_key_record = {
            'id': secrets.token_urlsafe(16),
            'user_id': user_id,
            'name': name,
            'key_hash': key_hash,
            'key_prefix': raw_key[:12],  # Store prefix for identification
            'scopes': scopes,
            'created_at': datetime.utcnow(),
            'last_used_at': None
        }

        self.db.api_keys.insert(api_key_record)

        # Return raw key only once
        return {
            'key': raw_key,
            'id': api_key_record['id'],
            'scopes': scopes
        }

    def validate_api_key(self, raw_key: str) -> Optional[Dict]:
        """Validate an API key and return associated data."""
        key_hash = hashlib.sha256(raw_key.encode()).hexdigest()

        api_key = self.db.api_keys.find_one({'key_hash': key_hash})

        if not api_key:
            return None

        # Update last used timestamp
        self.db.api_keys.update(
            {'id': api_key['id']},
            {'last_used_at': datetime.utcnow()}
        )

        return {
            'user_id': api_key['user_id'],
            'scopes': api_key['scopes']
        }
```

---

## Secrets Management

### Environment Variables

```python
import os
from typing import Optional
from dataclasses import dataclass

@dataclass
class AppSecrets:
    database_url: str
    jwt_secret: str
    api_key: str
    encryption_key: str

def load_secrets() -> AppSecrets:
    """Load secrets from environment with validation."""

    def get_required(name: str) -> str:
        value = os.environ.get(name)
        if not value:
            raise ValueError(f"Required environment variable {name} is not set")
        return value

    return AppSecrets(
        database_url=get_required('DATABASE_URL'),
        jwt_secret=get_required('JWT_SECRET'),
        api_key=get_required('API_KEY'),
        encryption_key=get_required('ENCRYPTION_KEY')
    )

# Never log secrets
import logging

class SecretFilter(logging.Filter):
    """Filter to redact secrets from logs."""

    def __init__(self, secrets: list):
        super().__init__()
        self.secrets = secrets

    def filter(self, record):
        message = record.getMessage()
        for secret in self.secrets:
            if secret in message:
                record.msg = record.msg.replace(secret, '[REDACTED]')
        return True
```

### HashiCorp Vault Integration

```python
import hvac
from typing import Dict, Optional

class VaultClient:
    def __init__(self, url: str, token: str = None, role_id: str = None, secret_id: str = None):
        self.client = hvac.Client(url=url)

        if token:
            self.client.token = token
        elif role_id and secret_id:
            # AppRole authentication
            self.client.auth.approle.login(
                role_id=role_id,
                secret_id=secret_id
            )

    def get_secret(self, path: str, key: str) -> Optional[str]:
        """Retrieve a secret from Vault."""
        try:
            response = self.client.secrets.kv.v2.read_secret_version(path=path)
            return response['data']['data'].get(key)
        except hvac.exceptions.InvalidPath:
            return None

    def get_database_credentials(self, role: str) -> Dict[str, str]:
        """Get dynamic database credentials."""
        response = self.client.secrets.database.generate_credentials(name=role)
        return {
            'username': response['data']['username'],
            'password': response['data']['password'],
            'lease_id': response['lease_id'],
            'lease_duration': response['lease_duration']
        }
```

---

## Security Headers

### HTTP Security Headers

```python
from flask import Flask, Response

def add_security_headers(response: Response) -> Response:
    """Add security headers to HTTP response."""

    # Prevent clickjacking
    response.headers['X-Frame-Options'] = 'DENY'

    # Enable XSS filter
    response.headers['X-XSS-Protection'] = '1; mode=block'

    # Prevent MIME type sniffing
    response.headers['X-Content-Type-Options'] = 'nosniff'

    # Referrer policy
    response.headers['Referrer-Policy'] = 'strict-origin-when-cross-origin'

    # Content Security Policy
    response.headers['Content-Security-Policy'] = (
        "default-src 'self'; "
        "script-src 'self' 'unsafe-inline'; "
        "style-src 'self' 'unsafe-inline'; "
        "img-src 'self' data: https:; "
        "font-src 'self'; "
        "frame-ancestors 'none'; "
        "form-action 'self'"
    )

    # HSTS (enable only with valid HTTPS)
    response.headers['Strict-Transport-Security'] = (
        'max-age=31536000; includeSubDomains; preload'
    )

    # Permissions Policy
    response.headers['Permissions-Policy'] = (
        'geolocation=(), microphone=(), camera=()'
    )

    return response

app = Flask(__name__)
app.after_request(add_security_headers)
```

---

## Quick Reference

### Security Checklist

| Category | Check | Priority |
|----------|-------|----------|
| Authentication | MFA enabled | Critical |
| Authentication | Password policy enforced | Critical |
| Authorization | RBAC implemented | Critical |
| Input | All inputs validated | Critical |
| Injection | Parameterized queries | Critical |
| Crypto | TLS 1.2+ enforced | Critical |
| Secrets | No hardcoded secrets | Critical |
| Headers | Security headers set | High |
| Logging | Security events logged | High |
| Dependencies | No known vulnerabilities | High |

### Tool Recommendations

| Purpose | Tool | Usage |
|---------|------|-------|
| SAST | Semgrep | `semgrep --config auto .` |
| SAST | Bandit (Python) | `bandit -r src/` |
| Secrets | Gitleaks | `gitleaks detect --source .` |
| Dependencies | Snyk | `snyk test` |
| Container | Trivy | `trivy image myapp:latest` |
| DAST | OWASP ZAP | Dynamic scanning |
