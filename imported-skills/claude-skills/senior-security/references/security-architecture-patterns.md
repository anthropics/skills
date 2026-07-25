# Security Architecture Patterns

Proven security architecture patterns for designing resilient systems.

---

## Table of Contents

- [Zero Trust Architecture](#zero-trust-architecture)
- [Defense in Depth](#defense-in-depth)
- [Secure Authentication Patterns](#secure-authentication-patterns)
- [API Security Patterns](#api-security-patterns)
- [Data Protection Patterns](#data-protection-patterns)
- [Security Anti-Patterns](#security-anti-patterns)

---

## Zero Trust Architecture

Never trust, always verify. Every request authenticated and authorized regardless of network location.

### Core Principles

| Principle | Implementation |
|-----------|----------------|
| Verify explicitly | Authenticate every request with identity, location, device health |
| Least privilege | Just-in-time and just-enough access (JIT/JEA) |
| Assume breach | Segment access, encrypt end-to-end, use analytics |

### Implementation Components

```
ZERO TRUST ARCHITECTURE

┌─────────────────────────────────────────────────────────────┐
│                        CONTROL PLANE                         │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐      │
│  │   Identity   │  │    Policy    │  │   Threat     │      │
│  │   Provider   │  │    Engine    │  │  Intelligence│      │
│  └──────────────┘  └──────────────┘  └──────────────┘      │
└─────────────────────────────────────────────────────────────┘
                              │
                    ┌─────────┴─────────┐
                    │   Policy Decision │
                    │   Point (PDP)     │
                    └─────────┬─────────┘
                              │
┌─────────────────────────────┴───────────────────────────────┐
│                        DATA PLANE                            │
│  ┌──────────────┐                      ┌──────────────┐     │
│  │    User      │──── PEP ────────────▶│   Resource   │     │
│  │   Device     │      │               │   (App/Data) │     │
│  └──────────────┘      │               └──────────────┘     │
│                   Policy Enforcement                         │
│                   Point (PEP)                               │
└─────────────────────────────────────────────────────────────┘
```

### Authentication Flow

```python
# Zero Trust authentication middleware
import jwt
from functools import wraps

def zero_trust_auth(required_claims=None):
    """
    Verify every request against identity, device, and context.
    """
    def decorator(f):
        @wraps(f)
        def decorated(*args, **kwargs):
            token = request.headers.get('Authorization', '').replace('Bearer ', '')

            # 1. Verify token signature and expiration
            try:
                payload = jwt.decode(token, PUBLIC_KEY, algorithms=['RS256'])
            except jwt.InvalidTokenError:
                return {'error': 'Invalid token'}, 401

            # 2. Verify device compliance
            device_id = request.headers.get('X-Device-ID')
            if not verify_device_compliance(device_id, payload['user_id']):
                return {'error': 'Device not compliant'}, 403

            # 3. Verify location/network context
            client_ip = request.remote_addr
            if not verify_network_context(client_ip, payload['allowed_networks']):
                return {'error': 'Network context invalid'}, 403

            # 4. Verify required claims
            if required_claims:
                for claim in required_claims:
                    if claim not in payload:
                        return {'error': f'Missing claim: {claim}'}, 403

            # 5. Log access for analytics
            log_access_attempt(payload, request, 'allowed')

            return f(*args, **kwargs)
        return decorated
    return decorator

@app.route('/api/sensitive-data')
@zero_trust_auth(required_claims=['data:read', 'clearance:secret'])
def get_sensitive_data():
    return fetch_data()
```

### Network Segmentation

| Segment | Access Level | Controls |
|---------|--------------|----------|
| DMZ | Public | WAF, DDoS protection, rate limiting |
| Application | Authenticated users | mTLS, service mesh, RBAC |
| Data | Authorized services only | Encryption, audit logging, DLP |
| Management | Privileged admins | PAM, MFA, session recording |

---

## Defense in Depth

Multiple layers of security controls so failure of one doesn't compromise the system.

### Security Layers

```
DEFENSE IN DEPTH LAYERS

┌─────────────────────────────────────────────────────────────┐
│  Layer 1: PERIMETER                                          │
│  - Firewall, WAF, DDoS mitigation, DNS filtering            │
├─────────────────────────────────────────────────────────────┤
│  Layer 2: NETWORK                                            │
│  - Segmentation, IDS/IPS, network monitoring, VPN           │
├─────────────────────────────────────────────────────────────┤
│  Layer 3: HOST                                               │
│  - Endpoint protection, hardening, patching, logging        │
├─────────────────────────────────────────────────────────────┤
│  Layer 4: APPLICATION                                        │
│  - Input validation, authentication, secure coding, SAST    │
├─────────────────────────────────────────────────────────────┤
│  Layer 5: DATA                                               │
│  - Encryption at rest/transit, access controls, DLP, backup │
└─────────────────────────────────────────────────────────────┘
```

### Implementation Checklist

| Layer | Control | Priority |
|-------|---------|----------|
| Perimeter | Web Application Firewall | Critical |
| Perimeter | Rate limiting | Critical |
| Network | Network segmentation (VLANs) | Critical |
| Network | Intrusion detection system | High |
| Host | Automated patching | Critical |
| Host | Endpoint Detection & Response | High |
| Application | Input validation | Critical |
| Application | Parameterized queries | Critical |
| Data | Encryption at rest (AES-256) | Critical |
| Data | TLS 1.3 for transit | Critical |

### Fail-Safe Defaults

```python
# Secure default configuration
class SecurityConfig:
    # Authentication
    SESSION_COOKIE_SECURE = True
    SESSION_COOKIE_HTTPONLY = True
    SESSION_COOKIE_SAMESITE = 'Strict'

    # Headers
    CONTENT_SECURITY_POLICY = "default-src 'self'; script-src 'self'"
    X_FRAME_OPTIONS = 'DENY'
    X_CONTENT_TYPE_OPTIONS = 'nosniff'
    REFERRER_POLICY = 'strict-origin-when-cross-origin'

    # Timeouts
    SESSION_LIFETIME = 3600  # 1 hour
    TOKEN_EXPIRY = 900  # 15 minutes

    # Rate limiting
    RATE_LIMIT_DEFAULT = '100/hour'
    RATE_LIMIT_AUTH = '10/minute'
```

---

## Secure Authentication Patterns

### OAuth 2.0 + PKCE Flow

```
OAUTH 2.0 AUTHORIZATION CODE FLOW WITH PKCE

┌──────────┐                                  ┌──────────────┐
│  Client  │                                  │    Auth      │
│  (SPA)   │                                  │   Server     │
└────┬─────┘                                  └──────┬───────┘
     │                                               │
     │ 1. Generate code_verifier (random string)     │
     │    code_challenge = SHA256(code_verifier)     │
     │                                               │
     │ 2. /authorize?                                │
     │    response_type=code&                        │
     │    client_id=xxx&                             │
     │    code_challenge=xxx&                        │
     │    code_challenge_method=S256                 │
     │──────────────────────────────────────────────▶│
     │                                               │
     │◀──────────────────────────────────────────────│
     │ 3. Redirect with authorization_code           │
     │                                               │
     │ 4. POST /token                                │
     │    grant_type=authorization_code&             │
     │    code=xxx&                                  │
     │    code_verifier=xxx  (proves possession)     │
     │──────────────────────────────────────────────▶│
     │                                               │
     │◀──────────────────────────────────────────────│
     │ 5. { access_token, refresh_token, id_token }  │
     │                                               │
```

### JWT Token Structure

```python
# Secure JWT implementation
import jwt
import secrets
from datetime import datetime, timedelta

class JWTService:
    def __init__(self, private_key, public_key, issuer):
        self.private_key = private_key
        self.public_key = public_key
        self.issuer = issuer

    def create_access_token(self, user_id, roles, expires_minutes=15):
        """Create short-lived access token."""
        now = datetime.utcnow()
        payload = {
            'iss': self.issuer,
            'sub': str(user_id),
            'iat': now,
            'exp': now + timedelta(minutes=expires_minutes),
            'jti': secrets.token_hex(16),  # Unique token ID
            'roles': roles,
            'type': 'access'
        }
        return jwt.encode(payload, self.private_key, algorithm='RS256')

    def create_refresh_token(self, user_id, expires_days=7):
        """Create longer-lived refresh token (stored server-side)."""
        now = datetime.utcnow()
        jti = secrets.token_hex(32)
        payload = {
            'iss': self.issuer,
            'sub': str(user_id),
            'iat': now,
            'exp': now + timedelta(days=expires_days),
            'jti': jti,
            'type': 'refresh'
        }
        # Store jti in database for revocation capability
        store_refresh_token(jti, user_id, now + timedelta(days=expires_days))
        return jwt.encode(payload, self.private_key, algorithm='RS256')

    def verify_token(self, token, token_type='access'):
        """Verify token with all security checks."""
        try:
            payload = jwt.decode(
                token,
                self.public_key,
                algorithms=['RS256'],
                issuer=self.issuer
            )

            # Verify token type
            if payload.get('type') != token_type:
                raise jwt.InvalidTokenError('Invalid token type')

            # For refresh tokens, check revocation
            if token_type == 'refresh':
                if is_token_revoked(payload['jti']):
                    raise jwt.InvalidTokenError('Token revoked')

            return payload

        except jwt.ExpiredSignatureError:
            raise AuthError('Token expired')
        except jwt.InvalidTokenError as e:
            raise AuthError(f'Invalid token: {e}')
```

### Multi-Factor Authentication

| Factor | Examples | Strength |
|--------|----------|----------|
| Knowledge | Password, PIN, security questions | Low-Medium |
| Possession | TOTP app, hardware key, SMS | Medium-High |
| Inherence | Fingerprint, face, voice | High |

```python
# TOTP implementation
import pyotp
import qrcode

class TOTPService:
    def __init__(self, issuer_name):
        self.issuer = issuer_name

    def generate_secret(self):
        """Generate a new TOTP secret for user."""
        return pyotp.random_base32()

    def get_provisioning_uri(self, secret, user_email):
        """Generate QR code URI for authenticator app."""
        totp = pyotp.TOTP(secret)
        return totp.provisioning_uri(
            name=user_email,
            issuer_name=self.issuer
        )

    def verify_code(self, secret, code, valid_window=1):
        """Verify TOTP code with time drift tolerance."""
        totp = pyotp.TOTP(secret)
        return totp.verify(code, valid_window=valid_window)
```

---

## API Security Patterns

### Input Validation

```python
from pydantic import BaseModel, validator, constr
import re

class UserCreateRequest(BaseModel):
    """Strict input validation for user creation."""

    email: constr(max_length=255)
    username: constr(min_length=3, max_length=50, regex=r'^[a-zA-Z0-9_]+$')
    password: constr(min_length=12, max_length=128)

    @validator('email')
    def validate_email(cls, v):
        email_regex = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$'
        if not re.match(email_regex, v):
            raise ValueError('Invalid email format')
        return v.lower()

    @validator('password')
    def validate_password_strength(cls, v):
        if not re.search(r'[A-Z]', v):
            raise ValueError('Password must contain uppercase letter')
        if not re.search(r'[a-z]', v):
            raise ValueError('Password must contain lowercase letter')
        if not re.search(r'\d', v):
            raise ValueError('Password must contain digit')
        if not re.search(r'[!@#$%^&*(),.?":{}|<>]', v):
            raise ValueError('Password must contain special character')
        return v
```

### Rate Limiting

```python
from redis import Redis
from functools import wraps
import time

class RateLimiter:
    """Token bucket rate limiter with Redis backend."""

    def __init__(self, redis_client):
        self.redis = redis_client

    def is_allowed(self, key, limit, window_seconds):
        """Check if request is within rate limit."""
        pipe = self.redis.pipeline()
        now = time.time()
        window_start = now - window_seconds

        # Remove old entries
        pipe.zremrangebyscore(key, 0, window_start)
        # Count current entries
        pipe.zcard(key)
        # Add new entry
        pipe.zadd(key, {str(now): now})
        # Set expiry
        pipe.expire(key, window_seconds)

        results = pipe.execute()
        current_count = results[1]

        return current_count < limit

def rate_limit(limit=100, window=3600, key_func=None):
    """Rate limiting decorator."""
    def decorator(f):
        @wraps(f)
        def decorated(*args, **kwargs):
            if key_func:
                key = f"rate_limit:{key_func()}"
            else:
                key = f"rate_limit:{request.remote_addr}:{f.__name__}"

            if not rate_limiter.is_allowed(key, limit, window):
                return {
                    'error': 'Rate limit exceeded',
                    'retry_after': window
                }, 429

            return f(*args, **kwargs)
        return decorated
    return decorator
```

### SQL Injection Prevention

```python
# NEVER: String concatenation
# query = f"SELECT * FROM users WHERE id = {user_id}"

# ALWAYS: Parameterized queries
from sqlalchemy import text

def get_user_secure(user_id):
    """Safe parameterized query."""
    query = text("SELECT * FROM users WHERE id = :user_id")
    result = db.execute(query, {'user_id': user_id})
    return result.fetchone()

# For dynamic queries, use ORM
def search_users(filters):
    """Safe dynamic query with ORM."""
    query = User.query

    if 'name' in filters:
        # ORM handles escaping
        query = query.filter(User.name.ilike(f"%{filters['name']}%"))

    if 'role' in filters:
        query = query.filter(User.role == filters['role'])

    return query.all()
```

---

## Data Protection Patterns

### Encryption at Rest

```python
from cryptography.fernet import Fernet
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC
import base64
import os

class FieldEncryption:
    """Encrypt sensitive database fields."""

    def __init__(self, master_key):
        self.fernet = Fernet(master_key)

    @staticmethod
    def derive_key(password, salt):
        """Derive encryption key from password."""
        kdf = PBKDF2HMAC(
            algorithm=hashes.SHA256(),
            length=32,
            salt=salt,
            iterations=480000,
        )
        key = base64.urlsafe_b64encode(kdf.derive(password.encode()))
        return key

    def encrypt(self, plaintext):
        """Encrypt a field value."""
        if isinstance(plaintext, str):
            plaintext = plaintext.encode()
        return self.fernet.encrypt(plaintext).decode()

    def decrypt(self, ciphertext):
        """Decrypt a field value."""
        if isinstance(ciphertext, str):
            ciphertext = ciphertext.encode()
        return self.fernet.decrypt(ciphertext).decode()

# Usage in ORM
class User(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    email = db.Column(db.String(255))  # Not sensitive
    _ssn = db.Column('ssn', db.String(500))  # Encrypted

    @property
    def ssn(self):
        if self._ssn:
            return field_encryption.decrypt(self._ssn)
        return None

    @ssn.setter
    def ssn(self, value):
        if value:
            self._ssn = field_encryption.encrypt(value)
        else:
            self._ssn = None
```

### Secret Management

| Storage Type | Use Case | Example |
|--------------|----------|---------|
| Environment variables | Container config | `DATABASE_URL` |
| Secret manager | Application secrets | AWS Secrets Manager, HashiCorp Vault |
| Hardware Security Module | Cryptographic keys | AWS CloudHSM |

```python
# HashiCorp Vault integration
import hvac

class VaultClient:
    def __init__(self, url, token):
        self.client = hvac.Client(url=url, token=token)

    def get_secret(self, path):
        """Retrieve secret from Vault."""
        secret = self.client.secrets.kv.v2.read_secret_version(path=path)
        return secret['data']['data']

    def get_database_credentials(self, role):
        """Get dynamic database credentials."""
        creds = self.client.secrets.database.generate_credentials(role)
        return {
            'username': creds['data']['username'],
            'password': creds['data']['password'],
            'ttl': creds['lease_duration']
        }
```

---

## Security Anti-Patterns

### Anti-Pattern: Security Through Obscurity

| Bad Practice | Why It's Wrong | Correct Approach |
|--------------|----------------|------------------|
| Custom encryption algorithm | Untested, likely breakable | Use AES-256-GCM, ChaCha20-Poly1305 |
| Hidden admin URLs | Discovery via fuzzing | Proper authentication + authorization |
| Encoded (not encrypted) secrets | Base64 is reversible | Use proper encryption |

### Anti-Pattern: Trusting Client Input

```python
# BAD: Trusting client-provided data
@app.route('/admin')
def admin_panel():
    # Client can forge this header!
    if request.headers.get('X-Is-Admin') == 'true':
        return render_admin()

# GOOD: Server-side verification
@app.route('/admin')
@login_required
def admin_panel():
    if not current_user.has_role('admin'):
        abort(403)
    return render_admin()
```

### Anti-Pattern: Hardcoded Secrets

```python
# BAD: Hardcoded credentials
DATABASE_URL = "postgresql://admin:SuperSecret123@localhost/db"
API_KEY = "sk-1234567890abcdef"

# GOOD: Environment variables + secret management
import os
DATABASE_URL = os.environ['DATABASE_URL']
API_KEY = vault_client.get_secret('api/keys')['api_key']
```

### Anti-Pattern: Verbose Error Messages

```python
# BAD: Reveals internal information
except Exception as e:
    return {'error': str(e), 'stack_trace': traceback.format_exc()}, 500

# GOOD: Generic message, detailed logging
except Exception as e:
    logger.exception(f"Internal error: {e}")
    return {'error': 'An internal error occurred', 'request_id': request_id}, 500
```

---

## Security Tools Reference

| Category | Tools |
|----------|-------|
| SAST (Static Analysis) | Semgrep, SonarQube, Bandit (Python), ESLint security plugins |
| DAST (Dynamic Analysis) | OWASP ZAP, Burp Suite, Nikto |
| Dependency Scanning | Snyk, Dependabot, npm audit, pip-audit |
| Secret Detection | GitLeaks, TruffleHog, detect-secrets |
| Container Security | Trivy, Clair, Anchore |
| Infrastructure | Terraform Sentinel, Checkov, tfsec |
