# Security Patterns for Modal APIs

Security best practices for building production-ready APIs on Modal, covering encryption, secrets management, and common vulnerabilities.

## Encryption at Rest

Encrypt sensitive data stored in volumes using Fernet (AES-128-CBC):

```python
from cryptography.fernet import Fernet
import base64
import json

def generate_encryption_key() -> bytes:
    """Generate a new encryption key."""
    return Fernet.generate_key()

def encrypt_data(data: dict, key: bytes) -> bytes:
    """Encrypt JSON data."""
    fernet = Fernet(key)
    json_bytes = json.dumps(data).encode()
    return fernet.encrypt(json_bytes)

def decrypt_data(encrypted: bytes, key: bytes) -> dict:
    """Decrypt JSON data."""
    fernet = Fernet(key)
    json_bytes = fernet.decrypt(encrypted)
    return json.loads(json_bytes)

# Usage
@app.function(volumes={VOLUME_PATH: volume})
def save_encrypted(user_id: str, data: dict, encryption_key: bytes):
    user_hash = get_user_hash(user_id)
    file_path = Path(VOLUME_PATH) / "users" / user_hash / "data.enc"
    file_path.parent.mkdir(parents=True, exist_ok=True)
    
    encrypted = encrypt_data(data, encryption_key)
    with open(file_path, "wb") as f:
        f.write(encrypted)
    
    volume.commit()

@app.function(volumes={VOLUME_PATH: volume})
def load_encrypted(user_id: str, encryption_key: bytes) -> dict:
    user_hash = get_user_hash(user_id)
    file_path = Path(VOLUME_PATH) / "users" / user_hash / "data.enc"
    
    with open(file_path, "rb") as f:
        encrypted = f.read()
    
    return decrypt_data(encrypted, encryption_key)
```

## Secrets Management with Modal

Store sensitive values in Modal secrets:

```python
# Create secret via CLI
# modal secret create my-api-secrets \
#   ENCRYPTION_KEY=base64_encoded_key \
#   DATABASE_URL=postgres://...

import modal
import os

# Reference secret in app
encryption_secret = modal.Secret.from_name("my-api-secrets")

@app.function(secrets=[encryption_secret])
def use_secret():
    # Access via environment variables
    encryption_key = os.environ["ENCRYPTION_KEY"]
    db_url = os.environ["DATABASE_URL"]
    
    # Use them...
    return "Secrets loaded"
```

**Never:**
- Commit secrets to git
- Log secret values
- Return secrets in API responses
- Store secrets in plaintext files

## Environment-Specific Secrets

Use different secrets for dev/staging/prod:

```python
# Check environment
import os as local_os

env = local_os.getenv("ENVIRONMENT", "dev")

if env == "production":
    secrets = [modal.Secret.from_name("prod-secrets")]
else:
    secrets = [modal.Secret.from_name("dev-secrets")]

@app.function(secrets=secrets)
def api_function():
    # Automatically uses correct secrets
    api_key = os.environ["API_KEY"]
```

## Dev Mode Toggle

Disable encryption for local development:

```python
import os as local_os

DEV_MODE = local_os.getenv("DEV_MODE", "false") == "true"

def save_data(path: Path, data: dict, encryption_key: bytes = None):
    """Save data with optional encryption."""
    if DEV_MODE:
        # Dev: plaintext JSON for easy debugging
        with open(path, "w") as f:
            json.dump(data, f, indent=2)
    else:
        # Production: encrypted binary
        encrypted = encrypt_data(data, encryption_key)
        with open(path, "wb") as f:
            f.write(encrypted)
    
    volume.commit()

def load_data(path: Path, encryption_key: bytes = None) -> dict:
    """Load data with optional decryption."""
    if DEV_MODE:
        with open(path, "r") as f:
            return json.load(f)
    else:
        with open(path, "rb") as f:
            encrypted = f.read()
        return decrypt_data(encrypted, encryption_key)
```

## Rate Limiting

Prevent abuse with simple rate limiting:

```python
from datetime import datetime, timedelta
from collections import defaultdict

# In-memory rate limit tracking (per-instance)
rate_limit_tracker = defaultdict(list)

def check_rate_limit(user_id: str, max_requests: int = 100, window_minutes: int = 60) -> bool:
    """
    Check if user is within rate limit.
    
    Returns True if allowed, False if rate limited.
    """
    now = datetime.utcnow()
    cutoff = now - timedelta(minutes=window_minutes)
    
    # Clean old requests
    rate_limit_tracker[user_id] = [
        req_time for req_time in rate_limit_tracker[user_id]
        if req_time > cutoff
    ]
    
    # Check limit
    if len(rate_limit_tracker[user_id]) >= max_requests:
        return False
    
    # Add this request
    rate_limit_tracker[user_id].append(now)
    return True

@web_app.post("/items")
def create_item(item: ItemCreate, user_id: str = Depends(get_current_user)):
    # Check rate limit
    if not check_rate_limit(user_id, max_requests=100, window_minutes=60):
        raise HTTPException(
            status_code=429,
            detail="Rate limit exceeded. Try again later."
        )
    
    # Process request
    return create_item_for_user(user_id, item)
```

**For production:** Use Redis or a database for distributed rate limiting across instances.

## Input Validation

Always validate and sanitize inputs:

```python
from pydantic import BaseModel, Field, validator

class CreateSchedule(BaseModel):
    agent_id: str = Field(..., regex=r"^agent-[a-zA-Z0-9\-]+$")
    message: str = Field(..., min_length=1, max_length=10000)
    execute_at: datetime
    
    @validator("execute_at")
    def validate_future_time(cls, v):
        """Ensure execution time has timezone info."""
        if v.tzinfo is None:
            raise ValueError("execute_at must have timezone info")
        return v
    
    @validator("message")
    def sanitize_message(cls, v):
        """Remove potentially dangerous characters."""
        # Strip null bytes
        v = v.replace("\x00", "")
        return v.strip()

@web_app.post("/schedules")
def create_schedule(schedule: CreateSchedule, user_id: str = Depends(get_current_user)):
    # Pydantic automatically validates!
    return save_schedule(user_id, schedule.dict())
```

## SQL Injection Prevention

If using a database, always use parameterized queries:

```python
import sqlite3

# ❌ BAD: SQL injection vulnerability
def get_user_bad(username: str):
    conn = sqlite3.connect("db.sqlite")
    cursor = conn.execute(f"SELECT * FROM users WHERE username = '{username}'")
    return cursor.fetchone()

# ✅ GOOD: Parameterized query
def get_user_good(username: str):
    conn = sqlite3.connect("db.sqlite")
    cursor = conn.execute("SELECT * FROM users WHERE username = ?", (username,))
    return cursor.fetchone()
```

## Path Traversal Prevention

Prevent directory traversal attacks:

```python
from pathlib import Path

def get_safe_file_path(user_id: str, filename: str) -> Path:
    """Get file path with path traversal prevention."""
    user_hash = get_user_hash(user_id)
    user_dir = Path(VOLUME_PATH) / "users" / user_hash
    
    # Sanitize filename
    filename = Path(filename).name  # Removes directory components
    
    # Construct full path
    file_path = user_dir / filename
    
    # Verify it's within user's directory
    try:
        file_path.resolve().relative_to(user_dir.resolve())
    except ValueError:
        raise HTTPException(status_code=400, detail="Invalid file path")
    
    return file_path

# ❌ BAD: Allows path traversal
@web_app.get("/files/{filename}")
def get_file_bad(filename: str, user_id: str = Depends(get_current_user)):
    # filename could be "../../../etc/passwd"
    file_path = Path(VOLUME_PATH) / "users" / user_id / filename
    return file_path.read_text()

# ✅ GOOD: Sanitized and validated
@web_app.get("/files/{filename}")
def get_file_good(filename: str, user_id: str = Depends(get_current_user)):
    file_path = get_safe_file_path(user_id, filename)
    if not file_path.exists():
        raise HTTPException(status_code=404)
    return file_path.read_text()
```

## CORS Configuration

Configure CORS carefully:

```python
from fastapi.middleware.cors import CORSMiddleware

# ❌ BAD: Allows all origins (development only!)
web_app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# ✅ GOOD: Specific origins only
web_app.add_middleware(
    CORSMiddleware,
    allow_origins=[
        "https://myapp.com",
        "https://app.mycompany.com"
    ],
    allow_credentials=True,
    allow_methods=["GET", "POST", "PUT", "DELETE"],
    allow_headers=["Authorization", "Content-Type"],
)
```

## Security Headers

Add security headers to responses:

```python
from fastapi import Response
from fastapi.middleware.trustedhost import TrustedHostMiddleware

# Trusted host middleware
web_app.add_middleware(
    TrustedHostMiddleware,
    allowed_hosts=["*.modal.run", "myapp.com"]
)

@web_app.middleware("http")
async def add_security_headers(request: Request, call_next):
    response = await call_next(request)
    
    # Prevent clickjacking
    response.headers["X-Frame-Options"] = "DENY"
    
    # Prevent MIME type sniffing
    response.headers["X-Content-Type-Options"] = "nosniff"
    
    # XSS protection
    response.headers["X-XSS-Protection"] = "1; mode=block"
    
    # HTTPS only (if using HTTPS)
    response.headers["Strict-Transport-Security"] = "max-age=31536000; includeSubDomains"
    
    return response
```

## Logging Best Practices

Log security events without exposing sensitive data:

```python
import logging

logger = logging.getLogger(__name__)

def mask_api_key(api_key: str) -> str:
    """Mask API key for logging."""
    if len(api_key) < 8:
        return "****"
    return f"{api_key[:4]}...{api_key[-4:]}"

@web_app.post("/items")
def create_item(item: ItemCreate, credentials = Security(security)):
    api_key = credentials.credentials
    
    # ❌ BAD: Logs full API key
    logger.info(f"User {api_key} creating item")
    
    # ✅ GOOD: Logs masked key
    logger.info(f"User {mask_api_key(api_key)} creating item: {item.name}")
    
    try:
        result = create_item_internal(item)
        logger.info(f"Item created: {result['id']}")
        return result
    except Exception as e:
        # Log error without sensitive data
        logger.error(f"Failed to create item: {type(e).__name__}")
        raise
```

## Dependency Versions

Pin dependency versions to avoid supply chain attacks:

```python
# requirements.txt
fastapi==0.104.1
pydantic==2.5.0
cryptography==41.0.7
# NOT: fastapi>=0.100.0
```

## Security Checklist

✅ **Encrypt sensitive data** at rest  
✅ **Use Modal secrets** for credentials  
✅ **Validate all inputs** with Pydantic  
✅ **Prevent path traversal** in file operations  
✅ **Use parameterized queries** for databases  
✅ **Configure CORS** restrictively  
✅ **Add security headers** to responses  
✅ **Implement rate limiting** for public endpoints  
✅ **Log security events** (without sensitive data)  
✅ **Pin dependency versions**  
✅ **Never commit secrets** to git  
✅ **Sanitize error messages** (don't leak implementation details)  
✅ **Use HTTPS** in production  
✅ **Regularly update dependencies**

## Common Vulnerabilities

### 1. Exposing Secrets in Logs

```python
# ❌ BAD
logger.info(f"API key: {api_key}")

# ✅ GOOD
logger.info(f"API key: {mask_api_key(api_key)}")
```

### 2. Trusting User Input for Paths

```python
# ❌ BAD
file_path = Path(BASE_DIR) / user_provided_path

# ✅ GOOD
file_path = get_safe_file_path(user_id, sanitize_filename(user_provided_path))
```

### 3. Returning Detailed Error Messages

```python
# ❌ BAD: Leaks implementation details
try:
    execute_query()
except DatabaseError as e:
    return {"error": str(e)}  # Exposes DB structure

# ✅ GOOD: Generic error message
try:
    execute_query()
except DatabaseError as e:
    logger.error(f"Database error: {e}")
    raise HTTPException(status_code=500, detail="Internal server error")
```

### 4. Not Validating Ownership

```python
# ❌ BAD: No ownership check
@web_app.delete("/items/{item_id}")
def delete_item(item_id: str):
    delete_item_from_db(item_id)  # Anyone can delete anyone's items!

# ✅ GOOD: Verify ownership
@web_app.delete("/items/{item_id}")
def delete_item(item_id: str, user_id: str = Depends(get_current_user)):
    item = load_item(item_id)
    if item.get("user_id") != user_id:
        raise HTTPException(status_code=403)
    delete_item_from_db(item_id)
```

## Testing Security

```python
def test_cannot_access_other_users_data():
    """Test multi-tenant isolation."""
    # User A creates data
    response_a = client.post(
        "/items",
        json={"name": "Secret"},
        headers={"Authorization": "Bearer user_a_key"}
    )
    item_id = response_a.json()["id"]
    
    # User B tries to access
    response_b = client.get(
        f"/items/{item_id}",
        headers={"Authorization": "Bearer user_b_key"}
    )
    
    assert response_b.status_code == 403

def test_rate_limiting():
    """Test rate limits prevent abuse."""
    for i in range(101):
        response = client.post("/items", json={"name": f"Item {i}"})
    
    # 101st request should be rate limited
    assert response.status_code == 429

def test_path_traversal_blocked():
    """Test directory traversal prevention."""
    response = client.get(
        "/files/../../../../etc/passwd",
        headers={"Authorization": "Bearer valid_key"}
    )
    
    assert response.status_code == 400
```
