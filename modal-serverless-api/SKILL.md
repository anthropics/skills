---
name: modal-serverless-api
description: Guide for building production-ready serverless REST APIs on Modal with FastAPI. Use when building web services that need serverless deployment, scheduled tasks, persistent storage, or multi-tenant data isolation. Covers API patterns, background jobs, cron scheduling, and volume-based storage.
license: Apache-2.0
---

# Modal Serverless API Development

Build production-ready serverless REST APIs on Modal with FastAPI. Modal provides serverless compute, persistent storage via volumes, and scheduled execution with cron - all without managing infrastructure.

## When to Use This Skill

Use this skill when building:
- **REST APIs** that need serverless deployment without infrastructure management
- **Scheduled services** with cron jobs (polling, batch processing, cleanup tasks)
- **Multi-tenant applications** requiring data isolation per user/customer
- **Stateful services** needing persistent storage across function invocations
- **Background workers** that process queued tasks on a schedule

**Ideal for:** APIs with intermittent traffic, scheduled data processing, webhook receivers, or services that benefit from instant scaling.

**Not ideal for:** WebSocket servers, long-lived stateful connections, or services requiring <10ms response times.

## Core Concepts

### Modal Architecture

Modal is a serverless platform where you define **apps** containing **functions** that run in isolated containers:

```python
import modal

app = modal.App("my-api")

@app.function()
def my_function():
    return "Hello, Modal!"
```

**Key components:**
- **App**: Container for related functions and resources
- **Image**: Docker-like environment with dependencies
- **Function**: Serverless compute that scales to zero
- **Volume**: Persistent storage that survives across invocations
- **Cron**: Scheduled function execution

### FastAPI Integration

Modal serves FastAPI apps via ASGI:

```python
from fastapi import FastAPI

web_app = FastAPI()

@web_app.get("/")
def root():
    return {"message": "Hello"}

@app.function()
@modal.asgi_app()
def serve():
    return web_app
```

Your API becomes accessible at: `https://{workspace}--{app-name}-serve.modal.run`

## Quick Start Pattern

The basic structure for a Modal serverless API:

```python
import modal

# 1. Define app and dependencies
app = modal.App("my-service")
image = modal.Image.debian_slim().pip_install("fastapi")

# 2. Create persistent storage
volume = modal.Volume.from_name("my-data", create_if_missing=True)
VOLUME_PATH = "/data"

# 3. Define FastAPI app
from fastapi import FastAPI
web_app = FastAPI()

@web_app.get("/")
def root():
    return {"status": "online"}

# 4. Serve via ASGI
@app.function(image=image, volumes={VOLUME_PATH: volume})
@modal.asgi_app()
def api():
    return web_app

# 5. Add scheduled background tasks
@app.function(
    image=image,
    volumes={VOLUME_PATH: volume},
    schedule=modal.Cron("*/5 * * * *")  # Every 5 minutes
)
def background_job():
    print("Running scheduled task...")
    volume.commit()  # Persist changes
```

## Key Patterns Covered

### 1. REST API Design
- FastAPI endpoint patterns
- Request validation with Pydantic
- Authentication and authorization
- Error handling and status codes
- Content negotiation (JSON/HTML)

→ See [references/fastapi_patterns.md](./references/fastapi_patterns.md)

### 2. Persistent Storage
- Volume-based file storage
- Reading/writing JSON data
- Committing changes for persistence
- Directory organization patterns

→ See [references/modal_volumes.md](./references/modal_volumes.md)

### 3. Scheduled Tasks
- Cron-based polling patterns
- Background job architecture
- Checking for due work
- Preventing duplicate execution

→ See [references/polling_scheduler.md](./references/polling_scheduler.md)

### 4. Multi-Tenant Isolation
- Hash-based directory structures
- User-scoped data access
- API key authentication
- Row-level security patterns

→ See [references/multi_tenant_storage.md](./references/multi_tenant_storage.md)

### 5. Security Patterns
- Encryption at rest
- API key validation
- Secrets management
- Rate limiting

→ See [references/security_patterns.md](./references/security_patterns.md)

## Common Workflows

### Deploy a New API

1. **Create app.py** with Modal app definition
2. **Test locally**: `modal serve app.py`
3. **Deploy to production**: `modal deploy app.py`
4. **Access at**: `https://{workspace}--{app-name}-{function}.modal.run`

### Add Scheduled Background Job

```python
@app.function(
    schedule=modal.Cron("0 * * * *"),  # Every hour
    volumes={VOLUME_PATH: volume}
)
def hourly_cleanup():
    # Process work, clean up old data, etc.
    volume.commit()  # Persist changes
```

### Store User Data in Volume

```python
import json
from pathlib import Path

@app.function(volumes={VOLUME_PATH: volume})
def save_user_data(user_id: str, data: dict):
    user_dir = Path(f"{VOLUME_PATH}/users/{user_id}")
    user_dir.mkdir(parents=True, exist_ok=True)
    
    with open(user_dir / "data.json", "w") as f:
        json.dump(data, f)
    
    volume.commit()  # Critical: persist changes
```

### Implement Authentication

```python
from fastapi import Security, HTTPException
from fastapi.security import HTTPBearer

security = HTTPBearer()

def validate_api_key(api_key: str) -> bool:
    # Check against your auth provider
    return api_key.startswith("valid-")

@web_app.get("/protected")
def protected_route(credentials: HTTPAuthorizationCredentials = Security(security)):
    api_key = credentials.credentials
    if not validate_api_key(api_key):
        raise HTTPException(status_code=401, detail="Invalid API key")
    return {"message": "Authorized"}
```

## Best Practices

**Image Configuration:**
- Install all dependencies in the image (not at runtime)
- Use `.add_local_python_source()` for local modules
- Keep images minimal for faster cold starts

**Volume Usage:**
- Always call `volume.commit()` after writes
- Use hash-based directories for user isolation (e.g., `{hash(user_id)}/`)
- Organize by time buckets for time-series data (e.g., `{date}/{hour}/`)

**Scheduled Functions:**
- Use cron for polling patterns (check for work every minute)
- Keep cron jobs idempotent (safe to run multiple times)
- Handle race conditions (multiple instances may spawn)

**Error Handling:**
- Return proper HTTP status codes
- Log errors for debugging (`print()` shows in Modal logs)
- Validate inputs with Pydantic models

**Performance:**
- Batch operations when possible
- Use efficient file formats (JSON for small data, binary for large)
- Consider cold start times (keep images lean)

## Examples

See the `examples/` directory for working implementations:

- **basic_rest_api.py** - Simple REST API with CRUD operations
- **scheduled_tasks.py** - Polling scheduler checking for due work
- **multi_tenant_storage.py** - User-isolated data storage
- **encrypted_storage.py** - Encryption at rest patterns

## Deployment Commands

```bash
# Test locally (hot reload)
modal serve app.py

# Deploy to production
modal deploy app.py

# View logs
modal app logs {app-name}

# List running apps
modal app list

# Stop an app
modal app stop {app-name}
```

## Modal-Specific Considerations

**Cold Starts:**
- First request after idle takes ~1-3 seconds
- Keep images minimal to reduce cold start time
- Consider warmup patterns for latency-sensitive APIs

**Concurrency:**
- Functions scale automatically based on load
- Multiple instances can run simultaneously
- Design for concurrent access (file locks, idempotency)

**Costs:**
- Pay per compute time (seconds of execution)
- Free tier includes generous compute credits
- Volumes charged per GB-month

**Limitations:**
- No WebSocket support (use ASGI but connections may drop)
- Maximum 15-minute function timeout
- Cold starts not ideal for <10ms latency requirements

## Additional Resources

- **Modal Documentation**: https://modal.com/docs
- **FastAPI Guide**: https://fastapi.tiangolo.com
- **Cron Expression Reference**: https://crontab.guru

For detailed guides on specific patterns, see the `references/` directory.
