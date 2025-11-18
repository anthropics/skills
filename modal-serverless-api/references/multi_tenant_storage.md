# Multi-Tenant Storage Patterns

Design patterns for isolating user data in multi-tenant applications, ensuring users can only access their own resources.

## Hash-Based User Isolation

Use deterministic hashing to create user-specific directories:

```python
import hashlib

def get_user_hash(user_id: str) -> str:
    """
    Generate consistent hash for user directory.
    
    Benefits:
    - Deterministic: Same user_id always produces same hash
    - Obfuscates user IDs from filesystem
    - Short: 16 chars vs full UUID
    """
    return hashlib.sha256(user_id.encode()).hexdigest()[:16]

# Directory structure:
# /data/users/{user_hash}/
# /data/users/a1b2c3d4e5f6g7h8/profile.json
# /data/users/9z8y7x6w5v4u3t2s/profile.json
```

## Storage Layout Patterns

### Pattern 1: Resource-First, Then User

Organize by resource type, then user:

```
/data/
  schedules/
    a1b2c3d4/  # User 1
      schedule_1.json
      schedule_2.json
    9z8y7x6w/  # User 2
      schedule_1.json
  results/
    a1b2c3d4/
      result_1.json
    9z8y7x6w/
      result_1.json
```

**Good for:**
- APIs with multiple resource types
- When you need to iterate all resources of one type
- Clear separation of concerns

**Implementation:**
```python
def get_resource_path(user_id: str, resource_type: str, resource_id: str) -> Path:
    user_hash = get_user_hash(user_id)
    return Path(VOLUME_PATH) / resource_type / user_hash / f"{resource_id}.json"

def save_schedule(user_id: str, schedule_id: str, data: dict):
    path = get_resource_path(user_id, "schedules", schedule_id)
    path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(path, "w") as f:
        json.dump(data, f)
    
    volume.commit()

def list_user_schedules(user_id: str) -> list[dict]:
    user_hash = get_user_hash(user_id)
    schedule_dir = Path(VOLUME_PATH) / "schedules" / user_hash
    
    if not schedule_dir.exists():
        return []
    
    schedules = []
    for file in schedule_dir.glob("*.json"):
        with open(file, "r") as f:
            schedules.append(json.load(f))
    
    return schedules
```

### Pattern 2: User-First, Then Resource

Organize by user, then resource type:

```
/data/
  users/
    a1b2c3d4/
      schedules/
        schedule_1.json
        schedule_2.json
      results/
        result_1.json
      profile.json
    9z8y7x6w/
      schedules/
      results/
      profile.json
```

**Good for:**
- User-centric applications
- When you frequently access all of a user's data
- Easier to export/delete all user data

**Implementation:**
```python
def get_user_resource_path(user_id: str, resource_type: str, resource_id: str) -> Path:
    user_hash = get_user_hash(user_id)
    return Path(VOLUME_PATH) / "users" / user_hash / resource_type / f"{resource_id}.json"

def save_user_resource(user_id: str, resource_type: str, resource_id: str, data: dict):
    path = get_user_resource_path(user_id, resource_type, resource_id)
    path.parent.mkdir(parents=True, exist_ok=True)
    
    with open(path, "w") as f:
        json.dump(data, f)
    
    volume.commit()

def delete_all_user_data(user_id: str):
    """Delete all data for a user (GDPR compliance)."""
    user_hash = get_user_hash(user_id)
    user_dir = Path(VOLUME_PATH) / "users" / user_hash
    
    if user_dir.exists():
        import shutil
        shutil.rmtree(user_dir)
        volume.commit()
```

## API Key-Based Authentication

Validate API keys and extract user identity:

```python
from fastapi import Security, HTTPException
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials

security = HTTPBearer()

def validate_and_extract_user(api_key: str) -> str:
    """
    Validate API key and return user ID.
    
    In production, this should:
    1. Call your auth service
    2. Verify the key is valid
    3. Return the associated user ID
    """
    # Example: Call external auth service
    response = requests.get(
        "https://your-auth-service.com/validate",
        headers={"Authorization": f"Bearer {api_key}"}
    )
    
    if response.status_code != 200:
        raise HTTPException(status_code=401, detail="Invalid API key")
    
    return response.json()["user_id"]

async def get_current_user(credentials: HTTPAuthorizationCredentials = Security(security)) -> str:
    """Dependency that validates auth and returns user ID."""
    api_key = credentials.credentials
    return validate_and_extract_user(api_key)

# Usage in endpoints
@web_app.get("/schedules")
def list_schedules(user_id: str = Depends(get_current_user)):
    """Automatically filtered to current user's schedules."""
    return list_user_schedules(user_id)
```

## Row-Level Security Pattern

Always verify ownership before returning data:

```python
@web_app.get("/schedules/{schedule_id}")
def get_schedule(schedule_id: str, user_id: str = Depends(get_current_user)):
    """Get specific schedule with ownership verification."""
    
    # Load schedule
    schedule = load_schedule(schedule_id)
    
    if schedule is None:
        raise HTTPException(status_code=404, detail="Schedule not found")
    
    # CRITICAL: Verify ownership
    if schedule.get("user_id") != user_id:
        raise HTTPException(status_code=403, detail="Forbidden")
    
    # Remove sensitive fields before returning
    schedule.pop("api_key", None)
    
    return schedule
```

**Key points:**
- Always check `schedule["user_id"] == user_id`
- Return 404 for both "not found" and "not yours" (don't leak existence)
- OR return 403 if you want to indicate forbidden access
- Strip sensitive fields before returning

## Automatic User Filtering

Build user filtering into your data access layer:

```python
class UserDataStore:
    def __init__(self, user_id: str, volume_path: str):
        self.user_id = user_id
        self.user_hash = get_user_hash(user_id)
        self.volume_path = volume_path
    
    def save_resource(self, resource_type: str, resource_id: str, data: dict):
        """Save resource with automatic user scoping."""
        # Automatically inject user_id
        data["user_id"] = self.user_id
        
        path = Path(self.volume_path) / resource_type / self.user_hash / f"{resource_id}.json"
        path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(path, "w") as f:
            json.dump(data, f)
        
        volume.commit()
    
    def load_resource(self, resource_type: str, resource_id: str) -> dict:
        """Load resource with automatic ownership check."""
        path = Path(self.volume_path) / resource_type / self.user_hash / f"{resource_id}.json"
        
        if not path.exists():
            return None
        
        with open(path, "r") as f:
            data = json.load(f)
        
        # Verify ownership
        if data.get("user_id") != self.user_id:
            raise PermissionError(f"Resource {resource_id} does not belong to user {self.user_id}")
        
        return data
    
    def list_resources(self, resource_type: str) -> list[dict]:
        """List all resources of type for this user."""
        dir_path = Path(self.volume_path) / resource_type / self.user_hash
        
        if not dir_path.exists():
            return []
        
        resources = []
        for file in dir_path.glob("*.json"):
            with open(file, "r") as f:
                resources.append(json.load(f))
        
        return resources

# Usage
@web_app.post("/schedules")
def create_schedule(schedule: ScheduleCreate, user_id: str = Depends(get_current_user)):
    store = UserDataStore(user_id, VOLUME_PATH)
    
    schedule_id = str(uuid.uuid4())
    store.save_resource("schedules", schedule_id, schedule.dict())
    
    return {"id": schedule_id}

@web_app.get("/schedules")
def list_schedules(user_id: str = Depends(get_current_user)):
    store = UserDataStore(user_id, VOLUME_PATH)
    return store.list_resources("schedules")
```

## API Key Storage

Never store or return API keys in responses:

```python
@web_app.post("/schedules")
def create_schedule(schedule: ScheduleCreate, credentials = Security(security)):
    api_key = credentials.credentials
    user_id = validate_and_extract_user(api_key)
    
    schedule_data = schedule.dict()
    # Store API key for execution (but encrypted!)
    schedule_data["api_key"] = encrypt_api_key(api_key)
    schedule_data["user_id"] = user_id
    
    save_schedule(user_id, schedule_id, schedule_data)
    
    # NEVER return API key in response
    schedule_data.pop("api_key")
    
    return schedule_data
```

## Testing Multi-Tenancy

Create test users and verify isolation:

```python
def test_user_isolation():
    # User A creates a schedule
    user_a_key = "test-key-user-a"
    response_a = client.post(
        "/schedules",
        json={"name": "User A Schedule"},
        headers={"Authorization": f"Bearer {user_a_key}"}
    )
    schedule_id = response_a.json()["id"]
    
    # User B tries to access User A's schedule
    user_b_key = "test-key-user-b"
    response_b = client.get(
        f"/schedules/{schedule_id}",
        headers={"Authorization": f"Bearer {user_b_key}"}
    )
    
    # Should return 403 or 404
    assert response_b.status_code in [403, 404]
    
    # User B lists schedules - should be empty
    response_b_list = client.get(
        "/schedules",
        headers={"Authorization": f"Bearer {user_b_key}"}
    )
    assert len(response_b_list.json()) == 0
```

## Performance Considerations

**Hash-Based Directories:**
- O(user's resources) instead of O(all resources)
- Fast lookups for user-specific data
- No database required

**Caching:**
```python
from functools import lru_cache

@lru_cache(maxsize=1000)
def get_user_hash_cached(user_id: str) -> str:
    """Cache hash computation."""
    return get_user_hash(user_id)
```

**Batch Operations:**
```python
def list_all_user_schedules_batch(user_ids: list[str]) -> dict[str, list[dict]]:
    """Load schedules for multiple users in one volume scan."""
    result = {user_id: [] for user_id in user_ids}
    user_hashes = {get_user_hash(uid): uid for uid in user_ids}
    
    schedule_dir = Path(VOLUME_PATH) / "schedules"
    
    for user_hash_dir in schedule_dir.iterdir():
        if user_hash_dir.name in user_hashes:
            user_id = user_hashes[user_hash_dir.name]
            
            for file in user_hash_dir.glob("*.json"):
                with open(file, "r") as f:
                    result[user_id].append(json.load(f))
    
    return result
```

## Security Checklist

✅ **Hash user IDs** in filesystem paths  
✅ **Validate API keys** on every request  
✅ **Check ownership** before returning data  
✅ **Strip sensitive fields** (API keys, etc.) from responses  
✅ **Use dependency injection** for consistent auth  
✅ **Test isolation** between users  
✅ **Log access attempts** for auditing  
✅ **Encrypt stored API keys** if needed for execution  
✅ **Return 403/404** for unauthorized access  
✅ **Implement GDPR compliance** (delete all user data)

## Common Pitfalls

**Leaking Existence:**
```python
# ❌ Bad: Reveals whether resource exists
if not schedule_exists(schedule_id):
    raise HTTPException(status_code=404)
if schedule.user_id != user_id:
    raise HTTPException(status_code=403)

# ✅ Better: Same error for both cases
schedule = load_schedule(schedule_id)
if not schedule or schedule.get("user_id") != user_id:
    raise HTTPException(status_code=404, detail="Schedule not found")
```

**Trusting Client Data:**
```python
# ❌ Bad: Client controls user_id!
@web_app.post("/schedules")
def create_schedule(schedule: ScheduleCreate, user_id: str):
    save_schedule(user_id, schedule.dict())

# ✅ Good: Extract from validated auth
@web_app.post("/schedules")
def create_schedule(schedule: ScheduleCreate, user_id: str = Depends(get_current_user)):
    save_schedule(user_id, schedule.dict())
```

**Returning Sensitive Data:**
```python
# ❌ Bad: Returns other users' API keys
@web_app.get("/schedules/{schedule_id}")
def get_schedule(schedule_id: str):
    return load_schedule(schedule_id)  # Contains api_key field!

# ✅ Good: Strip sensitive fields
@web_app.get("/schedules/{schedule_id}")
def get_schedule(schedule_id: str, user_id: str = Depends(get_current_user)):
    schedule = load_schedule(schedule_id)
    if schedule.get("user_id") != user_id:
        raise HTTPException(status_code=404)
    
    # Remove sensitive fields
    schedule.pop("api_key", None)
    return schedule
```
