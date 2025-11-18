# Modal Volumes: Persistent Storage Patterns

Modal Volumes provide persistent, network-attached storage that survives across function invocations. Think of them as a shared filesystem accessible to all your functions.

## Creating and Mounting Volumes

```python
import modal

app = modal.App("my-app")

# Create or reference existing volume
volume = modal.Volume.from_name("my-data", create_if_missing=True)

# Mount at a path in your container
VOLUME_PATH = "/data"

@app.function(volumes={VOLUME_PATH: volume})
def my_function():
    # Volume is now accessible at /data
    pass
```

## Writing Data

**Critical: Always call `volume.commit()` after writes!**

```python
from pathlib import Path
import json

@app.function(volumes={VOLUME_PATH: volume})
def save_data(data: dict):
    # Write to volume
    file_path = Path(VOLUME_PATH) / "data.json"
    with open(file_path, "w") as f:
        json.dump(data, f)
    
    # CRITICAL: Commit to persist changes
    volume.commit()
```

Without `.commit()`, changes are lost when the function exits.

## Reading Data

```python
@app.function(volumes={VOLUME_PATH: volume})
def read_data():
    file_path = Path(VOLUME_PATH) / "data.json"
    
    if not file_path.exists():
        return None
    
    with open(file_path, "r") as f:
        return json.load(f)
```

No commit needed for reads.

## Directory Organization Patterns

### Hash-Based User Isolation

For multi-tenant apps, isolate user data using hashed directories:

```python
import hashlib

def get_user_hash(user_id: str) -> str:
    """Generate deterministic hash for user."""
    return hashlib.sha256(user_id.encode()).hexdigest()[:16]

@app.function(volumes={VOLUME_PATH: volume})
def save_user_file(user_id: str, filename: str, content: bytes):
    user_hash = get_user_hash(user_id)
    user_dir = Path(VOLUME_PATH) / "users" / user_hash
    user_dir.mkdir(parents=True, exist_ok=True)
    
    file_path = user_dir / filename
    with open(file_path, "wb") as f:
        f.write(content)
    
    volume.commit()
```

**Directory structure:**
```
/data/
  users/
    a1b2c3d4e5f6g7h8/  # User 1's hash
      data.json
      settings.json
    9z8y7x6w5v4u3t2s/  # User 2's hash
      data.json
```

**Benefits:**
- O(user's files) lookup instead of O(all files)
- Natural data isolation
- Obfuscates user IDs from filesystem

### Time-Bucketed Storage

For time-series data, organize by date/hour:

```python
from datetime import datetime

@app.function(volumes={VOLUME_PATH: volume})
def save_event(user_id: str, event_data: dict):
    now = datetime.utcnow()
    user_hash = get_user_hash(user_id)
    
    # /data/events/2025-11-18/15/a1b2c3/event_123.json
    event_dir = Path(VOLUME_PATH) / "events" / now.strftime("%Y-%m-%d") / str(now.hour) / user_hash
    event_dir.mkdir(parents=True, exist_ok=True)
    
    event_id = event_data.get("id", "unknown")
    with open(event_dir / f"{event_id}.json", "w") as f:
        json.dump(event_data, f)
    
    volume.commit()
```

**Benefits:**
- Efficient time-range queries (only check relevant hour buckets)
- Natural data partitioning
- Easy cleanup of old data (delete old date directories)

### Hierarchical Storage

For complex data models:

```python
# /data/{resource_type}/{user_hash}/{resource_id}.json
@app.function(volumes={VOLUME_PATH: volume})
def save_resource(user_id: str, resource_type: str, resource_id: str, data: dict):
    user_hash = get_user_hash(user_id)
    resource_dir = Path(VOLUME_PATH) / resource_type / user_hash
    resource_dir.mkdir(parents=True, exist_ok=True)
    
    with open(resource_dir / f"{resource_id}.json", "w") as f:
        json.dump(data, f)
    
    volume.commit()
```

**Directory structure:**
```
/data/
  schedules/
    a1b2c3d4/
      schedule_1.json
      schedule_2.json
  results/
    a1b2c3d4/
      result_1.json
  profiles/
    a1b2c3d4/
      profile.json
```

## Listing Files

```python
from pathlib import Path

@app.function(volumes={VOLUME_PATH: volume})
def list_user_files(user_id: str) -> list[str]:
    user_hash = get_user_hash(user_id)
    user_dir = Path(VOLUME_PATH) / "users" / user_hash
    
    if not user_dir.exists():
        return []
    
    # Get all JSON files
    return [f.name for f in user_dir.glob("*.json")]
```

## Deleting Files

```python
@app.function(volumes={VOLUME_PATH: volume})
def delete_user_file(user_id: str, filename: str):
    user_hash = get_user_hash(user_id)
    file_path = Path(VOLUME_PATH) / "users" / user_hash / filename
    
    if file_path.exists():
        file_path.unlink()  # Delete file
        volume.commit()  # Persist deletion
        return True
    return False
```

## Cleanup Patterns

### Remove Empty Directories

```python
@app.function(volumes={VOLUME_PATH: volume})
def cleanup_empty_dirs(base_path: str):
    """Remove empty directories recursively."""
    base = Path(VOLUME_PATH) / base_path
    
    for dir_path in sorted(base.rglob("*"), reverse=True):
        if dir_path.is_dir() and not any(dir_path.iterdir()):
            dir_path.rmdir()
    
    volume.commit()
```

### Delete Old Data

```python
from datetime import datetime, timedelta

@app.function(volumes={VOLUME_PATH: volume})
def cleanup_old_events(days_to_keep: int = 30):
    """Delete events older than specified days."""
    cutoff_date = datetime.utcnow() - timedelta(days=days_to_keep)
    events_dir = Path(VOLUME_PATH) / "events"
    
    for date_dir in events_dir.iterdir():
        if not date_dir.is_dir():
            continue
        
        # Parse date from directory name (YYYY-MM-DD)
        try:
            dir_date = datetime.strptime(date_dir.name, "%Y-%m-%d")
            if dir_date < cutoff_date:
                # Delete entire date directory
                import shutil
                shutil.rmtree(date_dir)
        except ValueError:
            continue
    
    volume.commit()
```

## Performance Considerations

**File Format Choice:**
- **JSON**: Easy debugging, human-readable, good for <1MB files
- **Binary (pickle, msgpack)**: Faster serialization for large data
- **CSV**: Good for tabular data, easy to process

**Batch Operations:**
```python
# Good: Batch writes with single commit
@app.function(volumes={VOLUME_PATH: volume})
def save_batch(items: list[dict]):
    for item in items:
        file_path = Path(VOLUME_PATH) / f"{item['id']}.json"
        with open(file_path, "w") as f:
            json.dump(item, f)
    volume.commit()  # Single commit for all writes

# Bad: Commit after each write (slow!)
@app.function(volumes={VOLUME_PATH: volume})
def save_batch_slow(items: list[dict]):
    for item in items:
        file_path = Path(VOLUME_PATH) / f"{item['id']}.json"
        with open(file_path, "w") as f:
            json.dump(item, f)
        volume.commit()  # Too many commits!
```

**Directory Scans:**
- Use `.glob()` with patterns instead of scanning all files
- Leverage hierarchical structure to limit scope
- Cache file lists when possible

## Common Pitfalls

**Forgetting to Commit:**
```python
# ❌ Wrong: Changes lost!
@app.function(volumes={VOLUME_PATH: volume})
def save_data(data: dict):
    with open(f"{VOLUME_PATH}/data.json", "w") as f:
        json.dump(data, f)
    # Missing volume.commit()!

# ✅ Correct
@app.function(volumes={VOLUME_PATH: volume})
def save_data(data: dict):
    with open(f"{VOLUME_PATH}/data.json", "w") as f:
        json.dump(data, f)
    volume.commit()  # Persist changes
```

**Race Conditions:**
```python
# ❌ Wrong: Two functions may overwrite each other
@app.function(volumes={VOLUME_PATH: volume})
def increment_counter():
    path = Path(VOLUME_PATH) / "counter.txt"
    count = int(path.read_text())
    count += 1
    path.write_text(str(count))
    volume.commit()

# ✅ Better: Use atomic operations or file locks
import fcntl

@app.function(volumes={VOLUME_PATH: volume})
def increment_counter():
    path = Path(VOLUME_PATH) / "counter.txt"
    with open(path, "r+") as f:
        fcntl.flock(f.fileno(), fcntl.LOCK_EX)  # Exclusive lock
        count = int(f.read())
        count += 1
        f.seek(0)
        f.write(str(count))
        f.truncate()
    volume.commit()
```

## Volume Reloading

If another function commits changes, reload the volume:

```python
@app.function(volumes={VOLUME_PATH: volume})
def read_latest_data():
    volume.reload()  # Get latest committed changes
    
    with open(f"{VOLUME_PATH}/data.json", "r") as f:
        return json.load(f)
```

Usually not needed - volumes are eventually consistent and updates propagate quickly.

## Testing with Volumes Locally

When running `modal serve app.py` locally, volumes are accessible and changes persist across hot reloads.

**Tips:**
- Use different volume names for dev/prod (`my-data-dev` vs `my-data-prod`)
- Inspect volume contents: `modal volume ls my-data`
- Download volume data: `modal volume get my-data /data/users users/`
