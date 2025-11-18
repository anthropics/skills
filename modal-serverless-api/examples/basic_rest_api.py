"""
Basic REST API on Modal with FastAPI

A minimal todo list API demonstrating:
- CRUD operations
- Multi-tenant storage with hash-based isolation
- Bearer token authentication
- Input validation
- Error handling

Deploy: modal deploy basic_rest_api.py
Test: modal serve basic_rest_api.py (then visit http://localhost:8000/docs)
"""

import modal
from fastapi import FastAPI, HTTPException, Security
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from pydantic import BaseModel, Field
from pathlib import Path
from datetime import datetime
import json
import hashlib
import uuid

# === Modal Setup ===

app = modal.App("basic-rest-api")

image = modal.Image.debian_slim().pip_install("fastapi")

volume = modal.Volume.from_name("rest-api-data", create_if_missing=True)
VOLUME_PATH = "/data"

# === FastAPI App ===

web_app = FastAPI(title="Todo API", version="1.0.0")
security = HTTPBearer()

# === Models ===

class TodoCreate(BaseModel):
    title: str = Field(..., min_length=1, max_length=200)
    description: str = Field(default="", max_length=1000)
    completed: bool = False

class TodoResponse(BaseModel):
    id: str
    title: str
    description: str
    completed: bool
    created_at: str
    user_id: str

# === Helpers ===

def get_user_hash(user_id: str) -> str:
    """Generate consistent hash for user directory."""
    return hashlib.sha256(user_id.encode()).hexdigest()[:16]

def validate_api_key(api_key: str) -> bool:
    """Validate API key (stub - replace with real validation)."""
    # In production: call your auth service
    return api_key.startswith("valid-")

async def get_current_user(credentials: HTTPAuthorizationCredentials = Security(security)) -> str:
    """Extract and validate user from Bearer token."""
    api_key = credentials.credentials
    
    if not validate_api_key(api_key):
        raise HTTPException(status_code=401, detail="Invalid API key")
    
    # In production: extract user ID from validated token
    return api_key  # For this example, use API key as user ID

def get_user_todos_dir(user_id: str) -> Path:
    """Get user's todo directory."""
    user_hash = get_user_hash(user_id)
    return Path(VOLUME_PATH) / "todos" / user_hash

# === Endpoints ===

@web_app.get("/")
def root():
    """API info."""
    return {
        "service": "Todo API",
        "version": "1.0.0",
        "endpoints": {
            "/todos": "List todos (GET)",
            "/todos": "Create todo (POST)",
            "/todos/{todo_id}": "Get todo (GET)",
            "/todos/{todo_id}": "Update todo (PUT)",
            "/todos/{todo_id}": "Delete todo (DELETE)",
        }
    }

@web_app.get("/todos")
@app.function(volumes={VOLUME_PATH: volume}, image=image)
async def list_todos(user_id: str = Security(get_current_user)):
    """List all todos for authenticated user."""
    todos_dir = get_user_todos_dir(user_id)
    
    if not todos_dir.exists():
        return []
    
    todos = []
    for todo_file in todos_dir.glob("*.json"):
        with open(todo_file, "r") as f:
            todos.append(json.load(f))
    
    return todos

@web_app.post("/todos", status_code=201)
@app.function(volumes={VOLUME_PATH: volume}, image=image)
async def create_todo(todo: TodoCreate, user_id: str = Security(get_current_user)):
    """Create a new todo."""
    todo_id = str(uuid.uuid4())
    todos_dir = get_user_todos_dir(user_id)
    todos_dir.mkdir(parents=True, exist_ok=True)
    
    todo_data = {
        "id": todo_id,
        "user_id": user_id,
        "title": todo.title,
        "description": todo.description,
        "completed": todo.completed,
        "created_at": datetime.utcnow().isoformat()
    }
    
    with open(todos_dir / f"{todo_id}.json", "w") as f:
        json.dump(todo_data, f)
    
    volume.commit()
    
    return todo_data

@web_app.get("/todos/{todo_id}")
@app.function(volumes={VOLUME_PATH: volume}, image=image)
async def get_todo(todo_id: str, user_id: str = Security(get_current_user)):
    """Get specific todo by ID."""
    todos_dir = get_user_todos_dir(user_id)
    todo_file = todos_dir / f"{todo_id}.json"
    
    if not todo_file.exists():
        raise HTTPException(status_code=404, detail="Todo not found")
    
    with open(todo_file, "r") as f:
        todo = json.load(f)
    
    # Verify ownership
    if todo.get("user_id") != user_id:
        raise HTTPException(status_code=403, detail="Forbidden")
    
    return todo

@web_app.put("/todos/{todo_id}")
@app.function(volumes={VOLUME_PATH: volume}, image=image)
async def update_todo(todo_id: str, updates: TodoCreate, user_id: str = Security(get_current_user)):
    """Update an existing todo."""
    todos_dir = get_user_todos_dir(user_id)
    todo_file = todos_dir / f"{todo_id}.json"
    
    if not todo_file.exists():
        raise HTTPException(status_code=404, detail="Todo not found")
    
    with open(todo_file, "r") as f:
        todo = json.load(f)
    
    # Verify ownership
    if todo.get("user_id") != user_id:
        raise HTTPException(status_code=403, detail="Forbidden")
    
    # Update fields
    todo["title"] = updates.title
    todo["description"] = updates.description
    todo["completed"] = updates.completed
    
    with open(todo_file, "w") as f:
        json.dump(todo, f)
    
    volume.commit()
    
    return todo

@web_app.delete("/todos/{todo_id}", status_code=204)
@app.function(volumes={VOLUME_PATH: volume}, image=image)
async def delete_todo(todo_id: str, user_id: str = Security(get_current_user)):
    """Delete a todo."""
    todos_dir = get_user_todos_dir(user_id)
    todo_file = todos_dir / f"{todo_id}.json"
    
    if not todo_file.exists():
        raise HTTPException(status_code=404, detail="Todo not found")
    
    with open(todo_file, "r") as f:
        todo = json.load(f)
    
    # Verify ownership
    if todo.get("user_id") != user_id:
        raise HTTPException(status_code=403, detail="Forbidden")
    
    todo_file.unlink()
    volume.commit()
    
    return None

# === Serve ===

@app.function(image=image, volumes={VOLUME_PATH: volume})
@modal.asgi_app()
def serve():
    return web_app
