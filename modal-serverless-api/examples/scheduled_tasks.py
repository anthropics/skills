"""
Scheduled Tasks with Polling Pattern on Modal

Demonstrates:
- Creating scheduled tasks via API
- Polling pattern with cron to check for due tasks
- Time-bucketed storage for performance
- Race condition handling (delete-before-execute)
- Execution result tracking

Deploy: modal deploy scheduled_tasks.py
Test: modal serve scheduled_tasks.py
"""

import modal
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from pathlib import Path
from datetime import datetime, timezone
import json
import uuid

# === Modal Setup ===

app = modal.App("scheduled-tasks")

image = modal.Image.debian_slim().pip_install("fastapi")

volume = modal.Volume.from_name("scheduled-tasks-data", create_if_missing=True)
VOLUME_PATH = "/data"

# === FastAPI App ===

web_app = FastAPI(title="Scheduled Tasks API")

# === Models ===

class TaskCreate(BaseModel):
    execute_at: datetime  # ISO 8601 with timezone
    task_type: str
    params: dict

class TaskResponse(BaseModel):
    id: str
    execute_at: str
    task_type: str
    params: dict
    status: str  # "pending" or "completed"

# === Task Execution Functions ===

def execute_task(task_type: str, params: dict):
    """Execute a task based on its type."""
    print(f"Executing {task_type} with params: {params}")
    
    if task_type == "send_email":
        # Simulate sending email
        print(f"Sending email to {params.get('to')}: {params.get('subject')}")
    
    elif task_type == "process_data":
        # Simulate data processing
        print(f"Processing data: {params.get('dataset_id')}")
    
    elif task_type == "cleanup":
        # Simulate cleanup
        print(f"Cleaning up resources: {params.get('resource_ids')}")
    
    else:
        print(f"Unknown task type: {task_type}")

# === Storage Helpers (Time-Bucketed) ===

def get_task_path(task_id: str, execute_at: datetime) -> Path:
    """
    Get task file path with time-bucketing.
    
    Structure: /data/tasks/{date}/{hour}/{task_id}.json
    This allows cron to only scan current hour's bucket.
    """
    date_str = execute_at.strftime("%Y-%m-%d")
    hour_str = str(execute_at.hour)
    
    task_dir = Path(VOLUME_PATH) / "tasks" / date_str / hour_str
    return task_dir / f"{task_id}.json"

def save_task(task_id: str, execute_at: datetime, task_type: str, params: dict):
    """Save task to volume."""
    task_path = get_task_path(task_id, execute_at)
    task_path.parent.mkdir(parents=True, exist_ok=True)
    
    task_data = {
        "id": task_id,
        "execute_at": execute_at.isoformat(),
        "task_type": task_type,
        "params": params,
        "status": "pending"
    }
    
    with open(task_path, "w") as f:
        json.dump(task_data, f)
    
    volume.commit()

def save_result(task_id: str, task_type: str, status: str, error: str = None):
    """Save execution result."""
    result_dir = Path(VOLUME_PATH) / "results"
    result_dir.mkdir(parents=True, exist_ok=True)
    
    result_data = {
        "task_id": task_id,
        "task_type": task_type,
        "status": status,  # "success" or "failed"
        "executed_at": datetime.now(timezone.utc).isoformat(),
        "error": error
    }
    
    with open(result_dir / f"{task_id}.json", "w") as f:
        json.dump(result_data, f)
    
    volume.commit()

# === API Endpoints ===

@web_app.get("/")
def root():
    return {
        "service": "Scheduled Tasks API",
        "endpoints": {
            "/tasks": "Create task (POST)",
            "/tasks": "List pending tasks (GET)",
            "/results": "List execution results (GET)",
        }
    }

@web_app.post("/tasks", status_code=201)
@app.function(volumes={VOLUME_PATH: volume}, image=image)
async def create_task(task: TaskCreate):
    """Create a scheduled task."""
    # Ensure timezone-aware
    execute_at = task.execute_at
    if execute_at.tzinfo is None:
        raise HTTPException(status_code=400, detail="execute_at must have timezone info")
    
    task_id = str(uuid.uuid4())
    save_task(task_id, execute_at, task.task_type, task.params)
    
    return {
        "id": task_id,
        "execute_at": execute_at.isoformat(),
        "task_type": task.task_type,
        "params": task.params,
        "status": "pending"
    }

@web_app.get("/tasks")
@app.function(volumes={VOLUME_PATH: volume}, image=image)
async def list_pending_tasks():
    """List all pending tasks."""
    tasks_base = Path(VOLUME_PATH) / "tasks"
    
    if not tasks_base.exists():
        return []
    
    tasks = []
    for date_dir in tasks_base.iterdir():
        if not date_dir.is_dir():
            continue
        for hour_dir in date_dir.iterdir():
            if not hour_dir.is_dir():
                continue
            for task_file in hour_dir.glob("*.json"):
                with open(task_file, "r") as f:
                    tasks.append(json.load(f))
    
    return tasks

@web_app.get("/results")
@app.function(volumes={VOLUME_PATH: volume}, image=image)
async def list_results():
    """List execution results."""
    results_dir = Path(VOLUME_PATH) / "results"
    
    if not results_dir.exists():
        return []
    
    results = []
    for result_file in results_dir.glob("*.json"):
        with open(result_file, "r") as f:
            results.append(json.load(f))
    
    return results

# === Background Scheduler (Cron) ===

@app.function(
    volumes={VOLUME_PATH: volume},
    image=image,
    schedule=modal.Cron("* * * * *")  # Every minute
)
def check_for_due_tasks():
    """
    Poll for tasks that are due and execute them.
    
    Only checks current hour's bucket for performance:
    O(tasks this hour) instead of O(all tasks)
    """
    now = datetime.now(timezone.utc)
    date_str = now.strftime("%Y-%m-%d")
    hour_str = str(now.hour)
    
    # Only check current hour's bucket
    hour_dir = Path(VOLUME_PATH) / "tasks" / date_str / hour_str
    
    if not hour_dir.exists():
        print(f"No tasks in bucket {date_str}/{hour_str}")
        return
    
    print(f"Checking for due tasks in {date_str}/{hour_str}...")
    
    for task_file in hour_dir.glob("*.json"):
        with open(task_file, "r") as f:
            task = json.load(f)
        
        # Check if due
        execute_at = datetime.fromisoformat(task["execute_at"])
        if execute_at.tzinfo is None:
            execute_at = execute_at.replace(tzinfo=timezone.utc)
        
        if execute_at <= now:
            print(f"Task {task['id']} is due, executing...")
            
            # DELETE IMMEDIATELY to prevent race conditions
            # (Multiple cron instances may spawn simultaneously)
            try:
                task_file.unlink()
                volume.commit()
                print(f"Locked task {task['id']} for execution")
            except FileNotFoundError:
                # Another instance already claimed it
                print(f"Task {task['id']} already claimed by another instance")
                continue
            
            # Now safe to execute (only one instance has it)
            try:
                execute_task(task["task_type"], task["params"])
                save_result(task["id"], task["task_type"], "success")
                print(f"Task {task['id']} completed successfully")
            
            except Exception as e:
                print(f"Task {task['id']} failed: {e}")
                save_result(task["id"], task["task_type"], "failed", error=str(e))
    
    # Clean up empty directories
    if not any(hour_dir.iterdir()):
        hour_dir.rmdir()
        volume.commit()
        print(f"Cleaned up empty bucket {date_str}/{hour_str}")

# === Serve ===

@app.function(image=image, volumes={VOLUME_PATH: volume})
@modal.asgi_app()
def serve():
    return web_app
