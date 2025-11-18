# Polling Scheduler Pattern on Modal

Use Modal's cron scheduling to build polling-based schedulers that check for due work and execute it. This pattern is ideal for deferred task execution, scheduled jobs, and background processing.

## Core Concept

Instead of complex job queues or schedulers, use a simple pattern:
1. **Store work** in volume as files (JSON, etc.)
2. **Cron function** polls every minute to check for due work
3. **Execute work** when it's time
4. **Clean up** after completion

This leverages Modal's built-in cron functionality instead of external dependencies like Celery or APScheduler.

## Basic Polling Pattern

```python
import modal
from datetime import datetime, timezone
from pathlib import Path
import json

app = modal.App("scheduler")
volume = modal.Volume.from_name("scheduler-data", create_if_missing=True)
VOLUME_PATH = "/data"

@app.function(
    volumes={VOLUME_PATH: volume},
    schedule=modal.Cron("* * * * *")  # Every minute
)
def check_for_due_work():
    """Poll for work that's due and execute it."""
    now = datetime.now(timezone.utc)
    work_dir = Path(VOLUME_PATH) / "pending"
    
    if not work_dir.exists():
        return
    
    for work_file in work_dir.glob("*.json"):
        with open(work_file, "r") as f:
            work = json.load(f)
        
        # Check if due
        due_at = datetime.fromisoformat(work["due_at"])
        if due_at <= now:
            # Execute work
            execute_work(work)
            
            # Remove from pending
            work_file.unlink()
            volume.commit()
```

## Scheduled Task Pattern

Store tasks with execution time and poll to execute when due:

```python
from pydantic import BaseModel
from datetime import datetime, timezone
import uuid

class ScheduledTask(BaseModel):
    id: str
    execute_at: datetime
    task_type: str
    params: dict
    created_at: datetime

def schedule_task(task_type: str, execute_at: datetime, params: dict) -> str:
    """Schedule a task for later execution."""
    task = ScheduledTask(
        id=str(uuid.uuid4()),
        execute_at=execute_at,
        task_type=task_type,
        params=params,
        created_at=datetime.now(timezone.utc)
    )
    
    # Save to volume
    task_dir = Path(VOLUME_PATH) / "tasks"
    task_dir.mkdir(parents=True, exist_ok=True)
    
    task_file = task_dir / f"{task.id}.json"
    with open(task_file, "w") as f:
        json.dump(task.model_dump(mode='json'), f)
    
    volume.commit()
    return task.id

@app.function(
    volumes={VOLUME_PATH: volume},
    schedule=modal.Cron("* * * * *")
)
def execute_due_tasks():
    """Check every minute for tasks that are due."""
    now = datetime.now(timezone.utc)
    task_dir = Path(VOLUME_PATH) / "tasks"
    
    if not task_dir.exists():
        return
    
    for task_file in task_dir.glob("*.json"):
        with open(task_file, "r") as f:
            task_data = json.load(f)
        
        task = ScheduledTask(**task_data)
        
        # Check if due (with timezone awareness)
        execute_at = task.execute_at.replace(tzinfo=timezone.utc) if task.execute_at.tzinfo is None else task.execute_at
        
        if execute_at <= now:
            print(f"Executing task {task.id}: {task.task_type}")
            
            # Execute based on task type
            if task.task_type == "send_email":
                send_email(task.params)
            elif task.task_type == "process_data":
                process_data(task.params)
            elif task.task_type == "cleanup":
                cleanup_resources(task.params)
            
            # Remove completed task
            task_file.unlink()
            volume.commit()
```

## Recurring Tasks with Cron Expressions

For recurring tasks, update "last_run" instead of deleting:

```python
from croniter import croniter

class RecurringTask(BaseModel):
    id: str
    cron: str  # "0 9 * * *" (daily at 9am)
    task_type: str
    params: dict
    last_run: Optional[datetime] = None

def create_recurring_task(cron: str, task_type: str, params: dict) -> str:
    """Create a recurring task with cron schedule."""
    task = RecurringTask(
        id=str(uuid.uuid4()),
        cron=cron,
        task_type=task_type,
        params=params,
        last_run=None
    )
    
    # Validate cron
    if not croniter.is_valid(cron):
        raise ValueError(f"Invalid cron expression: {cron}")
    
    # Save to volume
    task_dir = Path(VOLUME_PATH) / "recurring"
    task_dir.mkdir(parents=True, exist_ok=True)
    
    with open(task_dir / f"{task.id}.json", "w") as f:
        json.dump(task.model_dump(mode='json'), f)
    
    volume.commit()
    return task.id

@app.function(
    volumes={VOLUME_PATH: volume},
    schedule=modal.Cron("* * * * *")
)
def execute_recurring_tasks():
    """Check every minute for recurring tasks that should run."""
    now = datetime.now(timezone.utc)
    task_dir = Path(VOLUME_PATH) / "recurring"
    
    if not task_dir.exists():
        return
    
    for task_file in task_dir.glob("*.json"):
        with open(task_file, "r") as f:
            task_data = json.load(f)
        
        task = RecurringTask(**task_data)
        
        # Calculate next run time
        cron = croniter(task.cron, task.last_run or now)
        next_run = cron.get_next(datetime)
        
        # Check if it's time to run (within this minute)
        if next_run <= now:
            print(f"Executing recurring task {task.id}: {task.task_type}")
            
            # Execute task
            execute_task(task.task_type, task.params)
            
            # Update last_run
            task.last_run = now
            with open(task_file, "w") as f:
                json.dump(task.model_dump(mode='json'), f)
            
            volume.commit()
```

## Time-Bucketed Polling (Performance Optimization)

For many scheduled tasks, organize by time buckets to avoid scanning all files:

```python
def schedule_task_bucketed(execute_at: datetime, task_data: dict) -> str:
    """Schedule task in time-bucketed directory."""
    task_id = str(uuid.uuid4())
    
    # Organize by date and hour: /data/tasks/2025-11-18/15/task_abc.json
    date_str = execute_at.strftime("%Y-%m-%d")
    hour_str = str(execute_at.hour)
    
    task_dir = Path(VOLUME_PATH) / "tasks" / date_str / hour_str
    task_dir.mkdir(parents=True, exist_ok=True)
    
    task = {
        "id": task_id,
        "execute_at": execute_at.isoformat(),
        "data": task_data
    }
    
    with open(task_dir / f"{task_id}.json", "w") as f:
        json.dump(task, f)
    
    volume.commit()
    return task_id

@app.function(
    volumes={VOLUME_PATH: volume},
    schedule=modal.Cron("* * * * *")
)
def execute_bucketed_tasks():
    """Only check current hour's bucket - O(tasks this hour) instead of O(all tasks)."""
    now = datetime.now(timezone.utc)
    date_str = now.strftime("%Y-%m-%d")
    hour_str = str(now.hour)
    
    task_dir = Path(VOLUME_PATH) / "tasks" / date_str / hour_str
    
    if not task_dir.exists():
        return
    
    for task_file in task_dir.glob("*.json"):
        with open(task_file, "r") as f:
            task = json.load(f)
        
        execute_at = datetime.fromisoformat(task["execute_at"])
        
        if execute_at <= now:
            # Execute
            execute_task(task["data"])
            
            # Delete
            task_file.unlink()
            volume.commit()
    
    # Clean up empty directory
    if not any(task_dir.iterdir()):
        task_dir.rmdir()
        volume.commit()
```

**Performance:**
- Only scans current hour's bucket
- O(tasks this hour) instead of O(all tasks)
- Automatic cleanup of old directories

## Race Condition Handling

Multiple cron instances may spawn simultaneously. Handle duplicates:

### Delete-Before-Execute Pattern

```python
@app.function(
    volumes={VOLUME_PATH: volume},
    schedule=modal.Cron("* * * * *")
)
def execute_tasks_safe():
    """Delete task file BEFORE execution to prevent duplicates."""
    now = datetime.now(timezone.utc)
    task_dir = Path(VOLUME_PATH) / "tasks"
    
    for task_file in task_dir.glob("*.json"):
        with open(task_file, "r") as f:
            task = json.load(f)
        
        execute_at = datetime.fromisoformat(task["execute_at"])
        
        if execute_at <= now:
            # DELETE IMMEDIATELY - filesystem becomes source of truth
            try:
                task_file.unlink()
                volume.commit()
                print(f"Locked task {task['id']} for execution")
            except FileNotFoundError:
                # Another instance already grabbed it
                print(f"Task {task['id']} already claimed")
                continue
            
            # Now safe to execute (only one instance has it)
            try:
                execute_task(task)
                print(f"Task {task['id']} completed")
            except Exception as e:
                print(f"Task {task['id']} failed: {e}")
                # Task is already deleted, error is logged
```

**Why this works:**
- File deletion is atomic
- Only one instance successfully deletes
- Others get FileNotFoundError and skip
- Filesystem acts as distributed lock

### Mark-As-Executed Pattern

For recurring tasks where you update instead of delete:

```python
@app.function(
    volumes={VOLUME_PATH: volume},
    schedule=modal.Cron("* * * * *")
)
def execute_recurring_safe():
    """Update last_run BEFORE execution to prevent duplicates."""
    now = datetime.now(timezone.utc)
    task_dir = Path(VOLUME_PATH) / "recurring"
    
    for task_file in task_dir.glob("*.json"):
        with open(task_file, "r") as f:
            task = json.load(f)
        
        # Check if due
        last_run = datetime.fromisoformat(task["last_run"]) if task.get("last_run") else None
        cron = croniter(task["cron"], last_run or now)
        next_run = cron.get_next(datetime)
        
        if next_run <= now:
            # UPDATE IMMEDIATELY before execution
            task["last_run"] = now.isoformat()
            with open(task_file, "w") as f:
                json.dump(task, f)
            volume.commit()
            
            # Now safe to execute (last_run prevents other instances)
            execute_task(task)
```

## Execution Results Tracking

Save execution results for auditing:

```python
def save_execution_result(task_id: str, status: str, result: dict = None, error: str = None):
    """Save execution result for tracking."""
    result_dir = Path(VOLUME_PATH) / "results"
    result_dir.mkdir(parents=True, exist_ok=True)
    
    result_data = {
        "task_id": task_id,
        "status": status,  # "success" or "failed"
        "executed_at": datetime.now(timezone.utc).isoformat(),
        "result": result,
        "error": error
    }
    
    with open(result_dir / f"{task_id}.json", "w") as f:
        json.dump(result_data, f)
    
    volume.commit()

@app.function(
    volumes={VOLUME_PATH: volume},
    schedule=modal.Cron("* * * * *")
)
def execute_tasks_with_tracking():
    """Execute tasks and save results."""
    for task_file in get_due_tasks():
        task_id = task_file.stem
        
        try:
            # Execute
            result = execute_task(task_file)
            
            # Save success result
            save_execution_result(task_id, "success", result=result)
            
        except Exception as e:
            # Save failure result
            save_execution_result(task_id, "failed", error=str(e))
        
        finally:
            # Clean up task
            task_file.unlink()
            volume.commit()
```

## Common Cron Schedules

```python
# Every minute
schedule=modal.Cron("* * * * *")

# Every 5 minutes
schedule=modal.Cron("*/5 * * * *")

# Every hour
schedule=modal.Cron("0 * * * *")

# Daily at 9am UTC
schedule=modal.Cron("0 9 * * *")

# Weekdays at 10am UTC
schedule=modal.Cron("0 10 * * 1-5")

# First day of month at midnight
schedule=modal.Cron("0 0 1 * *")
```

Reference: https://crontab.guru

## Best Practices

**Idempotency:**
- Design tasks to be safely re-executed
- Use delete-before-execute for one-time tasks
- Update last_run before executing recurring tasks

**Error Handling:**
- Always wrap execution in try/except
- Log errors for debugging
- Save failed execution results
- Don't retry infinitely (delete or update after N failures)

**Performance:**
- Use time-bucketed directories for many tasks
- Only scan relevant directories (current hour)
- Batch commits when possible
- Clean up empty directories

**Timezone Handling:**
- Always use timezone-aware datetimes
- Store everything in UTC
- Convert to UTC when receiving user input

**Testing:**
- Test cron functions locally with `modal serve`
- Manually trigger: `modal run app.py::check_for_due_work`
- Create test tasks with past times for immediate execution

## Example: Complete Scheduler

See `examples/scheduled_tasks.py` for a complete working implementation combining all these patterns.
