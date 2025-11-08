# Tauri + React IPC Patterns

## Overview

Inter-Process Communication (IPC) in Tauri enables seamless communication between the Rust backend and React frontend. This document covers the primary patterns for different communication scenarios.

## Pattern 1: Request-Response Commands

### Use Case
One-off operations where React waits for a Rust function to complete and return a result.

### When to Use
- File operations (read, write, delete)
- Computational tasks
- Database queries
- API calls from backend
- State queries

### Implementation

#### Rust Side (src/commands/mod.rs)
```rust
use tauri::State;
use std::sync::Arc;

#[tauri::command]
pub async fn read_file(path: String) -> Result<String, String> {
    tokio::fs::read_to_string(&path)
        .await
        .map_err(|e| e.to_string())
}

#[tauri::command]
pub async fn calculate_sum(numbers: Vec<f64>) -> f64 {
    numbers.iter().sum()
}

#[tauri::command]
pub async fn query_database(id: i32) -> Result<UserData, String> {
    db::fetch_user(id)
        .await
        .map_err(|e| e.to_string())
}
```

#### React Component (src/components/FileReader.tsx)
```typescript
import { invoke } from '@tauri-apps/api/core';
import { useState, useEffect } from 'react';

export function FileReader({ filePath }: { filePath: string }) {
  const [content, setContent] = useState<string | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [loading, setLoading] = useState(false);

  const readFile = async () => {
    setLoading(true);
    setError(null);
    try {
      const result = await invoke<string>('read_file', { path: filePath });
      setContent(result);
    } catch (err) {
      setError(err instanceof Error ? err.message : String(err));
    } finally {
      setLoading(false);
    }
  };

  return (
    <div>
      <button onClick={readFile} disabled={loading}>
        {loading ? 'Reading...' : 'Read File'}
      </button>
      {error && <div className="error">{error}</div>}
      {content && <pre>{content}</pre>}
    </div>
  );
}
```

### Custom Hook
```typescript
export function useCommand<P, R>(
  command: string,
  shouldFetch: boolean = true
) {
  const [data, setData] = useState<R | null>(null);
  const [error, setError] = useState<string | null>(null);
  const [loading, setLoading] = useState(false);

  const execute = async (payload?: P) => {
    setLoading(true);
    setError(null);
    try {
      const result = await invoke<R>(command, payload);
      setData(result);
      return result;
    } catch (err) {
      const message = err instanceof Error ? err.message : String(err);
      setError(message);
      throw err;
    } finally {
      setLoading(false);
    }
  };

  useEffect(() => {
    if (shouldFetch) {
      execute();
    }
  }, [command, shouldFetch]);

  return { data, error, loading, execute };
}

// Usage
function MyComponent() {
  const { data, loading, execute } = useCommand<{ id: number }, User>(
    'fetch_user',
    false
  );

  return (
    <button onClick={() => execute({ id: 123 })}>
      {loading ? 'Loading...' : 'Fetch User'}
    </button>
  );
}
```

---

## Pattern 2: Event Broadcasting

### Use Case
Backend sends real-time updates to frontend. Multiple components can listen to the same event.

### When to Use
- Progress updates (downloads, uploads, processing)
- Status changes (connected/disconnected, file saved)
- Background task notifications
- Real-time data updates
- System events (file system changes, hardware changes)

### Implementation

#### Rust Side (src/main.rs)
```rust
use tauri::Manager;

fn main() {
  tauri::Builder::default()
    .setup(|app| {
      let app_handle = app.app_handle().clone();

      // Spawn background task
      std::thread::spawn(move || {
        for i in 0..100 {
          std::thread::sleep(std::time::Duration::from_millis(100));
          let _ = app_handle.emit_all("progress_update", ProgressEvent {
            current: i,
            total: 100,
            percentage: (i as f64 / 100.0) * 100.0,
          });
        }
      });

      Ok(())
    })
    .run(tauri::generate_context!())
    .expect("error while running tauri application");
}

#[derive(serde::Serialize)]
pub struct ProgressEvent {
  pub current: i32,
  pub total: i32,
  pub percentage: f64,
}
```

#### Rust Command with Events
```rust
#[tauri::command]
pub async fn process_file(
  path: String,
  app_handle: tauri::AppHandle,
) -> Result<ProcessResult, String> {
  let mut processed = 0;
  let total_items = 1000;

  for item in get_items(&path)? {
    // Process item
    processed += 1;

    // Emit progress
    let _ = app_handle.emit_all("file_processing", ProgressPayload {
      current: processed,
      total: total_items,
      item_name: item.name,
    });
  }

  Ok(ProcessResult { success: true })
}
```

#### React Component
```typescript
import { listen, UnlistenFn } from '@tauri-apps/api/event';
import { useState, useEffect } from 'react';

interface ProgressPayload {
  current: number;
  total: number;
  item_name: string;
}

export function ProgressMonitor() {
  const [progress, setProgress] = useState(0);
  const [currentItem, setCurrentItem] = useState<string>('');

  useEffect(() => {
    let unlistenProgress: UnlistenFn | null = null;

    const setupListener = async () => {
      unlistenProgress = await listen<ProgressPayload>(
        'file_processing',
        (event) => {
          const { current, total, item_name } = event.payload;
          setProgress((current / total) * 100);
          setCurrentItem(item_name);
        }
      );
    };

    setupListener();

    // Cleanup listener on unmount
    return () => {
      if (unlistenProgress) {
        unlistenProgress();
      }
    };
  }, []);

  return (
    <div>
      <div className="progress-bar">
        <div className="progress" style={{ width: `${progress}%` }} />
      </div>
      <p>Processing: {currentItem}</p>
      <p>Progress: {Math.round(progress)}%</p>
    </div>
  );
}
```

### Custom Hook for Events
```typescript
export function useEvent<T>(eventName: string) {
  const [data, setData] = useState<T | null>(null);
  const [isListening, setIsListening] = useState(false);

  useEffect(() => {
    let unlistenFn: UnlistenFn | null = null;

    const setupListener = async () => {
      unlistenFn = await listen<T>(eventName, (event) => {
        setData(event.payload);
      });
      setIsListening(true);
    };

    setupListener().catch(console.error);

    return () => {
      if (unlistenFn) {
        unlistenFn();
        setIsListening(false);
      }
    };
  }, [eventName]);

  return { data, isListening };
}

// Usage
function MyComponent() {
  const { data: progress } = useEvent<ProgressPayload>('progress_update');
  return <div>Progress: {progress?.percentage}%</div>;
}
```

---

## Pattern 3: Command with Event Streaming

### Use Case
React initiates a command that returns immediately, but backend streams updates via events.

### When to Use
- Long-running operations (data processing, downloads)
- Background tasks that need progress reporting
- Operations with multiple phases
- Tasks that can be cancelled

### Implementation

#### Rust Side
```rust
use tauri::{Manager, State};
use tokio::sync::Mutex;
use std::sync::Arc;

pub struct OperationState {
  pub is_running: bool,
  pub current_step: u32,
}

#[tauri::command]
pub async fn start_background_task(
  app_handle: tauri::AppHandle,
  state: State<'_, Arc<Mutex<OperationState>>>,
) -> Result<String, String> {
  let state_clone = state.inner().clone();

  tokio::spawn(async move {
    let mut op_state = state_clone.lock().await;
    op_state.is_running = true;
    drop(op_state);

    for step in 1..=10 {
      tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

      let _ = app_handle.emit_all("task_progress", TaskProgress {
        step,
        total: 10,
        message: format!("Executing step {}", step),
      });

      let mut op_state = state_clone.lock().await;
      op_state.current_step = step;
    }

    let _ = app_handle.emit_all("task_completed", ());
    let mut op_state = state_clone.lock().await;
    op_state.is_running = false;
  });

  Ok("Task started".to_string())
}

#[tauri::command]
pub async fn cancel_background_task(
  state: State<'_, Arc<Mutex<OperationState>>>,
) -> Result<(), String> {
  let mut op_state = state.lock().await;
  op_state.is_running = false;
  Ok(())
}
```

#### React Component
```typescript
import { invoke } from '@tauri-apps/api/core';
import { listen } from '@tauri-apps/api/event';
import { useState, useEffect } from 'react';

interface TaskProgress {
  step: number;
  total: number;
  message: string;
}

export function BackgroundTaskRunner() {
  const [isRunning, setIsRunning] = useState(false);
  const [progress, setProgress] = useState<TaskProgress | null>(null);

  const startTask = async () => {
    setIsRunning(true);
    setProgress(null);

    // Setup listeners before starting
    const unlistenProgress = await listen<TaskProgress>(
      'task_progress',
      (event) => {
        setProgress(event.payload);
      }
    );

    const unlistenComplete = await listen(
      'task_completed',
      () => {
        setIsRunning(false);
        unlistenProgress();
        unlistenComplete();
      }
    );

    try {
      await invoke('start_background_task');
    } catch (error) {
      console.error('Failed to start task:', error);
      setIsRunning(false);
      unlistenProgress();
      unlistenComplete();
    }
  };

  const cancelTask = async () => {
    try {
      await invoke('cancel_background_task');
      setIsRunning(false);
    } catch (error) {
      console.error('Failed to cancel task:', error);
    }
  };

  return (
    <div>
      <button onClick={startTask} disabled={isRunning}>
        Start Task
      </button>
      {isRunning && (
        <button onClick={cancelTask}>Cancel</button>
      )}
      {progress && (
        <div>
          <p>{progress.message}</p>
          <progress
            value={progress.step}
            max={progress.total}
          />
          <p>
            {progress.step} / {progress.total}
          </p>
        </div>
      )}
    </div>
  );
}
```

---

## Pattern 4: Two-Way Binding

### Use Case
Keep a data structure synchronized between Rust and React.

### Implementation

#### Rust Side
```rust
use tauri::{Manager, State};
use tokio::sync::RwLock;
use std::sync::Arc;

pub struct AppData {
  pub counter: i32,
  pub user_data: UserData,
}

#[tauri::command]
pub async fn get_app_data(
  state: State<'_, Arc<RwLock<AppData>>>,
) -> Result<AppData, String> {
  let data = state.read().await;
  Ok(AppData {
    counter: data.counter,
    user_data: data.user_data.clone(),
  })
}

#[tauri::command]
pub async fn update_counter(
  increment: i32,
  app_handle: tauri::AppHandle,
  state: State<'_, Arc<RwLock<AppData>>>,
) -> Result<i32, String> {
  let mut data = state.write().await;
  data.counter += increment;
  let new_value = data.counter;
  drop(data);

  // Notify all clients
  let _ = app_handle.emit_all("counter_changed", new_value);

  Ok(new_value)
}
```

#### React Component
```typescript
import { invoke } from '@tauri-apps/api/core';
import { listen } from '@tauri-apps/api/event';
import { useState, useEffect } from 'react';

export function CounterSync() {
  const [counter, setCounter] = useState(0);

  useEffect(() => {
    // Load initial value
    invoke<number>('get_app_data').then((data) => {
      setCounter(data.counter);
    });

    // Listen for updates from other windows/instances
    const unlistenCounter = listen<number>('counter_changed', (event) => {
      setCounter(event.payload);
    });

    return () => {
      unlistenCounter.then((f) => f());
    };
  }, []);

  const handleIncrement = async () => {
    try {
      const newValue = await invoke<number>('update_counter', {
        increment: 1,
      });
      setCounter(newValue);
    } catch (error) {
      console.error('Failed to update counter:', error);
    }
  };

  return (
    <div>
      <p>Counter: {counter}</p>
      <button onClick={handleIncrement}>Increment</button>
    </div>
  );
}
```

---

## Comparison Table

| Pattern | Direction | Wait for Response | Use Case |
|---------|-----------|-------------------|----------|
| Request-Response | Bidirectional | Yes | One-off operations |
| Events | Backend → Frontend | No | Notifications, progress |
| Command + Streaming | Mixed | Partial | Long operations with progress |
| Two-Way Binding | Bidirectional | Yes + Events | Synchronized state |

---

## Common Mistakes to Avoid

1. **Not Cleaning Up Event Listeners**
   - Always unlisten in useEffect cleanup
   - Memory leaks otherwise

2. **Forgetting Error Handling**
   - Commands can fail; handle errors gracefully
   - Use Result types in Rust

3. **Not Using Types**
   - TypeScript loses safety without types
   - Auto-generate types from Rust

4. **Blocking the Main Thread**
   - Use async/await in Rust
   - Don't block the Tauri window thread

5. **Not Handling Disconnections**
   - Network interruptions happen
   - Implement retry logic

## Performance Tips

1. **Batch Events**: Send 1 event per 100ms instead of per operation
2. **Debounce Updates**: In React, debounce rapid state changes
3. **Use Lazy Queries**: Only fetch data when needed
4. **Cache Results**: Cache responses from read-only commands
5. **Optimize Serialization**: Keep payloads small
