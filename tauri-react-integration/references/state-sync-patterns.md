# State Synchronization Patterns

## Overview

Keeping React UI state synchronized with Rust backend state is a core challenge in Tauri applications. This guide covers patterns for different synchronization scenarios.

## Pattern 1: Pessimistic Synchronization

### Use Case
Update backend first, then update UI. Roll back UI on failure.

### When to Use
- Critical operations that must succeed
- Transactions that require consistency
- Financial operations
- Permission changes
- Irreversible actions

### Implementation

#### Rust
```rust
#[tauri::command]
pub async fn transfer_funds(
    from_account: String,
    to_account: String,
    amount: f64,
    app_handle: tauri::AppHandle,
) -> Result<TransferResult, String> {
    // Perform the transfer
    let result = process_transfer(&from_account, &to_account, amount)
        .await
        .map_err(|e| e.to_string())?;

    // Notify all listeners of the state change
    let _ = app_handle.emit_all("transfer_completed", TransferEvent {
        from: from_account,
        to: to_account,
        amount,
        timestamp: chrono::Local::now(),
    });

    Ok(result)
}
```

#### React
```typescript
interface Account {
  id: string;
  balance: number;
}

export function TransferFunds() {
  const [accounts, setAccounts] = useState<Account[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);

  const handleTransfer = async (
    fromId: string,
    toId: string,
    amount: number
  ) => {
    setLoading(true);
    setError(null);

    try {
      // Perform transfer on backend first
      await invoke('transfer_funds', {
        from_account: fromId,
        to_account: toId,
        amount,
      });

      // Update UI only after backend confirms
      setAccounts((prev) =>
        prev.map((acc) => {
          if (acc.id === fromId) {
            return { ...acc, balance: acc.balance - amount };
          }
          if (acc.id === toId) {
            return { ...acc, balance: acc.balance + amount };
          }
          return acc;
        })
      );
    } catch (err) {
      // Backend operation failed, don't update UI
      setError(err instanceof Error ? err.message : String(err));
    } finally {
      setLoading(false);
    }
  };

  return (
    <div>
      {error && <div className="error">{error}</div>}
      {/* Transfer UI */}
    </div>
  );
}
```

---

## Pattern 2: Optimistic Synchronization

### Use Case
Update UI immediately, sync with backend asynchronously. Rollback on failure.

### When to Use
- Non-critical updates
- UI responsiveness is important
- Fast feedback for user actions
- Reversible operations
- Network latency tolerance

### Implementation

#### React
```typescript
interface TodoItem {
  id: string;
  title: string;
  completed: boolean;
  synced: boolean; // Track sync status
}

export function TodoList() {
  const [todos, setTodos] = useState<TodoItem[]>([]);

  const toggleTodo = async (id: string) => {
    // Optimistic update
    setTodos((prev) =>
      prev.map((todo) =>
        todo.id === id
          ? { ...todo, completed: !todo.completed, synced: false }
          : todo
      )
    );

    // Sync with backend
    try {
      await invoke('toggle_todo', { id });

      // Mark as synced
      setTodos((prev) =>
        prev.map((todo) =>
          todo.id === id ? { ...todo, synced: true } : todo
        )
      );
    } catch (err) {
      // Rollback on failure
      setTodos((prev) =>
        prev.map((todo) =>
          todo.id === id
            ? { ...todo, completed: !todo.completed, synced: false }
            : todo
        )
      );

      console.error('Failed to update todo:', err);
    }
  };

  const deleteTodo = async (id: string) => {
    const originalTodos = todos;

    // Optimistic removal
    setTodos((prev) => prev.filter((todo) => todo.id !== id));

    // Sync with backend
    try {
      await invoke('delete_todo', { id });
    } catch (err) {
      // Restore on failure
      setTodos(originalTodos);
      console.error('Failed to delete todo:', err);
    }
  };

  return (
    <ul>
      {todos.map((todo) => (
        <li key={todo.id} className={!todo.synced ? 'pending-sync' : ''}>
          <input
            type="checkbox"
            checked={todo.completed}
            onChange={() => toggleTodo(todo.id)}
            disabled={!todo.synced}
          />
          <span>{todo.title}</span>
          {!todo.synced && <span className="sync-indicator">syncing...</span>}
          <button onClick={() => deleteTodo(todo.id)}>Delete</button>
        </li>
      ))}
    </ul>
  );
}
```

---

## Pattern 3: Event-Driven Synchronization

### Use Case
Backend emits events when state changes. Frontend listens and updates accordingly.

### When to Use
- Multi-window applications
- Collaborative features
- Real-time updates
- Shared state across instances
- Background task notifications

### Implementation

#### Rust
```rust
use tauri::{Manager, State};
use tokio::sync::RwLock;
use std::sync::Arc;

pub struct ApplicationState {
    pub user_settings: UserSettings,
    pub cache: HashMap<String, CachedData>,
}

#[tauri::command]
pub async fn update_user_settings(
    settings: UserSettings,
    app_handle: tauri::AppHandle,
    state: State<'_, Arc<RwLock<ApplicationState>>>,
) -> Result<(), String> {
    // Update state
    let mut app_state = state.write().await;
    app_state.user_settings = settings.clone();
    drop(app_state);

    // Broadcast to all windows
    let _ = app_handle.emit_all("user_settings_updated", settings);

    Ok(())
}

#[tauri::command]
pub async fn invalidate_cache(
    key: String,
    app_handle: tauri::AppHandle,
    state: State<'_, Arc<RwLock<ApplicationState>>>,
) -> Result<(), String> {
    // Update state
    let mut app_state = state.write().await;
    app_state.cache.remove(&key);
    drop(app_state);

    // Notify all listeners
    let _ = app_handle.emit_all("cache_invalidated", key);

    Ok(())
}
```

#### React
```typescript
interface UserSettings {
  theme: 'light' | 'dark';
  fontSize: number;
  autoSave: boolean;
}

export function SettingsSync() {
  const [settings, setSettings] = useState<UserSettings | null>(null);

  useEffect(() => {
    // Load initial settings
    invoke<UserSettings>('get_user_settings').then(setSettings);

    // Listen for settings updates from backend
    const unlistenSettings = listen<UserSettings>(
      'user_settings_updated',
      (event) => {
        setSettings(event.payload);
      }
    );

    // Listen for cache invalidation
    const unlistenCache = listen<string>('cache_invalidated', (event) => {
      const cacheKey = event.payload;
      invalidateCache(cacheKey);
    });

    return () => {
      unlistenSettings.then((f) => f());
      unlistenCache.then((f) => f());
    };
  }, []);

  const handleSettingsChange = async (newSettings: UserSettings) => {
    setSettings(newSettings);
    try {
      await invoke('update_user_settings', newSettings);
    } catch (err) {
      console.error('Failed to update settings:', err);
    }
  };

  return (
    <div>
      <label>
        Theme:
        <select
          value={settings?.theme || 'light'}
          onChange={(e) =>
            handleSettingsChange({
              ...settings!,
              theme: e.target.value as 'light' | 'dark',
            })
          }
        >
          <option>light</option>
          <option>dark</option>
        </select>
      </label>
    </div>
  );
}
```

---

## Pattern 4: Bidirectional Binding with Debouncing

### Use Case
Frequent updates that should be synchronized but throttled.

### When to Use
- Form inputs (search, filters)
- Slider values
- Textarea content
- Real-time collaboration
- Analytics tracking

### Implementation

```typescript
export function useDebounce<T>(value: T, delayMs: number = 500) {
  const [debouncedValue, setDebouncedValue] = useState(value);

  useEffect(() => {
    const handler = setTimeout(() => {
      setDebouncedValue(value);
    }, delayMs);

    return () => clearTimeout(handler);
  }, [value, delayMs]);

  return debouncedValue;
}

export function SearchForm() {
  const [query, setQuery] = useState('');
  const [results, setResults] = useState<SearchResult[]>([]);
  const [loading, setLoading] = useState(false);

  const debouncedQuery = useDebounce(query, 300);

  useEffect(() => {
    if (!debouncedQuery) {
      setResults([]);
      return;
    }

    setLoading(true);
    invoke<SearchResult[]>('search', { query: debouncedQuery })
      .then(setResults)
      .catch(console.error)
      .finally(() => setLoading(false));
  }, [debouncedQuery]);

  return (
    <div>
      <input
        value={query}
        onChange={(e) => setQuery(e.target.value)}
        placeholder="Search..."
      />
      {loading && <p>Searching...</p>}
      <ul>
        {results.map((result) => (
          <li key={result.id}>{result.title}</li>
        ))}
      </ul>
    </div>
  );
}
```

---

## Pattern 5: Eventual Consistency

### Use Case
Accept temporary inconsistency; resolve over time.

### When to Use
- Distributed systems
- Offline-first applications
- High-latency scenarios
- Large-scale collaborative apps

### Implementation

```typescript
interface SyncQueue {
  id: string;
  action: 'create' | 'update' | 'delete';
  resource: string;
  data: unknown;
  timestamp: number;
  synced: boolean;
}

export function useSyncQueue() {
  const [queue, setQueue] = useState<SyncQueue[]>([]);

  const enqueue = (
    action: SyncQueue['action'],
    resource: string,
    data: unknown
  ) => {
    const item: SyncQueue = {
      id: `${Date.now()}-${Math.random()}`,
      action,
      resource,
      data,
      timestamp: Date.now(),
      synced: false,
    };

    setQueue((prev) => [...prev, item]);
  };

  const processSyncQueue = async () => {
    const unsyncedItems = queue.filter((item) => !item.synced);

    for (const item of unsyncedItems) {
      try {
        await invoke('sync_operation', {
          action: item.action,
          resource: item.resource,
          data: item.data,
        });

        // Mark as synced
        setQueue((prev) =>
          prev.map((q) =>
            q.id === item.id ? { ...q, synced: true } : q
          )
        );
      } catch (err) {
        console.error(`Failed to sync ${item.resource}:`, err);
        // Retry will happen on next processSyncQueue call
        break;
      }
    }
  };

  // Try to sync periodically
  useEffect(() => {
    const interval = setInterval(processSyncQueue, 5000);
    return () => clearInterval(interval);
  }, [queue]);

  return { queue, enqueue, processSyncQueue };
}
```

---

## Pattern 6: Cache Invalidation

### Use Case
Manage stale data when backend state changes.

### Implementation

```typescript
export class DataCache<T> {
  private data: Map<string, CacheEntry<T>> = new Map();
  private ttlMs: number;

  constructor(ttlMs: number = 60000) {
    this.ttlMs = ttlMs;
  }

  set(key: string, value: T) {
    this.data.set(key, {
      value,
      timestamp: Date.now(),
    });
  }

  get(key: string): T | null {
    const entry = this.data.get(key);

    if (!entry) return null;

    // Check if expired
    if (Date.now() - entry.timestamp > this.ttlMs) {
      this.data.delete(key);
      return null;
    }

    return entry.value;
  }

  invalidate(key: string) {
    this.data.delete(key);
  }

  invalidateAll() {
    this.data.clear();
  }

  has(key: string): boolean {
    return this.get(key) !== null;
  }
}

interface CacheEntry<T> {
  value: T;
  timestamp: number;
}

export function useCachedQuery<T>(
  command: string,
  params: Record<string, unknown>,
  ttlMs: number = 60000
) {
  const cacheRef = useRef(new DataCache<T>(ttlMs));
  const [data, setData] = useState<T | null>(null);
  const [loading, setLoading] = useState(false);
  const cacheKey = JSON.stringify(params);

  useEffect(() => {
    // Check cache first
    const cached = cacheRef.current.get(cacheKey);
    if (cached) {
      setData(cached);
      return;
    }

    // Fetch from backend
    setLoading(true);
    invoke<T>(command, params)
      .then((result) => {
        cacheRef.current.set(cacheKey, result);
        setData(result);
      })
      .catch(console.error)
      .finally(() => setLoading(false));

    // Listen for invalidation events
    const unlistenInvalidate = listen('cache_invalidated', (event) => {
      const invalidatedKey = event.payload;
      if (invalidatedKey === cacheKey) {
        cacheRef.current.invalidate(cacheKey);
        setData(null);
      }
    });

    return () => {
      unlistenInvalidate.then((f) => f());
    };
  }, [command, cacheKey]);

  return { data, loading };
}
```

---

## Comparison Table

| Pattern | Consistency | Responsiveness | Use Case |
|---------|-------------|-----------------|----------|
| Pessimistic | Strong | Slower | Critical operations |
| Optimistic | Eventual | Faster | Non-critical updates |
| Event-Driven | Strong | Real-time | Shared state |
| Debounced | Strong | Balanced | Frequent updates |
| Eventually Consistent | Weak | Fastest | Offline-first |
| Cache-Invalidation | Strong | Variable | Data freshness |

---

## Best Practices

1. **Choose Pattern Based on Requirements**
   - Critical operations: Pessimistic
   - UI responsiveness: Optimistic
   - Shared state: Event-driven

2. **Always Handle Failures**
   - Implement rollback/retry logic
   - Notify users of sync status

3. **Use Unique IDs for Items**
   - Enables proper tracking and updates
   - Prevents state corruption

4. **Implement Sync Status Tracking**
   - Show users what's synced/pending
   - Disable actions on unsync items if needed

5. **Test Sync Scenarios**
   - Network failures
   - Slow connections
   - Concurrent updates
   - Backend changes

6. **Monitor Sync Performance**
   - Track sync times
   - Monitor queue sizes
   - Alert on persistent failures

7. **Document Sync Behavior**
   - Explain to users what happens in different scenarios
   - Document retry policies
   - Explain offline behavior
