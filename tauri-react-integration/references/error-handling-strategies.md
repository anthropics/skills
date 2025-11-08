# Error Handling Strategies in Tauri + React

## Overview

Robust error handling across the Rust backend and React frontend is critical for building reliable applications. This guide covers patterns for error definition, propagation, recovery, and user feedback.

## Error Type Definition

### Rust Error Types

Define custom error types that serialize well:

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct TauriError {
    pub code: String,
    pub message: String,
    pub details: Option<String>,
}

impl From<std::io::Error> for TauriError {
    fn from(err: std::io::Error) -> Self {
        TauriError {
            code: "IO_ERROR".to_string(),
            message: err.to_string(),
            details: None,
        }
    }
}

impl From<tokio::task::JoinError> for TauriError {
    fn from(err: tokio::task::JoinError) -> Self {
        TauriError {
            code: "TASK_ERROR".to_string(),
            message: err.to_string(),
            details: None,
        }
    }
}

// Custom error types for domain logic
impl TauriError {
    pub fn validation_error(field: &str, reason: &str) -> Self {
        TauriError {
            code: "VALIDATION_ERROR".to_string(),
            message: format!("Invalid {}", field),
            details: Some(reason.to_string()),
        }
    }

    pub fn not_found(resource: &str) -> Self {
        TauriError {
            code: "NOT_FOUND".to_string(),
            message: format!("{} not found", resource),
            details: None,
        }
    }

    pub fn permission_denied(action: &str) -> Self {
        TauriError {
            code: "PERMISSION_DENIED".to_string(),
            message: format!("Permission denied: {}", action),
            details: None,
        }
    }
}
```

### TypeScript Error Types

```typescript
export interface TauriError {
  code: string;
  message: string;
  details?: string;
}

export enum ErrorCode {
  VALIDATION_ERROR = 'VALIDATION_ERROR',
  NOT_FOUND = 'NOT_FOUND',
  PERMISSION_DENIED = 'PERMISSION_DENIED',
  IO_ERROR = 'IO_ERROR',
  TASK_ERROR = 'TASK_ERROR',
  NETWORK_ERROR = 'NETWORK_ERROR',
  TIMEOUT = 'TIMEOUT',
  CANCELLED = 'CANCELLED',
}

export class AppError extends Error {
  constructor(
    public code: ErrorCode,
    message: string,
    public details?: string
  ) {
    super(message);
    this.name = 'AppError';
  }

  static from(err: unknown): AppError {
    if (err instanceof AppError) {
      return err;
    }

    if (typeof err === 'string') {
      return new AppError(ErrorCode.VALIDATION_ERROR, err);
    }

    if (err instanceof Error) {
      return new AppError(
        ErrorCode.VALIDATION_ERROR,
        err.message,
        err.stack
      );
    }

    return new AppError(
      ErrorCode.VALIDATION_ERROR,
      'Unknown error occurred'
    );
  }
}
```

---

## Error Propagation Patterns

### Pattern 1: Simple Error Propagation

#### Rust
```rust
#[tauri::command]
pub async fn read_config(path: String) -> Result<Config, String> {
    let content = tokio::fs::read_to_string(&path)
        .await
        .map_err(|e| format!("Failed to read config: {}", e))?;

    let config: Config = serde_json::from_str(&content)
        .map_err(|e| format!("Invalid config format: {}", e))?;

    Ok(config)
}
```

#### React
```typescript
export function useConfig(path: string) {
  const [config, setConfig] = useState<Config | null>(null);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    invoke<Config>('read_config', { path })
      .then(setConfig)
      .catch((err) => {
        const message = typeof err === 'string' ? err : err.message;
        setError(message);
      });
  }, [path]);

  return { config, error };
}
```

### Pattern 2: Structured Error Handling

#### Rust
```rust
#[tauri::command]
pub async fn process_data(
    input: String,
) -> Result<ProcessedData, TauriError> {
    // Validate input
    if input.is_empty() {
        return Err(TauriError::validation_error("input", "cannot be empty"));
    }

    // Check length
    if input.len() > 1000 {
        return Err(TauriError::validation_error(
            "input",
            "must be less than 1000 characters",
        ));
    }

    // Process
    let result = perform_processing(&input).map_err(|e| {
        TauriError {
            code: "PROCESSING_ERROR".to_string(),
            message: "Failed to process data".to_string(),
            details: Some(e.to_string()),
        }
    })?;

    Ok(result)
}
```

#### React
```typescript
export function DataProcessor() {
  const [data, setData] = useState('');
  const [error, setError] = useState<AppError | null>(null);
  const [isLoading, setIsLoading] = useState(false);

  const handleProcess = async () => {
    setIsLoading(true);
    setError(null);

    try {
      const result = await invoke<ProcessedData>('process_data', {
        input: data,
      });
      setData(result);
    } catch (err: unknown) {
      const appError = AppError.from(err);
      setError(appError);

      // Log for debugging
      console.error('Processing failed:', appError);
    } finally {
      setIsLoading(false);
    }
  };

  return (
    <div>
      <input
        value={data}
        onChange={(e) => setData(e.target.value)}
        disabled={isLoading}
      />
      <button onClick={handleProcess} disabled={isLoading}>
        Process
      </button>
      {error && (
        <div className="error">
          <strong>{error.message}</strong>
          {error.details && <p>{error.details}</p>}
        </div>
      )}
    </div>
  );
}
```

---

## Retry Logic

### Exponential Backoff Retry

```typescript
interface RetryOptions {
  maxAttempts?: number;
  initialDelayMs?: number;
  maxDelayMs?: number;
  backoffMultiplier?: number;
}

export async function invokeWithRetry<T>(
  command: string,
  payload?: Record<string, unknown>,
  options: RetryOptions = {}
): Promise<T> {
  const {
    maxAttempts = 3,
    initialDelayMs = 100,
    maxDelayMs = 10000,
    backoffMultiplier = 2,
  } = options;

  let lastError: Error | null = null;

  for (let attempt = 1; attempt <= maxAttempts; attempt++) {
    try {
      return await invoke<T>(command, payload);
    } catch (err) {
      lastError = err instanceof Error ? err : new Error(String(err));

      // Don't retry for validation errors
      if (
        lastError.message.includes('VALIDATION_ERROR') ||
        lastError.message.includes('NOT_FOUND')
      ) {
        throw lastError;
      }

      if (attempt < maxAttempts) {
        const delay = Math.min(
          initialDelayMs * Math.pow(backoffMultiplier, attempt - 1),
          maxDelayMs
        );
        await new Promise((resolve) => setTimeout(resolve, delay));
      }
    }
  }

  throw lastError || new Error('Max retry attempts exceeded');
}

// Usage
async function fetchUserData(userId: number) {
  return invokeWithRetry<UserData>('fetch_user', { id: userId }, {
    maxAttempts: 3,
    initialDelayMs: 200,
  });
}
```

### Retry with Circuit Breaker

```typescript
interface CircuitBreakerState {
  failures: number;
  lastFailureTime: number;
  state: 'CLOSED' | 'OPEN' | 'HALF_OPEN';
}

export class CircuitBreaker {
  private state: CircuitBreakerState = {
    failures: 0,
    lastFailureTime: 0,
    state: 'CLOSED',
  };

  private failureThreshold = 5;
  private resetTimeoutMs = 60000; // 1 minute

  async execute<T>(
    fn: () => Promise<T>
  ): Promise<T> {
    if (this.state.state === 'OPEN') {
      const timeSinceLastFailure =
        Date.now() - this.state.lastFailureTime;

      if (timeSinceLastFailure > this.resetTimeoutMs) {
        this.state.state = 'HALF_OPEN';
      } else {
        throw new Error(
          'Circuit breaker is OPEN. Service temporarily unavailable.'
        );
      }
    }

    try {
      const result = await fn();
      this.onSuccess();
      return result;
    } catch (error) {
      this.onFailure();
      throw error;
    }
  }

  private onSuccess() {
    this.state.failures = 0;
    this.state.state = 'CLOSED';
  }

  private onFailure() {
    this.state.failures++;
    this.state.lastFailureTime = Date.now();

    if (this.state.failures >= this.failureThreshold) {
      this.state.state = 'OPEN';
    }
  }
}

// Usage
const breaker = new CircuitBreaker();

async function safeFetchUser(userId: number) {
  return breaker.execute(() =>
    invoke<UserData>('fetch_user', { id: userId })
  );
}
```

---

## User-Friendly Error Messages

### Error Message Mapping

```typescript
export function getErrorMessage(error: unknown): string {
  if (typeof error === 'string') {
    return error;
  }

  if (error instanceof AppError) {
    switch (error.code) {
      case ErrorCode.VALIDATION_ERROR:
        return `Please check your input: ${error.message}`;
      case ErrorCode.NOT_FOUND:
        return `${error.message}. Please try a different search.`;
      case ErrorCode.PERMISSION_DENIED:
        return `You don't have permission to perform this action.`;
      case ErrorCode.NETWORK_ERROR:
        return 'Network error. Please check your connection and try again.';
      case ErrorCode.TIMEOUT:
        return 'Operation took too long. Please try again.';
      case ErrorCode.CANCELLED:
        return 'Operation was cancelled.';
      default:
        return error.message || 'An unexpected error occurred';
    }
  }

  return 'An unexpected error occurred. Please try again.';
}

// Usage in component
export function ErrorBoundary({ error }: { error: unknown }) {
  const message = getErrorMessage(error);
  return (
    <div className="error-container">
      <p className="error-message">{message}</p>
    </div>
  );
}
```

### Error Notification Component

```typescript
interface ErrorNotification {
  id: string;
  code: string;
  message: string;
  details?: string;
  timestamp: number;
}

export function useErrorNotifications() {
  const [notifications, setNotifications] = useState<ErrorNotification[]>([]);

  const addError = (error: unknown, autoDismiss = true) => {
    const appError = AppError.from(error);
    const id = `${Date.now()}-${Math.random()}`;

    const notification: ErrorNotification = {
      id,
      code: appError.code,
      message: appError.message,
      details: appError.details,
      timestamp: Date.now(),
    };

    setNotifications((prev) => [...prev, notification]);

    if (autoDismiss) {
      setTimeout(() => {
        removeError(id);
      }, 5000);
    }
  };

  const removeError = (id: string) => {
    setNotifications((prev) => prev.filter((n) => n.id !== id));
  };

  return { notifications, addError, removeError };
}

export function ErrorNotificationCenter() {
  const { notifications, removeError } = useErrorNotifications();

  return (
    <div className="notification-center">
      {notifications.map((notif) => (
        <div key={notif.id} className="notification error">
          <h4>{notif.message}</h4>
          {notif.details && <p>{notif.details}</p>}
          <button onClick={() => removeError(notif.id)}>Dismiss</button>
        </div>
      ))}
    </div>
  );
}
```

---

## Timeout Handling

```typescript
interface TimeoutOptions {
  timeoutMs?: number;
  onTimeout?: () => void;
}

export function invokeWithTimeout<T>(
  command: string,
  payload?: Record<string, unknown>,
  options: TimeoutOptions = {}
): Promise<T> {
  const { timeoutMs = 30000, onTimeout } = options;

  return Promise.race([
    invoke<T>(command, payload),
    new Promise<T>((_, reject) =>
      setTimeout(() => {
        onTimeout?.();
        reject(
          new AppError(
            ErrorCode.TIMEOUT,
            `Operation timed out after ${timeoutMs}ms`
          )
        );
      }, timeoutMs)
    ),
  ]);
}

// Usage
async function fetchWithTimeout(userId: number) {
  return invokeWithTimeout<UserData>(
    'fetch_user',
    { id: userId },
    {
      timeoutMs: 10000,
      onTimeout: () => console.warn('Fetch operation timed out'),
    }
  );
}
```

---

## Logging and Debugging

### Error Logging Service

```typescript
interface ErrorLog {
  timestamp: Date;
  code: string;
  message: string;
  details?: string;
  stack?: string;
  context?: Record<string, unknown>;
}

export class ErrorLogger {
  private logs: ErrorLog[] = [];
  private maxLogs = 100;

  log(error: unknown, context?: Record<string, unknown>) {
    const appError = AppError.from(error);

    const log: ErrorLog = {
      timestamp: new Date(),
      code: appError.code,
      message: appError.message,
      details: appError.details,
      stack: appError.stack,
      context,
    };

    this.logs.push(log);

    // Keep only recent logs
    if (this.logs.length > this.maxLogs) {
      this.logs.shift();
    }

    // Log to console in development
    if (process.env.NODE_ENV === 'development') {
      console.error('Error logged:', log);
    }
  }

  getLogs(): ErrorLog[] {
    return [...this.logs];
  }

  exportLogs(): string {
    return JSON.stringify(this.logs, null, 2);
  }

  clearLogs() {
    this.logs = [];
  }
}

export const errorLogger = new ErrorLogger();
```

---

## Testing Error Handling

```typescript
describe('Error Handling', () => {
  it('should handle validation errors', async () => {
    const error = TauriError.validation_error('email', 'invalid format');
    expect(error.code).toBe('VALIDATION_ERROR');
  });

  it('should convert errors to AppError', () => {
    const err = new Error('Test error');
    const appError = AppError.from(err);
    expect(appError).toBeInstanceOf(AppError);
  });

  it('should retry failed operations', async () => {
    let attempts = 0;
    const fn = async () => {
      attempts++;
      if (attempts < 3) throw new Error('Failed');
      return 'success';
    };

    const result = await invokeWithRetry('test_command');
    expect(attempts).toBe(3);
  });
});
```

---

## Best Practices Summary

1. **Define Clear Error Types**: Both Rust and TypeScript
2. **Propagate Structured Errors**: Include code, message, and details
3. **Implement Retry Logic**: For transient failures only
4. **Provide User-Friendly Messages**: Hide technical details
5. **Log Errors**: For debugging and monitoring
6. **Handle Timeouts**: Prevent indefinite hangs
7. **Use Circuit Breakers**: For failing services
8. **Clean Up Resources**: Even when errors occur
9. **Test Error Cases**: Don't just test happy paths
10. **Monitor in Production**: Track error rates and patterns
