# PyO3 Async Python from Rust

## Overview

Calling async Python functions from Rust requires careful coordination between the Python event loop and Rust's async runtime. PyO3 provides integration through the `pyo3-asyncio` crate.

## Setup and Configuration

### Dependencies

Add to `Cargo.toml`:

```toml
[dependencies]
pyo3 = { version = "0.27.1", features = ["extension-module"] }
pyo3-asyncio = { version = "0.21", features = ["tokio-runtime"] }
tokio = { version = "1", features = ["full"] }
```

### Initializing the Event Loop

The Python event loop must be initialized on startup:

```rust
use pyo3_asyncio::TaskLocal;
use pyo3::prelude::*;

#[tokio::main]
async fn main() {
    // Initialize Python event loop for async operations
    pyo3_asyncio::tokio::run(|| async {
        // Async operations here
        println!("Async event loop ready");
    })
    .await
    .unwrap();
}
```

## Basic Async Function Calls

### Simple Coroutine Call

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;
use pyo3_asyncio::tokio::into_future_bound;

async fn call_async_python() -> PyResult<i32> {
    let result = Python::with_gil(|py| {
        // Import module
        let module = PyModule::import_bound(py, "async_module")?;

        // Get async function
        let coro = module.getattr("async_function")?.call1(("arg",))?;

        // Convert to Rust future
        into_future_bound(coro.bind(py))
    })?;

    // Await the future
    let value: i32 = result.await?;
    Ok(value)
}
```

### With Error Handling

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;
use pyo3_asyncio::tokio::into_future_bound;

async fn safe_async_call() -> Result<String, String> {
    let result = Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "async_ops")
            .map_err(|e| e.to_string())?;

        let coro = module
            .getattr("fetch_data")?
            .call0()
            .map_err(|e| e.to_string())?;

        into_future_bound(coro.bind(py))
    })?;

    result.await.map_err(|e| e.to_string())
}
```

## Tauri Command Integration

### Basic Async Tauri Command

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;
use pyo3_asyncio::tokio::into_future_bound;

#[tauri::command]
async fn async_python_command(input: String) -> Result<String, String> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "backend")
            .map_err(|e| e.to_string())?;

        let coro = module
            .getattr("process_async")?
            .call1((input,))
            .map_err(|e| e.to_string())?;

        into_future_bound(coro.bind(py))
    })?
    .await
    .map_err(|e| e.to_string())
}
```

### With Timeout

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;
use pyo3_asyncio::tokio::into_future_bound;
use tokio::time::{timeout, Duration};

#[tauri::command]
async fn async_python_with_timeout(
    input: String,
) -> Result<String, String> {
    let future = Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "backend")
            .map_err(|e| e.to_string())?;

        let coro = module
            .getattr("long_operation")?
            .call1((input,))
            .map_err(|e| e.to_string())?;

        into_future_bound(coro.bind(py))
    })?;

    match timeout(Duration::from_secs(30), future).await {
        Ok(Ok(result)) => Ok(result),
        Ok(Err(e)) => Err(format!("Python error: {}", e)),
        Err(_) => Err("Operation timed out".to_string()),
    }
}
```

## Advanced Patterns

### Multiple Concurrent Async Calls

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;
use pyo3_asyncio::tokio::into_future_bound;

async fn concurrent_operations() -> PyResult<Vec<i32>> {
    let futures = Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "async_module")?;

        // Create multiple coroutines
        let coro1 = module.getattr("task")?.call1((1,))?;
        let coro2 = module.getattr("task")?.call1((2,))?;
        let coro3 = module.getattr("task")?.call1((3,))?;

        Ok::<_, PyErr>((
            into_future_bound(coro1.bind(py))?,
            into_future_bound(coro2.bind(py))?,
            into_future_bound(coro3.bind(py))?,
        ))
    })?;

    // Run concurrently
    let (r1, r2, r3) = tokio::join!(futures.0, futures.1, futures.2);

    Ok(vec![r1?, r2?, r3?])
}
```

### Waiting for Multiple Futures

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;
use pyo3_asyncio::tokio::into_future_bound;
use futures::future::join_all;

async fn wait_all() -> PyResult<Vec<String>> {
    let futures = Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "async_module")?;

        let mut futs = Vec::new();
        for i in 0..5 {
            let coro = module.getattr("task")?.call1((i,))?;
            let fut = into_future_bound(coro.bind(py))?;
            futs.push(fut);
        }

        Ok::<_, PyErr>(futs)
    })?;

    let results = join_all(futures).await;

    results
        .into_iter()
        .collect::<Result<Vec<_>, _>>()
}
```

### Streaming/Yielding Results

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;

async fn stream_from_python() -> PyResult<()> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "async_module")?;

        // Get async generator
        let gen = module.getattr("async_generator")?.call0()?;

        // Iterate over async generator results
        loop {
            // Get next item
            let next_coro = gen.call_method0("__anext__")?;

            match next_coro {
                _ => {
                    // Convert to future and await
                    // (This is a simplified example)
                }
            }
        }

        Ok(())
    })
}
```

## GIL Management in Async Code

### Acquiring GIL in Async Block

```rust
async fn async_with_gil() -> PyResult<String> {
    Python::with_gil(|py| {
        // Quick Python operation with GIL
        let module = PyModule::import_bound(py, "module")?;
        let value: String = module
            .getattr("quick_function")?
            .call0()?
            .extract()?;

        Ok(value)
    })
}
```

### Releasing GIL During Blocking Operations

```rust
async fn async_with_blocking() -> PyResult<String> {
    let value = Python::with_gil(|py| {
        // Quick GIL work
        let module = PyModule::import_bound(py, "module")?;

        // Create coroutine
        let coro = module.getattr("async_function")?.call0()?;

        // Convert to future (releases GIL during await)
        pyo3_asyncio::tokio::into_future_bound(coro.bind(py))
    })?;

    // Blocking operation happens here with GIL released
    let result = value.await?;
    Ok(result)
}
```

## Python Async Example

Here's the Python side for reference:

```python
# async_module.py

import asyncio

async def async_function(value: str) -> str:
    """Simple async function."""
    await asyncio.sleep(1)
    return f"Processed: {value}"

async def long_operation(data: str) -> str:
    """Long-running async operation."""
    await asyncio.sleep(5)
    return f"Result: {data}"

async def task(id: int) -> int:
    """Concurrent task."""
    await asyncio.sleep(1)
    return id * 2

async def async_generator():
    """Async generator for streaming."""
    for i in range(5):
        await asyncio.sleep(0.5)
        yield i
```

## Error Handling in Async Code

### Catching Async Exceptions

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;
use pyo3_asyncio::tokio::into_future_bound;

async fn async_with_error_handling() -> Result<String, String> {
    let result = Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "async_module")
            .map_err(|e| format!("Import error: {}", e))?;

        let coro = module
            .getattr("risky_operation")?
            .call0()
            .map_err(|e| format!("Call error: {}", e))?;

        into_future_bound(coro.bind(py))
            .map_err(|e| format!("Future conversion error: {}", e))
    })?;

    result
        .await
        .map_err(|e| format!("Async execution error: {}", e))
}
```

### Retry Logic

```rust
use tokio::time::{sleep, Duration};

async fn async_with_retry(max_retries: u32) -> PyResult<String> {
    for attempt in 0..max_retries {
        match call_async_python().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                if attempt < max_retries - 1 {
                    eprintln!("Attempt {} failed: {}", attempt + 1, e);
                    sleep(Duration::from_millis(100 * (attempt as u64 + 1))).await;
                } else {
                    return Err(e);
                }
            }
        }
    }
    unreachable!()
}
```

## Performance Considerations

### 1. Minimize Time Under GIL

```rust
// Good - quick GIL work, async happens without GIL
async fn good_async() -> PyResult<String> {
    let future = Python::with_gil(|py| {
        let coro = PyModule::import_bound(py, "module")?
            .getattr("task")?
            .call0()?;
        pyo3_asyncio::tokio::into_future_bound(coro.bind(py))
    })?;

    future.await
}

// Less good - holding GIL during async operation
async fn bad_async() -> PyResult<String> {
    Python::with_gil(|py| {
        let future = pyo3_asyncio::tokio::into_future_bound(
            PyModule::import_bound(py, "module")?
                .getattr("task")?
                .call0()?
                .bind(py)
        )?;
        // GIL held during entire await
        future.await
    })
}
```

### 2. Batch Operations

```rust
// Good - create all futures, then await
async fn batched() -> PyResult<Vec<i32>> {
    let futures = Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "module")?;

        let mut futs = Vec::new();
        for i in 0..100 {
            let coro = module.getattr("task")?.call1((i,))?;
            futs.push(pyo3_asyncio::tokio::into_future_bound(coro.bind(py))?);
        }

        Ok::<_, PyErr>(futs)
    })?;

    futures::future::try_join_all(futures).await
}
```

### 3. Use Timeouts for Robustness

```rust
use tokio::time::{timeout, Duration};

async fn robust_call() -> PyResult<String> {
    let future = Python::with_gil(|py| {
        let coro = PyModule::import_bound(py, "module")?
            .getattr("task")?
            .call0()?;
        pyo3_asyncio::tokio::into_future_bound(coro.bind(py))
    })?;

    timeout(Duration::from_secs(30), future)
        .await
        .map_err(|_| PyErr::new::<pyo3::exceptions::PyTimeoutError, _>("Operation timed out"))?
}
```

## Debugging Async Code

### Enable Logging

```rust
use log::{debug, info};

async fn logged_async_call() -> PyResult<String> {
    info!("Starting async Python call");

    let result = Python::with_gil(|py| {
        debug!("Acquired GIL");
        let module = PyModule::import_bound(py, "module")?;
        debug!("Module imported");

        let coro = module.getattr("task")?.call0()?;
        debug!("Coroutine created");

        pyo3_asyncio::tokio::into_future_bound(coro.bind(py))
    })?;

    debug!("Awaiting future");
    let value = result.await?;
    info!("Async call completed");

    Ok(value)
}
```

### Debugging Tips

1. Use `log::debug!()` to trace execution
2. Print error tracebacks: `e.print(py)`
3. Check Python event loop status
4. Use `tokio-console` for async runtime debugging
5. Enable PyO3 debug features for detailed logging

## Common Pitfalls

### 1. Forgetting to Convert to Future

```rust
// Wrong - Coroutine not converted to future
async fn wrong() -> PyResult<String> {
    let coro = Python::with_gil(|py| {
        PyModule::import_bound(py, "module")?
            .getattr("task")?
            .call0()
    })?;

    // Can't await a Coroutine directly
    // coro.await
    Ok("".to_string())
}

// Correct - Use into_future_bound
async fn correct() -> PyResult<String> {
    let future = Python::with_gil(|py| {
        let coro = PyModule::import_bound(py, "module")?
            .getattr("task")?
            .call0()?;

        pyo3_asyncio::tokio::into_future_bound(coro.bind(py))
    })?;

    future.await
}
```

### 2. Holding GIL Across Await

```rust
// Wrong - GIL held during await
async fn bad_gil_handling() -> PyResult<String> {
    Python::with_gil(|py| {
        let future = pyo3_asyncio::tokio::into_future_bound(
            PyModule::import_bound(py, "module")?
                .getattr("task")?
                .call0()?
                .bind(py)
        )?;

        future.await  // GIL held here!
    })
}

// Good - Release GIL before await
async fn good_gil_handling() -> PyResult<String> {
    let future = Python::with_gil(|py| {
        let coro = PyModule::import_bound(py, "module")?
            .getattr("task")?
            .call0()?;

        pyo3_asyncio::tokio::into_future_bound(coro.bind(py))
    })?;

    future.await  // GIL released here
}
```

### 3. Missing Error Propagation

```rust
// Wrong - loses error context
async fn bad_error_handling() -> PyResult<String> {
    let future = Python::with_gil(|py| {
        let coro = PyModule::import_bound(py, "module")?
            .getattr("task")?
            .call0()?;

        pyo3_asyncio::tokio::into_future_bound(coro.bind(py))
    })?;  // Error lost here!

    future.await
}

// Good - proper error handling
async fn good_error_handling() -> PyResult<String> {
    let future = Python::with_gil(|py| {
        let coro = PyModule::import_bound(py, "module")
            .map_err(|e| format!("Import: {}", e))?
            .getattr("task")
            .map_err(|e| format!("Attr: {}", e))?
            .call0()
            .map_err(|e| format!("Call: {}", e))?;

        pyo3_asyncio::tokio::into_future_bound(coro.bind(py))
            .map_err(|e| format!("Future: {}", e))
    })?;

    future.await.map_err(|e| format!("Await: {}", e))
}
```
