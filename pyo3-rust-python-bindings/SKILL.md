---
name: pyo3-rust-python-bindings
description: Create zero-overhead Rust-Python communication for Tauri-Python IPC using PyO3 v0.27.1. Use when calling Python from Rust, managing GIL safely, converting types between Rust and Python, handling async Python from Rust, or implementing Tauri commands that invoke ML backends.
---

# PyO3 Rust-Python Bindings

## Overview

PyO3 v0.27.1 provides seamless zero-overhead Rust-Python interoperability. Use this skill to build Tauri applications that efficiently invoke Python ML/data processing backends, safely manage the Global Interpreter Lock (GIL), convert types between languages, and handle async Python operations from Rust without serialization overhead.

## When to Use This Skill

- Building Tauri applications that invoke Python ML/data processing backends
- Creating performant Rust-Python bridges without serialization overhead
- Implementing async Python operations from Rust code
- Converting between Rust and Python types safely and efficiently
- Managing GIL (Global Interpreter Lock) in multi-threaded contexts
- Building IPC channels between Tauri commands and Python modules
- Implementing low-latency Python callbacks from Rust

## Core Concepts

### PyO3 v0.27.1 Overview

PyO3 is a Rust library that provides seamless interoperability between Python and Rust through:
- Zero-copy conversions between compatible types
- Safe GIL management via Rust's type system
- Procedural macros for generating Python bindings from Rust functions
- Safe access to Python objects, exceptions, and protocols
- Full async/await support for Python coroutines

**Requirements:**
- Rust 1.83 or later
- Python 3.8 or later
- PyO3 0.27.1 in Cargo.toml

### Global Interpreter Lock (GIL)

The GIL is a mutex protecting Python's internal state. Critical points:
- Only one thread executes Python bytecode at a time
- Release GIL for blocking Rust operations using `allow_threads()`
- Acquire GIL for Python operations using `with_gil()`
- Async operations require careful GIL management per operation
- Never hold GIL across blocking operations

### Type Conversions

PyO3 provides automatic conversions via `FromPyObject` and `ToPyObject` traits:
- **Primitives:** i32, u64, f64, bool, String convert directly with zero cost
- **Collections:** Vec<T>, HashMap<K,V> convert to lists and dicts
- **Custom types:** Implement `FromPyObject`/`ToPyObject` traits
- **Object references:** Use `Py<T>` for GIL-independent references
- **Option:** `None` becomes `PyNone`, `Some(x)` passes through

### Error Handling

Python exceptions integrate with Rust's Result type:
- `PyErr` represents Python exceptions with traceback
- `PyResult<T>` is `Result<T, PyErr>` convenience alias
- `#[pyfunction]` auto-converts errors to exceptions
- Call `print(py)` to show Python traceback in logs
- Use `PyException` and subclasses to raise specific errors

### Async Integration

Calling async Python from Rust requires:
- `pyo3-asyncio` crate for event loop management
- `tokio` runtime for Rust side async
- `Python::with_gil()` wrapper for each async block
- Proper cleanup when exiting event loop context

### Tauri Command → Python Bridge

Standard pattern for invoking Python from Tauri frontend:
1. Initialize Python interpreter on app startup via `PyO3Initializer`
2. Define Rust function with `#[tauri::command]` decorator
3. Acquire GIL and import Python module
4. Call Python function and handle errors
5. Convert result to JSON-serializable type
6. Return to frontend via Tauri IPC message

## Common Patterns

### Simple Function Call
```rust
use pyo3::prelude::*;

#[tauri::command]
fn call_python_function(x: i32) -> Result<i32, String> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "my_module")
            .map_err(|e| e.to_string())?;
        let result: i32 = module
            .getattr("my_function")?
            .call1((x,))?
            .extract()?;
        Ok(result)
    })
}
```

### GIL Release for Blocking Rust Code
```rust
fn blocking_operation() -> PyResult<String> {
    Python::with_gil(|py| {
        // Acquire GIL for Python setup
        let result = Python::allow_threads(|| {
            // GIL released here - safe for blocking Rust code
            std::thread::sleep(std::time::Duration::from_secs(2));
            "Done".to_string()
        });
        Ok(result)
    })
}
```

### Type Conversion Example
```rust
use pyo3::types::{PyList, PyDict};

Python::with_gil(|py| {
    // Rust to Python
    let py_list = PyList::new_bound(py, &[1, 2, 3, 4]);

    // Python to Rust
    let rust_vec: Vec<i32> = py_list.extract()?;

    // Dictionary conversion
    let py_dict = PyDict::new_bound(py);
    py_dict.set_item("key", "value")?;
    let rust_map: HashMap<String, String> = py_dict.extract()?;
    Ok::<(), PyErr>(())
})
```

### Error Handling with Tracebacks
```rust
fn safe_python_call() -> Result<(), String> {
    Python::with_gil(|py| {
        match module.getattr("process_data") {
            Ok(func) => match func.call1(("input",)) {
                Ok(result) => {
                    println!("Success: {:?}", result);
                    Ok(())
                }
                Err(e) => {
                    eprintln!("Python error occurred:");
                    e.print(py);  // Prints traceback to stderr
                    Err(e.to_string())
                }
            },
            Err(e) => Err(format!("Module error: {}", e)),
        }
    })
}
```

### Returning Complex Types
```rust
#[tauri::command]
fn analyze_data(input: Vec<f64>) -> Result<serde_json::Value, String> {
    Python::with_gil(|py| {
        let py_list = PyList::new_bound(py, &input);
        let result = module
            .getattr("analyze")?
            .call1((py_list,))?;

        // Convert Python result to JSON for frontend
        let json_str: String = result.extract()?;
        Ok(serde_json::from_str(&json_str)?)
    })
}
```

## Resources

This skill includes:

- **scripts/generate-pyo3-bindings.py** - Auto-generate Rust bindings from Python API signatures
- **references/pyo3-function-calling.md** - Calling Python from Rust, GIL acquisition and release patterns
- **references/pyo3-type-conversion.md** - Complete Rust ↔ Python type mapping reference
- **references/pyo3-error-handling.md** - PyErr, PyResult patterns and exception handling
- **references/pyo3-async.md** - Async Python from Rust integration and event loop management
- **assets/pyo3-bridge-template.rs** - Ready-to-use Tauri command → Python bridge template

## Related Skills

- Tauri desktop application development
- Rust async/await patterns
- Python module design for Rust integration
- ML backend architecture patterns
