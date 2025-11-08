# PyO3 Function Calling and GIL Management

## Calling Python Functions from Rust

### Basic Function Call Pattern

The fundamental pattern for calling Python from Rust:

```rust
use pyo3::prelude::*;

fn call_python() -> PyResult<()> {
    Python::with_gil(|py| {
        // Import the module
        let module = PyModule::import_bound(py, "my_module")?;

        // Get the function
        let func = module.getattr("my_function")?;

        // Call with arguments
        let result = func.call1((arg1, arg2))?;

        // Extract the result
        let value: i32 = result.extract()?;
        Ok(())
    })
}
```

### One-Line Function Calls

For simple calls, you can combine operations:

```rust
let result: String = PyModule::import_bound(py, "module")?
    .getattr("func")?
    .call1(("arg",))?
    .extract()?;
```

### Calling with Different Argument Counts

```rust
// No arguments
func.call0()?;

// One argument
func.call1(("arg",))?;

// Multiple arguments - note the trailing comma for tuples
func.call1(("arg1", "arg2", 42))?;

// Named arguments
let kwargs = [("key", "value")].into_py_dict_bound(py);
func.call((), Some(&kwargs))?;

// Mixed positional and keyword arguments
let args = ("pos_arg",);
let kwargs = [("key", py.None())].into_py_dict_bound(py);
func.call(args, Some(&kwargs))?;
```

## Global Interpreter Lock (GIL)

### What is the GIL?

The Python Global Interpreter Lock (GIL) is a mutex that protects Python's internal state. Only one thread can execute Python bytecode at a time. Key implications:

- Rust code holding the GIL prevents other threads from running Python
- Blocking operations should release the GIL
- Multi-threaded Python requires careful GIL management
- Async operations need GIL handling at each await point

### Acquiring the GIL

Use `Python::with_gil()` to acquire the GIL:

```rust
use pyo3::prelude::*;

fn acquire_gil() {
    Python::with_gil(|py| {
        // GIL is acquired here
        // Safe to call Python code
        let module = PyModule::import_bound(py, "sys")?;
    });
    // GIL is released when closure exits
}
```

### Releasing the GIL

For long-running Rust code, release the GIL using `allow_threads()`:

```rust
fn long_operation() -> PyResult<String> {
    Python::with_gil(|py| {
        // Some quick Python setup
        let config = PyModule::import_bound(py, "config")?
            .getattr("setting")?
            .extract()?;

        // Release GIL for blocking operation
        let result = Python::allow_threads(|| {
            // GIL released here - safe for blocking Rust code
            // Other threads can run Python code
            compute_expensive_algorithm(&config)
        });

        Ok(result)
    })
}
```

The `allow_threads` block will panic if it detects the GIL is already released.

### GIL-Independent References

Use `Py<T>` to hold Python objects without holding the GIL:

```rust
use pyo3::Py;
use pyo3::types::PyModule;

struct DataProcessor {
    py_module: Py<PyModule>,
}

impl DataProcessor {
    fn new(module: Py<PyModule>) -> Self {
        DataProcessor { py_module: module }
    }

    fn process(&self, data: Vec<i32>) -> PyResult<Vec<i32>> {
        Python::with_gil(|py| {
            let module = self.py_module.bind(py);
            let func = module.getattr("process")?;
            let result = func.call1((data,))?;
            result.extract()
        })
    }
}
```

## Common Calling Patterns

### Pattern 1: Simple Module Function

```rust
#[tauri::command]
fn analyze_data(input: Vec<f64>) -> Result<f64, String> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "analysis")
            .map_err(|e| format!("Import failed: {}", e))?;

        let result = module
            .getattr("analyze")?
            .call1((input,))?
            .extract::<f64>()?;

        Ok(result)
    })
}
```

### Pattern 2: Class Method Call

```rust
fn call_class_method() -> PyResult<String> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "mymodule")?;

        // Get class
        let class = module.getattr("MyClass")?;

        // Create instance
        let instance = class.call0()?;

        // Call method
        let result = instance
            .getattr("process")?
            .call1(("data",))?
            .extract()?;

        Ok(result)
    })
}
```

### Pattern 3: Async Function Awaiting

```rust
use pyo3_asyncio::TaskLocal;

#[tokio::main]
async fn call_async_python() -> PyResult<String> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "async_module")?;

        let coro = module
            .getattr("async_function")?
            .call1(("arg",))?;

        // Get the event loop
        let task = pyo3_asyncio::tokio::into_future_bound(coro.bind(py))?;
        Ok(task)
    })
}
```

### Pattern 4: Error Handling with Traceback

```rust
fn safe_python_call() -> Result<i32, String> {
    Python::with_gil(|py| {
        match PyModule::import_bound(py, "ops") {
            Ok(module) => {
                match module.getattr("compute").and_then(|f| f.call1((42,))) {
                    Ok(result) => {
                        match result.extract::<i32>() {
                            Ok(value) => Ok(value),
                            Err(e) => {
                                eprintln!("Type conversion error: {}", e);
                                Err(e.to_string())
                            }
                        }
                    }
                    Err(e) => {
                        // Print full Python traceback
                        eprintln!("Python function error:");
                        e.print(py);
                        Err(e.to_string())
                    }
                }
            }
            Err(e) => {
                eprintln!("Failed to import module:");
                e.print(py);
                Err(e.to_string())
            }
        }
    })
}
```

### Pattern 5: Lambda and Callback

```rust
fn use_python_lambda() -> PyResult<i32> {
    Python::with_gil(|py| {
        let code = "lambda x: x * 2";
        let lambda = py.eval_bound(code, None, None)?;

        let result = lambda.call1((5,))?;
        let value: i32 = result.extract()?;

        Ok(value)
    })
}
```

## Best Practices

### 1. Always Use `with_gil()` for Python Access

```rust
// Good
Python::with_gil(|py| {
    PyModule::import_bound(py, "module")?;
});

// Bad - will panic if called outside with_gil
// let module = unsafe { /* accessing Python without GIL */ };
```

### 2. Release GIL for Blocking Operations

```rust
// Good - GIL released during blocking call
let result = Python::allow_threads(|| {
    std::thread::sleep(Duration::from_secs(5));
});

// Bad - GIL held during blocking call, blocking other threads
let result = {
    std::thread::sleep(Duration::from_secs(5));
};
```

### 3. Use Error Propagation

```rust
// Good - uses ? operator for clean error handling
fn compute() -> PyResult<i32> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "math")?;
        let result = module.getattr("compute")?.call0()?.extract()?;
        Ok(result)
    })
}

// Less good - nested match statements
fn compute_verbose() -> PyResult<i32> {
    Python::with_gil(|py| {
        match PyModule::import_bound(py, "math") {
            Ok(module) => {
                match module.getattr("compute") {
                    Ok(func) => {
                        match func.call0() {
                            Ok(result) => result.extract(),
                            Err(e) => Err(e),
                        }
                    }
                    Err(e) => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    })
}
```

### 4. Cache Module References

```rust
// Good - module loaded once
struct Engine {
    module: Py<PyModule>,
}

impl Engine {
    fn call_function(&self) -> PyResult<i32> {
        Python::with_gil(|py| {
            let module = self.module.bind(py);
            // Call functions on cached module
            Ok(42)
        })
    }
}

// Less efficient - module imported every time
fn call_function() -> PyResult<i32> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "module")?;
        // Call functions
        Ok(42)
    })
}
```

## Multi-threaded Considerations

When calling Python from multiple threads:

1. Each thread needs its own `with_gil()` call
2. Never share `&PyObject` across threads - use `Py<T>` instead
3. Consider the performance implications of GIL contention
4. Use `allow_threads()` to release GIL in worker threads

```rust
fn multi_threaded_example() -> PyResult<()> {
    let handles: Vec<_> = (0..4)
        .map(|i| {
            std::thread::spawn(move || {
                Python::with_gil(|py| {
                    let module = PyModule::import_bound(py, "worker")?;
                    let func = module.getattr("process")?;
                    let _result = func.call1((i,))?;
                    Ok::<(), PyErr>(())
                })
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap()?;
    }

    Ok(())
}
```
