# PyO3 Error Handling Reference

## PyErr and PyResult

### PyErr Structure

`PyErr` represents a Python exception with the following information:
- **Exception type** (e.g., `ValueError`, `TypeError`)
- **Exception message**
- **Traceback** (if available)
- **Python instance** of the exception

### PyResult<T>

`PyResult<T>` is an alias for `Result<T, PyErr>`. It's the standard return type for PyO3 operations:

```rust
use pyo3::prelude::*;

type PyResult<T> = Result<T, PyErr>;

fn python_operation() -> PyResult<i32> {
    Python::with_gil(|py| {
        let result = 42;
        Ok(result)
    })
}
```

## Creating and Raising Exceptions

### Raising Python Exceptions from Rust

```rust
use pyo3::exceptions::*;
use pyo3::prelude::*;

fn raise_value_error() -> PyResult<()> {
    Err(PyValueError::new_err("This is a value error"))
}

fn raise_type_error() -> PyResult<()> {
    Err(PyTypeError::new_err("Expected integer"))
}

fn raise_runtime_error() -> PyResult<()> {
    Err(PyRuntimeError::new_err("Something went wrong"))
}

fn raise_custom_message() -> PyResult<i32> {
    Python::with_gil(|py| {
        Err(PyException::new_err("Custom error message"))
    })
}
```

### Exception Types

PyO3 provides wrappers for common Python exceptions:

| Python Exception | PyO3 Type | Use Case |
|------------------|-----------|----------|
| `ValueError` | `PyValueError` | Invalid value |
| `TypeError` | `PyTypeError` | Wrong type |
| `KeyError` | `PyKeyError` | Missing dictionary key |
| `IndexError` | `PyIndexError` | Out of bounds access |
| `AttributeError` | `PyAttributeError` | Missing attribute |
| `RuntimeError` | `PyRuntimeError` | Runtime error |
| `OSError` | `PyOSError` | Operating system error |
| `ZeroDivisionError` | `PyZeroDivisionError` | Division by zero |
| `ImportError` | `PyImportError` | Module import failed |

```rust
use pyo3::exceptions::*;
use pyo3::prelude::*;

fn validate_input(value: i32) -> PyResult<String> {
    if value < 0 {
        return Err(PyValueError::new_err("Value must be non-negative"));
    }

    if value > 1000 {
        return Err(PyValueError::new_err("Value too large"));
    }

    Ok(format!("Valid: {}", value))
}
```

## Error Propagation

### Using the ? Operator

The `?` operator automatically propagates `PyErr`:

```rust
use pyo3::prelude::*;
use pyo3::types::PyModule;

fn propagate_errors() -> PyResult<i32> {
    Python::with_gil(|py| {
        // If any of these fail, the error is returned immediately
        let module = PyModule::import_bound(py, "math")?;
        let func = module.getattr("sqrt")?;
        let result = func.call1((16.0,))?;
        let value: f64 = result.extract()?;
        Ok(value as i32)
    })
}
```

### Converting to String

Convert `PyErr` to a human-readable string:

```rust
use pyo3::prelude::*;

fn handle_with_string() -> Result<i32, String> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "nonexistent")
            .map_err(|e| e.to_string())?;  // Convert to String
        Ok(42)
    })
}
```

## Catching and Handling Exceptions

### Basic Exception Handling

```rust
use pyo3::prelude::*;

fn catch_exception() -> Result<i32, String> {
    Python::with_gil(|py| {
        match PyModule::import_bound(py, "problematic") {
            Ok(module) => {
                match module.getattr("function") {
                    Ok(func) => {
                        match func.call0() {
                            Ok(result) => {
                                match result.extract::<i32>() {
                                    Ok(value) => Ok(value),
                                    Err(e) => {
                                        eprintln!("Extraction error: {}", e);
                                        Err(e.to_string())
                                    }
                                }
                            }
                            Err(e) => {
                                eprintln!("Call error: {}", e);
                                Err(e.to_string())
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("Attribute error: {}", e);
                        Err(e.to_string())
                    }
                }
            }
            Err(e) => {
                eprintln!("Import error: {}", e);
                Err(e.to_string())
            }
        }
    })
}
```

### Checking Exception Type

```rust
use pyo3::exceptions::*;
use pyo3::prelude::*;

fn check_exception_type() -> PyResult<()> {
    Python::with_gil(|py| {
        let result = PyModule::import_bound(py, "bad_module");

        if let Err(e) = result {
            if e.matches(py, PyImportError::type_object_bound(py)) {
                println!("Import error caught!");
            } else if e.matches(py, PyAttributeError::type_object_bound(py)) {
                println!("Attribute error caught!");
            } else {
                println!("Other error: {}", e);
            }
        }

        Ok(())
    })
}
```

### Chaining Results

```rust
use pyo3::prelude::*;

fn chain_operations() -> PyResult<String> {
    Python::with_gil(|py| {
        PyModule::import_bound(py, "module")?
            .getattr("func")?
            .call0()?
            .extract()
    })
}
```

## Printing Tracebacks

### Using print(py)

The `print()` method on `PyErr` shows the full Python traceback:

```rust
use pyo3::prelude::*;

fn debug_error() {
    Python::with_gil(|py| {
        if let Err(e) = some_operation(py) {
            eprintln!("Python error occurred:");
            e.print(py);  // Prints full traceback to stderr
        }
    })
}

fn some_operation(py: Python<'_>) -> PyResult<()> {
    Err(PyErr::new::<pyo3::exceptions::PyRuntimeError, _>(
        "Something went wrong",
    ))
}
```

### Capturing Error Information

```rust
use pyo3::prelude::*;

fn get_error_details(py: Python<'_>, e: &PyErr) {
    // Get exception type
    println!("Type: {}", e.get_type_bound(py));

    // Get exception value
    println!("Value: {}", e.value_bound(py));

    // Get traceback
    if let Some(traceback) = e.traceback_bound(py) {
        println!("Has traceback: true");
    } else {
        println!("Has traceback: false");
    }

    // Print full traceback
    e.print(py);
}
```

## Custom Error Handling Patterns

### Pattern 1: Convert to Tauri Error

```rust
use pyo3::prelude::*;

#[tauri::command]
fn python_command(input: String) -> Result<String, String> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "backend")
            .map_err(|e| format!("Failed to import: {}", e))?;

        let result = module
            .getattr("process")?
            .call1((input,))?
            .extract::<String>()?;

        Ok(result)
    })
}
```

### Pattern 2: Detailed Error Logging

```rust
use pyo3::prelude::*;

fn operation_with_logging() -> PyResult<i32> {
    Python::with_gil(|py| {
        match PyModule::import_bound(py, "module") {
            Ok(module) => {
                println!("Module imported successfully");

                match module.getattr("compute") {
                    Ok(func) => {
                        println!("Function found");

                        match func.call1((42,)) {
                            Ok(result) => {
                                println!("Function executed");
                                result.extract()
                            }
                            Err(e) => {
                                eprintln!("Function call failed");
                                e.print(py);
                                Err(e)
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("Function not found");
                        Err(e)
                    }
                }
            }
            Err(e) => {
                eprintln!("Import failed");
                e.print(py);
                Err(e)
            }
        }
    })
}
```

### Pattern 3: Fallback on Error

```rust
use pyo3::prelude::*;

fn operation_with_fallback() -> PyResult<i32> {
    Python::with_gil(|py| {
        match PyModule::import_bound(py, "preferred") {
            Ok(module) => {
                match module.getattr("compute") {
                    Ok(func) => func.call0()?.extract(),
                    Err(_) => {
                        println!("Fallback to default implementation");
                        Ok(42)
                    }
                }
            }
            Err(_) => {
                println!("Preferred module not found, using default");
                Ok(0)
            }
        }
    })
}
```

### Pattern 4: Error Wrapping

```rust
use pyo3::prelude::*;
use std::fmt;

#[derive(Debug)]
enum AppError {
    PythonError(String),
    ProcessingError(String),
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            AppError::PythonError(msg) => write!(f, "Python error: {}", msg),
            AppError::ProcessingError(msg) => write!(f, "Processing error: {}", msg),
        }
    }
}

impl From<PyErr> for AppError {
    fn from(err: PyErr) -> Self {
        AppError::PythonError(err.to_string())
    }
}

fn wrapped_operation() -> Result<i32, AppError> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "module")?;
        let result = module
            .getattr("compute")?
            .call0()?
            .extract::<i32>()?;

        Ok(result)
    })
}
```

## Exception Handling in Macros

### Using #[pyfunction]

Functions decorated with `#[pyfunction]` automatically convert `PyErr` to Python exceptions:

```rust
use pyo3::prelude::*;

#[pyfunction]
fn compute(x: i32) -> PyResult<i32> {
    if x < 0 {
        Err(PyValueError::new_err("x must be non-negative"))
    } else {
        Ok(x * 2)
    }
}

#[pymodule]
fn my_module(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(compute, m)?)?;
    Ok(())
}
```

### Using #[pymethods]

Methods in classes also handle errors:

```rust
use pyo3::prelude::*;

#[pyclass]
struct Calculator;

#[pymethods]
impl Calculator {
    fn divide(&self, a: f64, b: f64) -> PyResult<f64> {
        if b == 0.0 {
            Err(PyZeroDivisionError::new_err("Division by zero"))
        } else {
            Ok(a / b)
        }
    }
}
```

## Best Practices

### 1. Always Use PyResult for Python Operations

```rust
// Good - returns PyResult
fn safe_operation() -> PyResult<i32> {
    Python::with_gil(|py| {
        let result = PyModule::import_bound(py, "mod")?;
        Ok(42)
    })
}

// Bad - ignores errors
fn unsafe_operation() -> i32 {
    Python::with_gil(|py| {
        let _result = PyModule::import_bound(py, "mod").unwrap();
        42
    })
}
```

### 2. Print Tracebacks for Debugging

```rust
// Good - shows full Python error
if let Err(e) = operation(py) {
    eprintln!("Error:");
    e.print(py);
}

// Less helpful - only shows string representation
if let Err(e) = operation(py) {
    eprintln!("Error: {}", e);
}
```

### 3. Convert Errors at Boundaries

```rust
// Good - convert PyErr to String at command boundary
#[tauri::command]
fn command_handler() -> Result<String, String> {
    Python::with_gil(|py| {
        operation(py).map_err(|e| e.to_string())
    })
}

// Less good - expose PyErr to frontend
#[tauri::command]
fn bad_handler() -> PyResult<String> {
    // PyErr doesn't serialize to JSON
    Ok("result".to_string())
}
```

### 4. Provide Context in Error Messages

```rust
// Good - informative error
Err(PyValueError::new_err(
    "Expected non-negative value, got: -5"
))

// Less helpful - vague error
Err(PyValueError::new_err("Invalid input"))
```

### 5. Match on Exception Type When Needed

```rust
// Good - specific error handling
match operation() {
    Ok(result) => process(result),
    Err(e) if e.matches(Python::with_gil(|py| PyImportError::type_object_bound(py))) => {
        println!("Module not found, using default");
    }
    Err(e) => {
        eprintln!("Unexpected error: {}", e);
    }
}

// Less precise - catch-all
match operation() {
    Ok(result) => process(result),
    Err(e) => eprintln!("Error: {}", e),
}
```
