# PyO3 Type Conversion Reference

## Overview

PyO3 provides automatic type conversion between Rust and Python through the `FromPyObject` and `ToPyObject` traits. Most conversions are zero-copy when possible.

## Primitive Type Conversions

### Numeric Types

| Python | Rust | Notes |
|--------|------|-------|
| `int` | `i8`, `i16`, `i32`, `i64`, `i128` | Supports all Rust integer types |
| `int` | `u8`, `u16`, `u32`, `u64`, `u128` | Unsigned types |
| `float` | `f32`, `f64` | Floating point conversion |
| `bool` | `bool` | Direct conversion |

```rust
// Python to Rust
Python::with_gil(|py| {
    let py_int: i32 = py.eval_bound("42", None, None)?.extract()?;
    let py_float: f64 = py.eval_bound("3.14", None, None)?.extract()?;
    let py_bool: bool = py.eval_bound("True", None, None)?.extract()?;
    Ok::<(), PyErr>(())
})?;

// Rust to Python
Python::with_gil(|py| {
    let rust_int: i32 = 42;
    let py_obj = rust_int.into_py(py);
    Ok::<(), PyErr>(())
})?;
```

### String Types

| Python | Rust | Notes |
|--------|------|-------|
| `str` | `String` | UTF-8 string, owned |
| `str` | `&str` | UTF-8 string, borrowed |
| `bytes` | `Vec<u8>` | Byte vector |
| `bytes` | `&[u8]` | Byte slice |

```rust
use pyo3::prelude::*;

Python::with_gil(|py| {
    // Python str to Rust String
    let py_str = py.eval_bound("'hello'", None, None)?;
    let rust_str: String = py_str.extract()?;

    // Rust String to Python str
    let rust_string = "hello".to_string();
    let py_obj = rust_string.into_py(py);

    // Python bytes to Rust Vec<u8>
    let py_bytes = py.eval_bound("b'data'", None, None)?;
    let rust_bytes: Vec<u8> = py_bytes.extract()?;

    Ok::<(), PyErr>(())
})?;
```

## Collection Type Conversions

### Lists and Vectors

```rust
use pyo3::types::PyList;

Python::with_gil(|py| {
    // Rust Vec to Python list
    let rust_vec = vec![1, 2, 3, 4];
    let py_list = PyList::new_bound(py, &rust_vec);

    // Python list to Rust Vec
    let py_list = py.eval_bound("[1, 2, 3]", None, None)?;
    let rust_vec: Vec<i32> = py_list.extract()?;

    // List of mixed types
    let py_mixed = py.eval_bound("[1, 'hello', 3.14]", None, None)?;
    let rust_mixed: Vec<PyObject> = py_mixed.extract()?;

    Ok::<(), PyErr>(())
})?;
```

### Dictionaries and HashMaps

```rust
use pyo3::types::PyDict;
use std::collections::HashMap;

Python::with_gil(|py| {
    // Rust HashMap to Python dict
    let mut rust_map = HashMap::new();
    rust_map.insert("key1", 42);
    rust_map.insert("key2", 99);
    let py_dict = PyDict::new_bound(py);
    for (k, v) in rust_map {
        py_dict.set_item(k, v)?;
    }

    // Python dict to Rust HashMap
    let py_dict = py.eval_bound("{'a': 1, 'b': 2}", None, None)?;
    let rust_map: HashMap<String, i32> = py_dict.extract()?;

    // Using into_py_dict helper
    let dict = [("key", 42), ("other", 99)].into_py_dict_bound(py);
    let rust_map: HashMap<String, i32> = dict.extract()?;

    Ok::<(), PyErr>(())
})?;
```

### Tuples

```rust
Python::with_gil(|py| {
    // Python tuple to Rust tuple
    let py_tuple = py.eval_bound("(1, 'hello', 3.14)", None, None)?;
    let rust_tuple: (i32, String, f64) = py_tuple.extract()?;

    // Rust tuple to Python tuple
    let rust_tuple = (42, "hello", 3.14);
    let py_tuple = rust_tuple.into_py(py);

    Ok::<(), PyErr>(())
})?;
```

### Sets

```rust
use pyo3::types::PySet;
use std::collections::HashSet;

Python::with_gil(|py| {
    // Rust HashSet to Python set
    let rust_set: HashSet<i32> = [1, 2, 3].into_iter().collect();
    let py_set = PySet::new_bound(py, &rust_set)?;

    // Python set to Rust HashSet
    let py_set = py.eval_bound("{1, 2, 3}", None, None)?;
    let rust_set: HashSet<i32> = py_set.extract()?;

    Ok::<(), PyErr>(())
})?;
```

## Option and Result Types

### Option<T>

```rust
Python::with_gil(|py| {
    // Python None to Rust None
    let py_none = py.None();
    let rust_none: Option<i32> = py_none.extract()?;
    assert_eq!(rust_none, None);

    // Python value to Rust Some
    let py_val = py.eval_bound("42", None, None)?;
    let rust_some: Option<i32> = py_val.extract()?;
    assert_eq!(rust_some, Some(42));

    // Rust Option to Python
    let rust_none: Option<String> = None;
    let py_obj = rust_none.into_py(py);

    Ok::<(), PyErr>(())
})?;
```

### Result<T, E>

PyO3 uses `PyResult<T>` which is `Result<T, PyErr>`. Errors are automatically converted to Python exceptions.

```rust
fn operation() -> PyResult<i32> {
    Python::with_gil(|py| {
        // PyErr gets converted to Python exception
        let module = PyModule::import_bound(py, "nonexistent")?;
        Ok(42)
    })
}
```

## Custom Type Conversions

### Implementing FromPyObject

```rust
use pyo3::prelude::*;
use pyo3::types::PyDict;

#[derive(Clone)]
struct Point {
    x: f64,
    y: f64,
}

impl<'py> FromPyObject<'py> for Point {
    fn extract_bound(ob: &Bound<'py, PyAny>) -> PyResult<Self> {
        // Expect a dict with 'x' and 'y' keys
        let dict = <&Bound<'py, PyDict>>::try_from(ob)?;

        Ok(Point {
            x: dict.get_item("x")?.extract()?,
            y: dict.get_item("y")?.extract()?,
        })
    }
}

// Usage
Python::with_gil(|py| {
    let py_point = py.eval_bound("{'x': 1.0, 'y': 2.0}", None, None)?;
    let point: Point = py_point.extract()?;
    println!("Point: ({}, {})", point.x, point.y);
    Ok::<(), PyErr>(())
})?;
```

### Implementing IntoPy

```rust
use pyo3::prelude::*;
use pyo3::types::PyDict;

impl IntoPy<PyObject> for Point {
    fn into_py(self, py: Python<'_>) -> PyObject {
        let dict = PyDict::new_bound(py);
        let _ = dict.set_item("x", self.x);
        let _ = dict.set_item("y", self.y);
        dict.into()
    }
}

// Usage
Python::with_gil(|py| {
    let point = Point { x: 1.0, y: 2.0 };
    let py_obj = point.into_py(py);
    Ok::<(), PyErr>(())
})?;
```

## Complex Conversion Patterns

### Nested Collections

```rust
use pyo3::types::PyList;

Python::with_gil(|py| {
    // List of lists
    let py_list_of_lists = py.eval_bound("[[1, 2], [3, 4]]", None, None)?;
    let rust_vec: Vec<Vec<i32>> = py_list_of_lists.extract()?;

    // Dict with list values
    let py_dict = py.eval_bound("{'a': [1, 2], 'b': [3, 4]}", None, None)?;
    let rust_map: HashMap<String, Vec<i32>> = py_dict.extract()?;

    Ok::<(), PyErr>(())
})?;
```

### Array-like Objects

```rust
use pyo3::types::{PyList, PyArray1};
use numpy::PyReadonlyArray1;

// When using numpy types
Python::with_gil(|py| {
    let arr = py.eval_bound("numpy.array([1, 2, 3])", None, None)?;
    let rust_array: PyReadonlyArray1<i32> = PyArray1::from_bound(&arr)?.readonly();

    Ok::<(), PyErr>(())
})?;
```

## Conversion Error Handling

### Handling Conversion Failures

```rust
Python::with_gil(|py| {
    let py_val = py.eval_bound("'not a number'", None, None)?;

    match py_val.extract::<i32>() {
        Ok(num) => println!("Got number: {}", num),
        Err(e) => {
            // Handle conversion error
            eprintln!("Conversion failed: {}", e);
            e.print(py);
        }
    }

    Ok::<(), PyErr>(())
})?;
```

### Type Checking Before Conversion

```rust
use pyo3::types::PyAny;

Python::with_gil(|py| {
    let py_val = py.eval_bound("42", None, None)?;

    if let Ok(int_val) = py_val.extract::<i32>() {
        println!("Is integer: {}", int_val);
    } else if let Ok(str_val) = py_val.extract::<String>() {
        println!("Is string: {}", str_val);
    } else {
        println!("Unknown type");
    }

    Ok::<(), PyErr>(())
})?;
```

## Type Mapping Reference

### Quick Reference Table

| Python Type | Rust Type | Method |
|-------------|-----------|--------|
| `None` | `()` or `Option<T>` | `.extract()` |
| `bool` | `bool` | `.extract()` |
| `int` | `i64`, `u32`, etc. | `.extract()` |
| `float` | `f64`, `f32` | `.extract()` |
| `str` | `String`, `&str` | `.extract()` |
| `bytes` | `Vec<u8>`, `&[u8]` | `.extract()` |
| `list` | `Vec<T>` | `.extract()` |
| `tuple` | `(T, U, ...)` | `.extract()` |
| `dict` | `HashMap<K, V>` | `.extract()` |
| `set` | `HashSet<T>` | `.extract()` |
| Custom | `Py<T>` | `.extract_bound()` |

## Performance Considerations

### Zero-Copy Conversions

These conversions are zero-copy when possible:
- `&str` ↔ Python `str` (borrowed references)
- `&[u8]` ↔ Python `bytes` (borrowed references)
- `Bound<'py, PyList>` ↔ list operations (borrowed operations)

### Owned Conversions

These require allocation:
- `String` ↔ Python `str` (owned string)
- `Vec<T>` ↔ Python `list` (new collection)
- `HashMap<K, V>` ↔ Python `dict` (new dict)

### Optimization Tips

```rust
// Good - borrowed reference
fn process(data: &str) -> PyResult<()> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "process")?;
        module.getattr("handle")?.call1((data,))?;
        Ok(())
    })
}

// Less efficient - owned copy
fn process_owned(data: String) -> PyResult<()> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "process")?;
        module.getattr("handle")?.call1((data.clone(),))?;
        Ok(())
    })
}
```

Use borrowed references (`&str`, `&[T]`) when possible to avoid unnecessary allocations.
