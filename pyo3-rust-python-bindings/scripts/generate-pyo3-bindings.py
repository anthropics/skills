#!/usr/bin/env python3
"""
Auto-generate Rust PyO3 bindings from Python API signatures.

This script inspects a Python module and generates corresponding Rust function
stubs that can call the Python functions through PyO3. It analyzes function
signatures, docstrings, and type hints to generate type-safe bindings.

Usage:
    python generate-pyo3-bindings.py path/to/python_module.py output.rs
"""

import inspect
import sys
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple


def python_type_to_rust(py_type_str: str) -> str:
    """Convert Python type hint string to Rust type."""
    type_map = {
        "int": "i64",
        "float": "f64",
        "str": "String",
        "bool": "bool",
        "bytes": "Vec<u8>",
        "list": "Vec<PyObject>",
        "dict": "HashMap<String, PyObject>",
        "None": "()",
        "Optional": "Option",
    }

    # Handle Optional[T]
    if py_type_str.startswith("Optional"):
        inner = py_type_str.split("[")[1].rstrip("]")
        return f"Option<{python_type_to_rust(inner)}>"

    # Handle List[T]
    if py_type_str.startswith("List"):
        inner = py_type_str.split("[")[1].rstrip("]")
        return f"Vec<{python_type_to_rust(inner)}>"

    # Handle Dict[K, V]
    if py_type_str.startswith("Dict"):
        parts = py_type_str.split("[")[1].rstrip("]").split(", ")
        key_type = python_type_to_rust(parts[0])
        val_type = python_type_to_rust(parts[1])
        return f"HashMap<{key_type}, {val_type}>"

    return type_map.get(py_type_str, "PyObject")


def extract_type_hint(func: Any) -> Dict[str, str]:
    """Extract type hints from a Python function."""
    hints = {}
    try:
        if hasattr(func, "__annotations__"):
            for param, type_hint in func.__annotations__.items():
                hints[param] = str(type_hint)
    except Exception:
        pass
    return hints


def generate_function_binding(func_name: str, func: Any) -> str:
    """Generate Rust binding code for a Python function."""
    signature = inspect.signature(func)
    type_hints = extract_type_hint(func)
    docstring = inspect.getdoc(func) or ""

    # Generate parameter list
    params = []
    for param_name, param in signature.parameters.items():
        if param_name == "self":
            continue
        type_hint = type_hints.get(param_name, "PyObject")
        rust_type = python_type_to_rust(type_hint)
        params.append(f"{param_name}: {rust_type}")

    params_str = ", ".join(params) if params else ""

    # Generate return type
    return_hint = type_hints.get("return", "PyObject")
    rust_return = python_type_to_rust(return_hint)

    # Build Rust function
    code = f"""/// Wrapper for Python function: {func_name}
/// {docstring.split(chr(10))[0] if docstring else 'No documentation available'}
fn {func_name}({params_str}) -> PyResult<{rust_return}> {{
    Python::with_gil(|py| {{
        let module = PyModule::import_bound(py, "your_module")?;
        let func = module.getattr("{func_name}")?;
"""

    # Build call parameters
    if params:
        call_params = ", ".join([p.split(":")[0] for p in params])
        code += f"        let result = func.call1(({call_params},))?;\n"
    else:
        code += f"        let result = func.call0()?;\n"

    code += f"        result.extract()\n"
    code += f"    }}\n"
    code += f"}}\n"

    return code


def generate_module_bindings(module_path: str) -> str:
    """Generate Rust bindings for all public functions in a module."""
    module_name = Path(module_path).stem
    sys.path.insert(0, str(Path(module_path).parent))

    try:
        module = __import__(module_name)
    except ImportError as e:
        print(f"Error importing module: {e}", file=sys.stderr)
        return ""

    code = f"""// Auto-generated PyO3 bindings for {module_name}
// Generated using: generate-pyo3-bindings.py

use pyo3::prelude::*;
use pyo3::types::PyModule;
use std::collections::HashMap;

"""

    public_functions = [
        (name, obj)
        for name, obj in inspect.getmembers(module)
        if inspect.isfunction(obj) and not name.startswith("_")
    ]

    for func_name, func_obj in public_functions:
        code += generate_function_binding(func_name, func_obj)
        code += "\n"

    code += """
// Module initialization for Tauri
#[tauri::command]
fn invoke_python_function(
    function_name: String,
    args: Vec<String>,
) -> Result<String, String> {
    Python::with_gil(|py| {
        let module = PyModule::import_bound(py, "your_module")
            .map_err(|e| e.to_string())?;

        let func = module
            .getattr(&function_name)
            .map_err(|e| e.to_string())?;

        let result = func
            .call1((args,))
            .map_err(|e| e.to_string())?;

        let json_result: String = result.extract().map_err(|e| e.to_string())?;
        Ok(json_result)
    })
}
"""

    return code


def main():
    if len(sys.argv) < 2:
        print(
            "Usage: python generate-pyo3-bindings.py <python_module> [output_file]",
            file=sys.stderr,
        )
        sys.exit(1)

    module_path = sys.argv[1]
    output_path = sys.argv[2] if len(sys.argv) > 2 else "generated_bindings.rs"

    if not Path(module_path).exists():
        print(f"Error: Module not found: {module_path}", file=sys.stderr)
        sys.exit(1)

    bindings = generate_module_bindings(module_path)

    with open(output_path, "w") as f:
        f.write(bindings)

    print(f"Generated bindings written to: {output_path}")


if __name__ == "__main__":
    main()
