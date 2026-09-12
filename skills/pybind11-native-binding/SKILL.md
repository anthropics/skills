---
name: pybind11-native-binding-debugger
description: Diagnoses common pybind11 Python ↔ C++ build, linkage, and binding errors and provides minimal corrective actions.
license: See LICENSE.txt for complete terms
---

# Pybind11 Native Binding Debugger

This skill helps diagnose and resolve common issues when building or running Python ↔ C++ extensions using `pybind11`.

It focuses on **error classification and minimal corrective actions**, not full build system tutorials.

---

# When to use this skill

Use this skill when encountering issues such as:

- ImportError when loading compiled extensions
- Missing symbols or unresolved external references
- Constructor or method binding mismatches
- ABI or Python version mismatch errors
- Include path or build configuration failures
- Runtime crashes in pybind11 modules

---

# Core Diagnosis Flow

## Step 1: Identify error type

Classify the issue into one of the following categories:

### 1. Import / module load failure
Typical symptoms:
- `ImportError: DLL load failed`
- `undefined symbol`
- module not found after compilation

Likely causes:
- missing compiled binary
- incorrect build output path
- Python environment mismatch

---

### 2. Binding mismatch (C++ ↔ Python API)
Typical symptoms:
- constructor errors
- `TypeError: __init__() takes...`
- missing attributes or methods

Likely causes:
- mismatched `PYBIND11_MODULE` definitions
- missing `py::arg` or signature mismatch
- methods not exposed in bindings

---

### 3. Compilation or linkage failure
Typical symptoms:
- linker errors (`LNK...`, `undefined reference`)
- include errors (`pybind11/pybind11.h not found`)

Likely causes:
- missing include directories
- pybind11 not installed in active environment
- incorrect compiler standard (C++ version mismatch)

---

### 4. Runtime crash in extension module
Typical symptoms:
- segmentation fault
- crash during function call into C++

Likely causes:
- invalid memory access in C++
- STL misuse across Python boundary
- incorrect object lifetime handling

---

# Step 2: Minimal Fix Strategy

Once categorized, apply the **smallest likely fix first**:

## A. Environment mismatch
- Ensure Python interpreter matches build environment
- Reinstall dependencies in active environment:
  - `pip install pybind11`

---

## B. Include / build configuration
- Ensure pybind11 headers are available to compiler
- Verify build system includes pybind11 include path
- Confirm C++ standard is C++17 or higher

---

## C. Binding corrections
- Ensure all exposed functions/classes are registered in `PYBIND11_MODULE`
- Match constructor signatures exactly between C++ and Python usage
- Use `py::arg(...)` for named parameters where needed

---

## D. Rebuild consistency
- Clean previous build artifacts before recompiling
- Rebuild extension module after any binding change

---

# Step 3: Validation

After applying a fix:

- Rebuild extension module
- Re-import in Python
- Confirm:
  - module imports successfully
  - expected methods are visible
  - constructor calls succeed

---

# Key Principles

- Prefer diagnosing the **most likely root cause first**
- Avoid changing multiple subsystems at once
- Keep fixes minimal and reversible
- Treat Python ↔ C++ boundary issues as either:
  - build-time
  - binding-time
  - runtime-memory

---

# Out of scope

This skill does **not** cover:

- Full CMake or setuptools tutorials
- IDE-specific setup instructions
- Operating system installation guides
- General Git or repository configuration
- Deep optimization of C++ performance code

---

# Example resolution pattern

**Input symptom:**
`ImportError: undefined symbol in pybind11 module`

**Output:**
1. Likely cause: ABI or missing symbol in compiled extension
2. Check: correct module rebuilt after binding changes
3. Fix: clean build + recompile extension with updated bindings
