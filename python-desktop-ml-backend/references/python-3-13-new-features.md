# Python 3.13 New Features for ML Backends

## Overview

Python 3.13 introduces transformative features for building high-performance ML backends, including adaptive JIT compilation, free-threaded mode (PEP 703), and significant optimizations to the runtime. This guide covers practical application of these features in desktop ML applications.

## 1. Adaptive JIT Compilation

### What It Is

Python 3.13 includes an adaptive bytecode interpreter that profiles hot code paths and compiles frequently executed code to optimized machine code. This provides performance improvements of 10-60% on CPU-bound workloads without requiring manual optimization.

### Enabling JIT Compilation

```bash
# Enable JIT with optimization level 2
PYTHONOPTIMIZE=2 python your_script.py

# Set the JIT threshold (default: 100 bytecode executions)
PYTHONJITCOUNTER=100 python your_script.py

# For faster JIT decisions (development)
PYTHONJITCOUNTER=10 python your_script.py

# For conservative JIT (production, larger threshold)
PYTHONJITCOUNTER=1000 python your_script.py
```

### Practical ML Example: Model Inference Loop

```python
import numpy as np
from typing import Protocol

class Predictor(Protocol):
    def predict(self, features: np.ndarray) -> np.ndarray: ...

def batch_inference(model: Predictor,
                   features: list[np.ndarray],
                   batch_size: int = 32) -> list[np.ndarray]:
    """Hot function that JIT will optimize.

    The inner loop executes frequently and will be JIT compiled.
    """
    results = []

    # This loop becomes a JIT compilation candidate
    for i in range(0, len(features), batch_size):
        batch = np.stack(features[i:i + batch_size])
        prediction = model.predict(batch)
        results.append(prediction)

    return results
```

### JIT Compilation Behavior

- **Counting**: After 100 bytecode executions (configurable), the function is compiled
- **Warm-up**: First 100 executions run in interpreter mode
- **Compilation**: Next request triggers compilation (slight latency spike)
- **Execution**: Subsequent calls use optimized machine code
- **Profiling**: The JIT gathers execution statistics to make optimization decisions

### Monitoring JIT Activity

```python
import sys

# Check if JIT is enabled
print(f"JIT enabled: {sys.monitoring is not None}")

# Use environment variables to track JIT compilation
import os
os.environ['PYTHONOPTIMIZE'] = '2'

# Monitor with py-spy
# py-spy record -o profile.svg -- python your_script.py
```

### When JIT Provides Benefits

- **Tight loops** in data preprocessing (10-60% improvement)
- **Numeric computations** on vectors/matrices
- **Frequently called functions** in inference pipelines
- **Algorithm optimization** without code changes

### When JIT Has Limited Impact

- **I/O-bound code** (file/network operations)
- **Async/await code** (JIT still helps, but benefits are lower)
- **Dynamic code paths** (function calls, polymorphism)
- **Single execution functions** (too fast to compile)

## 2. Free-Threaded Mode (PEP 703)

### What It Is

Free-threaded mode removes Python's Global Interpreter Lock (GIL), enabling true parallel execution of Python bytecode across multiple threads. This is critical for CPU-bound ML workloads that previously couldn't utilize multiple cores.

### Building Python with Free-Threading

```bash
# Install Python 3.13 with free-threading support
# Option 1: From source
git clone https://github.com/python/cpython.git
cd cpython
git checkout 3.13
./configure --disable-gil
make
sudo make install

# Option 2: Using PyEnv
pyenv install --with-freethreading 3.13.0

# Option 3: Check if prebuilt binary is available
python3.13 --version  # Verify installation
python3.13 -c "import sys; print(sys.flags.nogil)"  # True if no-GIL
```

### Running with Free-Threaded Mode

```bash
# Run Python 3.13 built with --disable-gil
python3.13t your_script.py  # 't' suffix indicates free-threaded build

# Or use the flag
python3.13 --disable-gil your_script.py

# Verify free-threading is active
python3.13 -c "import sys; print('Free-threaded' if not hasattr(sys, 'flags') or sys.flags.nogil else 'GIL enabled')"
```

### Parallel ML Inference with Free-Threading

```python
import threading
from concurrent.futures import ThreadPoolExecutor
import numpy as np
from typing import Callable

class ParallelInference:
    """CPU-bound inference using thread-level parallelism.

    With free-threaded Python 3.13, each thread executes in parallel
    without GIL contention. Perfect for batch inference.
    """

    def __init__(self, predict_fn: Callable, num_workers: int = 4):
        self.predict_fn = predict_fn
        self.num_workers = num_workers
        self.executor = ThreadPoolExecutor(max_workers=num_workers)

    def parallel_batch_predict(self,
                              samples: list[np.ndarray]) -> list[np.ndarray]:
        """Distribute inference across threads.

        In free-threaded Python 3.13, true parallelism is achieved.
        """
        # Submit all predictions to thread pool
        futures = [
            self.executor.submit(self.predict_fn, sample)
            for sample in samples
        ]

        # Collect results in order
        return [future.result() for future in futures]

    def __del__(self):
        self.executor.shutdown(wait=True)

# Usage
def model_predict(features: np.ndarray) -> np.ndarray:
    # Simulate CPU-intensive model inference
    return np.dot(features, np.random.randn(features.shape[-1], 10))

if __name__ == "__main__":
    inference = ParallelInference(model_predict, num_workers=4)
    samples = [np.random.randn(784) for _ in range(100)]
    results = inference.parallel_batch_predict(samples)
    print(f"Processed {len(results)} samples in parallel")
```

### Per-Interpreter GIL Isolation

Even in free-threaded mode, you can isolate Python interpreters for independent GIL domains:

```python
import _interpreters
from typing import Any

class PerInterpreterInference:
    """Initialize separate Python interpreters for completely isolated execution.

    Each interpreter has its own GIL, enabling independent inference sessions.
    Useful for multi-model ensemble systems.
    """

    def __init__(self, num_interpreters: int = 4):
        self.interpreters = [
            _interpreters.create() for _ in range(num_interpreters)
        ]
        self.current = 0

    def submit_inference(self, code: str) -> Any:
        """Submit inference code to next available interpreter."""
        interp = self.interpreters[self.current % len(self.interpreters)]
        self.current += 1

        # Run code in isolated interpreter
        _interpreters.run_string(interp, code)
```

### Memory Implications of Free-Threading

- **Higher memory overhead**: Each thread maintains its own reference counts (no shared object tracking)
- **Trade-off**: Accept 10-20% higher memory usage for true parallelism
- **Monitor with**: `psutil.Process().memory_info()`

## 3. Enhanced Type System

### PEP 673: Self Type

Use `Self` type for methods that return instances of the current class:

```python
from typing import Self

class MLModel:
    """Model class with proper Self type hints."""

    def __init__(self, name: str):
        self.name = name

    def configure(self, **kwargs) -> Self:
        """Configuration method returns instance of the same type.

        This enables proper type checking with subclasses.
        """
        for key, value in kwargs.items():
            setattr(self, key, value)
        return self

    def copy(self) -> Self:
        """Create a copy of the current model."""
        import copy
        return copy.deepcopy(self)

class AdvancedModel(MLModel):
    """Subclass properly inherits Self type hints."""

    def __init__(self, name: str, version: int):
        super().__init__(name)
        self.version = version

# Type checking works correctly with inheritance
model: AdvancedModel = AdvancedModel("gpt2", 1).configure(layers=12)
```

### Improved Type Narrowing

```python
from typing import TypeVar, Union

T = TypeVar('T', bound='Prediction')

class Prediction:
    def __init__(self, value: float, confidence: float):
        self.value = value
        self.confidence = confidence

class ClassificationPrediction(Prediction):
    def __init__(self, class_id: int, confidence: float):
        self.class_id = class_id
        super().__init__(class_id, confidence)

def process_prediction(pred: Union[Prediction, ClassificationPrediction]) -> float:
    """Type narrowing improved in Python 3.13.

    The type checker can narrow the union type through control flow.
    """
    if isinstance(pred, ClassificationPrediction):
        # Type narrowed to ClassificationPrediction
        return pred.class_id + pred.confidence
    else:
        # Type narrowed to Prediction
        return pred.value
```

## 4. Performance Optimizations

### Inlined Bytecode Operations

Frequently used operations are now inlined:

```python
# These operations are faster in Python 3.13
def fast_numeric_operations(x: list[int]) -> int:
    # List indexing is inlined
    total = x[0]

    # Attribute access is optimized
    class Config:
        threshold = 10

    # Integer operations are inlined
    result = total * 2 + 5

    return result
```

### Faster Attribute Access

```python
# Attribute lookups are optimized with inline caches
class Features:
    def __init__(self):
        self.embeddings = None
        self.metadata = None

def hot_function(features: Features) -> None:
    # These attribute accesses use optimized inline caches
    for _ in range(1000000):
        _ = features.embeddings
        _ = features.metadata
```

### Optimized List/Dict Operations

```python
# List comprehensions are faster
def optimize_comprehension(data: list[float]) -> list[float]:
    return [x * 2.0 for x in data if x > 0.5]

# Dictionary operations optimized
def optimize_dict_ops():
    d = {}
    for i in range(10000):
        d[f"key_{i}"] = i  # Faster insertion
        value = d.get(f"key_{i}", 0)  # Faster lookup
```

## 5. Migration Guide from Python 3.12

### Code Changes

1. **Type hints**: Update to use `Self` for return types of class methods
2. **Import paths**: Some internal modules reorganized (unlikely to affect applications)
3. **Deprecations**: Remove usage of deprecated features listed in 3.12 warnings

### Testing

```python
# Verify JIT compilation
import sys
PYTHONOPTIMIZE = "2"

# Test free-threaded mode
import threading
thread_count = threading.active_count()

# Run existing tests with new features
# pytest tests/
```

### Performance Verification

```python
import time
import numpy as np

def benchmark_inference(iterations: int = 1000):
    """Compare Python 3.12 vs 3.13 performance."""

    start = time.perf_counter()

    for _ in range(iterations):
        # Typical inference operation
        data = np.random.randn(100, 784)
        result = np.dot(data, np.random.randn(784, 10))

    elapsed = time.perf_counter() - start

    print(f"Time: {elapsed:.3f}s")
    print(f"Per-iteration: {elapsed/iterations*1000:.2f}ms")

    return elapsed

# Run multiple times to see JIT warmup
for i in range(3):
    benchmark_inference(1000)
    print("---")
```

## 6. Configuration Best Practices

### Environment Setup

```bash
#!/bin/bash
# Recommended Python 3.13 environment variables for ML backends

export PYTHONOPTIMIZE=2              # Enable JIT with optimization level
export PYTHONJITCOUNTER=100          # Compilation threshold
export PYTHONHASHSEED=0              # Reproducible hashing
export PYTHONDONTWRITEBYTECODE=0     # Generate .pyc files for caching
export PYTHONUNBUFFERED=1            # Unbuffered output for logs
export PYTHONWARNINGS=error::DeprecationWarning  # Treat deprecations as errors
```

### Development vs Production

```toml
# pyproject.toml configuration

[tool.pytest.ini_options]
# Development: Enable all warnings
filterwarnings = ["error"]

[build-system]
requires = ["setuptools>=65.0", "wheel"]
build-backend = "setuptools.build_meta"

[project]
requires-python = ">=3.13.0"
dependencies = [
    "numpy>=1.24",
    "scikit-learn>=1.3",
]
```

## 7. Troubleshooting

### JIT Compilation Not Working

```python
# Check if JIT is actually compiling
import sys
import os

def debug_jit_status():
    print(f"PYTHONOPTIMIZE: {os.environ.get('PYTHONOPTIMIZE', 'not set')}")
    print(f"PYTHONJITCOUNTER: {os.environ.get('PYTHONJITCOUNTER', 'not set')}")
    print(f"Python: {sys.version}")

    # Run a hot function and check compilation
    def hot_function():
        result = 0
        for i in range(1000):
            result += i * 2
        return result

    # First 100 executions: interpreter
    # After: JIT compilation
    for _ in range(500):
        hot_function()

debug_jit_status()
```

### Free-Threaded Build Not Detected

```bash
# Verify free-threading support
python3.13 -c "import sys; print('nogil' in sys.abiflags or 'free-threaded' in sys.version)"

# If False, rebuild Python 3.13 with --disable-gil
```

## Conclusion

Python 3.13's JIT compilation and free-threaded mode are game-changers for ML backends. The performance improvements require minimal code changes while providing substantial benefits for CPU-bound inference workloads.
