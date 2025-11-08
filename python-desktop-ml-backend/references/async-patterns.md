# Async/Await Patterns for ML Inference

## Overview

Building responsive ML backend services requires non-blocking I/O patterns. This guide covers asyncio patterns specifically for managing inference pipelines, integrating with synchronous ML libraries, and handling concurrent predictions without blocking the main thread or UI.

## 1. Asyncio Fundamentals for ML Backends

### Basic Event Loop and Coroutines

```python
import asyncio
from typing import Awaitable

async def load_model_async(model_path: str) -> None:
    """Coroutine: Model loading with async I/O.

    The async def syntax creates a coroutine that can be awaited.
    """
    print(f"Loading model from {model_path}...")
    await asyncio.sleep(2)  # Simulate I/O delay
    print("Model loaded")

async def main():
    """Main coroutine orchestrating async operations."""
    # Create and run the event loop
    await load_model_async("./models/model.pth")

# Run the async main function
if __name__ == "__main__":
    asyncio.run(main())
```

### Event Loop Management

```python
import asyncio
from contextvars import ContextVar

# Store request context (e.g., user ID, request ID)
request_context: ContextVar[str] = ContextVar('request_id')

async def inference_with_context(features: list[float]) -> float:
    """Inference operation with context tracking."""
    request_id = request_context.get("unknown")
    print(f"Processing request {request_id}")
    await asyncio.sleep(0.1)
    return sum(features) / len(features)

async def process_batch(requests: list[tuple[str, list[float]]]):
    """Process multiple requests with context isolation."""
    tasks = []

    for request_id, features in requests:
        # Create task with context
        ctx = request_context.set(request_id)
        task = asyncio.create_task(inference_with_context(features))
        tasks.append(task)

    # Gather all results
    results = await asyncio.gather(*tasks)
    return results
```

## 2. TaskGroup: Structured Concurrency (PEP 668)

TaskGroup provides clean, structured concurrency for related operations:

```python
import asyncio
from asyncio import TaskGroup

class BatchInference:
    """Inference manager using TaskGroup for structured concurrency."""

    def __init__(self, num_workers: int = 4):
        self.num_workers = num_workers

    async def predict_single(self, model_id: str, features: list[float]) -> float:
        """Single prediction operation (simulate async ML library call)."""
        await asyncio.sleep(0.01)  # Simulate inference latency
        return sum(features) / len(features)

    async def process_batch_with_taskgroup(self,
                                          batch: dict[str, list[float]]) -> dict[str, float]:
        """Process batch using TaskGroup.

        All predictions run concurrently, but failures are collected together.
        """
        results = {}

        try:
            async with TaskGroup() as tg:
                # Create tasks for each prediction
                for model_id, features in batch.items():
                    task = tg.create_task(
                        self.predict_single(model_id, features)
                    )
                    # Store mapping for result collection
                    task.set_name(model_id)

                # TaskGroup waits for all tasks; exception handling is centralized
        except ExceptionGroup as eg:
            # Handle multiple exceptions from different tasks
            print(f"Some predictions failed: {eg.exceptions}")
            return {}

        # Collect results from completed tasks
        for task in asyncio.all_tasks():
            if task.get_name() in batch:
                try:
                    results[task.get_name()] = task.result()
                except Exception:
                    pass

        return results

# Usage
async def demo_taskgroup():
    inference = BatchInference()
    batch = {
        "model_1": [1.0, 2.0, 3.0],
        "model_2": [4.0, 5.0, 6.0],
        "model_3": [7.0, 8.0, 9.0],
    }
    results = await inference.process_batch_with_taskgroup(batch)
    print(f"Results: {results}")
```

## 3. Integrating Sync ML Libraries with Async

### ThreadPoolExecutor Wrapper

```python
import asyncio
from concurrent.futures import ThreadPoolExecutor
from functools import partial
import numpy as np

class AsyncMLAdapter:
    """Wrapper making synchronous ML libraries work with async code."""

    def __init__(self, max_workers: int = 4):
        self.executor = ThreadPoolExecutor(max_workers=max_workers)
        self.loop = asyncio.get_event_loop()

    async def predict_async(self,
                            model,
                            features: np.ndarray) -> np.ndarray:
        """Run synchronous predict() in thread pool without blocking.

        The event loop delegates to executor thread, freeing the main thread
        to handle other async operations.
        """
        # Schedule sync function in thread pool
        prediction = await self.loop.run_in_executor(
            self.executor,
            model.predict,
            features
        )
        return prediction

    async def batch_predict_async(self,
                                 model,
                                 features_list: list[np.ndarray]) -> list[np.ndarray]:
        """Batch predictions using async concurrency."""
        tasks = [
            self.predict_async(model, features)
            for features in features_list
        ]
        return await asyncio.gather(*tasks)

    def __del__(self):
        self.executor.shutdown(wait=True)

# Usage with real ML library
async def demo_async_ml():
    from sklearn.ensemble import RandomForestClassifier

    # Train a simple model
    X = np.random.randn(100, 10)
    y = (X[:, 0] > 0).astype(int)
    model = RandomForestClassifier().fit(X, y)

    # Use async adapter
    adapter = AsyncMLAdapter(max_workers=2)
    batch = [np.random.randn(10) for _ in range(5)]
    predictions = await adapter.batch_predict_async(model, batch)
    print(f"Predictions shape: {[p.shape for p in predictions]}")

# asyncio.run(demo_async_ml())
```

### Custom Async Wrapper Class

```python
import asyncio
from typing import Protocol, TypeVar, Generic

T = TypeVar('T')
InputType = TypeVar('InputType')
OutputType = TypeVar('OutputType')

class SyncMLModel(Protocol):
    """Protocol for synchronous ML models."""

    def predict(self, data: InputType) -> OutputType:
        """Synchronous prediction method."""
        ...

class AsyncMLModel(Generic[InputType, OutputType]):
    """Async wrapper for synchronous ML models."""

    def __init__(self, model: SyncMLModel, max_workers: int = 4):
        self.model = model
        self.executor = asyncio.Semaphore(max_workers)

    async def predict(self, data: InputType) -> OutputType:
        """Async predict with concurrency control."""
        async with self.executor:  # Limit concurrent predictions
            loop = asyncio.get_event_loop()
            return await loop.run_in_executor(
                None,
                self.model.predict,
                data
            )

    async def predict_batch(self,
                           batch: list[InputType]) -> list[OutputType]:
        """Batch prediction with bounded concurrency."""
        tasks = [self.predict(item) for item in batch]
        return await asyncio.gather(*tasks)
```

## 4. Async Generators for Streaming Predictions

```python
import asyncio
from typing import AsyncGenerator

class StreamingInference:
    """Real-time streaming of ML predictions."""

    async def stream_predictions(self,
                                data_source,
                                batch_size: int = 32) -> AsyncGenerator[dict, None]:
        """Stream predictions from continuous data source.

        Perfect for real-time dashboards or progressive rendering.
        """
        buffer = []

        async for item in data_source:  # Assume data_source is an async iterator
            buffer.append(item)

            if len(buffer) >= batch_size:
                # Process batch
                predictions = await self.batch_predict(buffer)

                # Yield results one by one
                for pred in predictions:
                    yield {"timestamp": asyncio.get_event_loop().time(),
                           "prediction": pred}

                buffer = []

            # Yield partial results periodically
            await asyncio.sleep(0.1)

        # Yield remaining items
        if buffer:
            predictions = await self.batch_predict(buffer)
            for pred in predictions:
                yield {"timestamp": asyncio.get_event_loop().time(),
                       "prediction": pred}

    async def batch_predict(self, batch: list) -> list:
        """Batch prediction (implementation details omitted)."""
        await asyncio.sleep(0.01)
        return [sum(item) if isinstance(item, list) else item for item in batch]

# Usage
async def stream_demo():
    async def data_source():
        """Simulated continuous data source."""
        for i in range(100):
            await asyncio.sleep(0.01)
            yield [float(i), float(i + 1), float(i + 2)]

    streamer = StreamingInference()

    async for result in streamer.stream_predictions(data_source(), batch_size=10):
        print(f"Streamed: {result['prediction']}")
```

## 5. Cancellation and Timeout Handling

### Proper Cancellation

```python
import asyncio

async def long_running_inference(duration: float) -> str:
    """Inference that can be cancelled."""
    try:
        await asyncio.sleep(duration)
        return "inference complete"
    except asyncio.CancelledError:
        print("Inference cancelled, cleaning up...")
        # Cleanup code here (close connections, save state, etc.)
        raise  # Re-raise to propagate cancellation

async def demo_cancellation():
    """Demonstrate proper task cancellation."""
    # Start long-running inference
    task = asyncio.create_task(long_running_inference(10.0))

    # Cancel after 2 seconds
    await asyncio.sleep(2)
    task.cancel()

    try:
        await task
    except asyncio.CancelledError:
        print("Task was cancelled")
```

### Timeout Patterns

```python
import asyncio

async def inference_with_timeout(model_id: str, timeout: float = 5.0) -> dict:
    """Inference with strict timeout."""
    try:
        result = await asyncio.wait_for(
            long_running_inference(10.0),
            timeout=timeout
        )
        return {"status": "success", "result": result}
    except asyncio.TimeoutError:
        return {"status": "timeout", "model_id": model_id, "timeout": timeout}

async def demo_timeout():
    """Multiple inferences with individual timeouts."""
    tasks = [
        inference_with_timeout("model_1", timeout=2.0),
        inference_with_timeout("model_2", timeout=5.0),
        inference_with_timeout("model_3", timeout=1.0),
    ]

    results = await asyncio.gather(*tasks, return_exceptions=True)
    for result in results:
        print(result)
```

## 6. Async Context Managers for Resource Management

```python
import asyncio
from contextlib import asynccontextmanager
from typing import AsyncGenerator

class ModelPool:
    """Connection pool for ML model inference with async context manager."""

    def __init__(self, pool_size: int = 4):
        self.pool_size = pool_size
        self.available = asyncio.Semaphore(pool_size)
        self.models = []

    async def initialize(self):
        """Initialize model pool."""
        # Load models asynchronously
        for i in range(self.pool_size):
            model = await self.load_model(i)
            self.models.append(model)

    async def load_model(self, model_id: int):
        """Simulate async model loading."""
        await asyncio.sleep(0.1)
        return f"model_{model_id}"

    @asynccontextmanager
    async def acquire_model(self) -> AsyncGenerator[str, None]:
        """Acquire model from pool with automatic release."""
        async with self.available:  # Wait for available model
            model = self.models.pop()
            try:
                yield model
            finally:
                self.models.append(model)  # Return to pool

async def demo_model_pool():
    """Demonstrate model pool with async context manager."""
    pool = ModelPool(pool_size=2)
    await pool.initialize()

    async def worker(worker_id: int):
        """Worker using model pool."""
        async with pool.acquire_model() as model:
            print(f"Worker {worker_id} using {model}")
            await asyncio.sleep(0.5)
            print(f"Worker {worker_id} releasing {model}")

    # 4 workers, 2 models -> some workers wait
    await asyncio.gather(
        worker(1), worker(2), worker(3), worker(4)
    )

# asyncio.run(demo_model_pool())
```

## 7. Error Handling in Async Code

### Exception Groups (PEP 654)

```python
import asyncio
from asyncio import TaskGroup

async def predict_with_error_handling():
    """Handle exceptions from multiple concurrent predictions."""

    async def might_fail(task_id: int) -> int:
        await asyncio.sleep(0.1 * task_id)
        if task_id % 2 == 0:
            raise ValueError(f"Prediction {task_id} failed")
        return task_id

    results = []

    try:
        async with TaskGroup() as tg:
            tasks = [
                tg.create_task(might_fail(i))
                for i in range(5)
            ]
    except ExceptionGroup as eg:
        print(f"Caught {len(eg.exceptions)} exceptions:")
        for exc in eg.exceptions:
            print(f"  - {exc}")

        # Collect partial results
        for task in tasks:
            try:
                results.append(task.result())
            except:
                results.append(None)

    return results
```

### Graceful Degradation

```python
import asyncio

async def predict_with_fallback(primary_model: str,
                               fallback_model: str,
                               features: list) -> float:
    """Try primary model, fall back to secondary on failure."""
    try:
        result = await asyncio.wait_for(
            primary_inference(primary_model, features),
            timeout=2.0
        )
        return result
    except (asyncio.TimeoutError, Exception) as e:
        print(f"Primary model failed ({e}), using fallback")
        return await fallback_inference(fallback_model, features)

async def primary_inference(model: str, features: list) -> float:
    await asyncio.sleep(3)  # Timeout
    return sum(features)

async def fallback_inference(model: str, features: list) -> float:
    await asyncio.sleep(0.1)
    return sum(features) / len(features)
```

## 8. Integration with Tauri Desktop Apps

```python
import asyncio
import json

class TauriMLBackend:
    """Async ML backend integrated with Tauri desktop application."""

    def __init__(self):
        self.model = None
        self.inference_queue = asyncio.Queue()
        self.results_cache = {}

    async def initialize(self):
        """Initialize ML backend on app startup."""
        print("Loading models...")
        await asyncio.sleep(1)  # Simulate model loading
        self.model = "initialized_model"
        print("Models loaded")

    async def handle_inference_request(self,
                                      request_id: str,
                                      features: list[float]) -> dict:
        """Handle single inference request from Tauri frontend.

        Returns quickly, results cached for frontend polling.
        """
        result = await asyncio.to_thread(
            self._sync_predict,
            features
        )

        self.results_cache[request_id] = {
            "status": "complete",
            "result": result
        }

        return {"status": "queued", "request_id": request_id}

    def _sync_predict(self, features: list[float]) -> float:
        """Synchronous prediction (blocking)."""
        return sum(features) / len(features)

    async def run_backend_loop(self):
        """Main backend event loop for Tauri."""
        await self.initialize()

        # Process inference requests continuously
        while True:
            await asyncio.sleep(0.1)  # Check for requests
            # In real implementation, integrate with Tauri IPC

# Usage with Tauri
async def main():
    backend = TauriMLBackend()
    # Start background task
    asyncio.create_task(backend.run_backend_loop())
    # API endpoints would call methods on backend instance
```

## 9. Best Practices Summary

1. **Use `asyncio.run()` for app entry point** - Simplifies event loop management
2. **Prefer `asyncio.gather()` for independent tasks** - Cleaner than manual task creation
3. **Use TaskGroup for structured concurrency** - Automatic exception grouping
4. **Always use timeouts on external operations** - Prevent hanging
5. **Implement graceful degradation** - Fallback strategies for failures
6. **Profile async overhead** - Not all I/O benefits from async
7. **Use semaphores for resource pooling** - Prevent overwhelming downstream services
8. **Monitor event loop responsiveness** - Track slow callbacks
9. **Test cancellation paths** - Ensure proper cleanup
10. **Document async dependencies** - Make requirements clear in docstrings

## 10. Performance Monitoring

```python
import asyncio
import time
from collections import defaultdict

class AsyncProfiler:
    """Profile async operations for performance analysis."""

    def __init__(self):
        self.metrics = defaultdict(list)

    async def timed_operation(self, name: str, coro):
        """Execute coroutine and record timing."""
        start = time.perf_counter()
        try:
            result = await coro
            elapsed = time.perf_counter() - start
            self.metrics[name].append({"elapsed": elapsed, "status": "success"})
            return result
        except Exception as e:
            elapsed = time.perf_counter() - start
            self.metrics[name].append({"elapsed": elapsed, "status": "error", "error": str(e)})
            raise

    def report(self):
        """Generate performance report."""
        for operation, timings in self.metrics.items():
            times = [t["elapsed"] for t in timings if t["status"] == "success"]
            if times:
                avg = sum(times) / len(times)
                print(f"{operation}: avg={avg:.3f}s, count={len(times)}")
```

## Conclusion

Async/await patterns are essential for responsive ML backends. By properly integrating synchronous ML libraries with async code, handling cancellation, and managing resources, you can build responsive desktop applications with no UI blocking.
