/// PyO3 Bridge Template for Tauri-Python IPC
///
/// This template provides a complete example of building a Tauri command that invokes
/// Python functions through PyO3. Customize this template for your specific use case.
///
/// Key sections:
/// 1. Python Module Initialization - Set up Python interpreter on app startup
/// 2. Tauri Commands - Bridge commands that call Python functions
/// 3. Type Conversions - Convert between Rust/JSON and Python types
/// 4. Error Handling - Proper error management and logging

use pyo3::prelude::*;
use pyo3::types::{PyModule, PyList, PyDict};
use serde::{Deserialize, Serialize};
use std::sync::Mutex;

/// Cached Python module reference
///
/// This prevents reimporting the module on every command invocation,
/// improving performance significantly.
pub struct PythonBackend {
    module: Py<PyModule>,
}

impl PythonBackend {
    /// Initialize the Python backend at app startup
    pub fn new(module_name: &str) -> PyResult<Self> {
        Python::with_gil(|py| {
            let module = PyModule::import_bound(py, module_name)?;
            Ok(PythonBackend {
                module: module.into(),
            })
        })
    }

    /// Call a Python function and return a JSON-serializable result
    pub fn call_function(&self, func_name: &str, args: Vec<String>) -> PyResult<String> {
        Python::with_gil(|py| {
            let module = self.module.bind(py);

            // Get the function from the module
            let func = module
                .getattr(func_name)
                .map_err(|e| {
                    PyErr::new::<pyo3::exceptions::PyAttributeError, _>(
                        format!("Function not found: {}", func_name),
                    )
                })?;

            // Call the function with arguments
            let result = func
                .call1((args,))
                .map_err(|e| {
                    eprintln!("Python function error:");
                    e.print(py);
                    e
                })?;

            // Convert result to JSON string
            let json_str: String = result.extract()?;
            Ok(json_str)
        })
    }

    /// Call a Python function with type-safe conversion
    pub fn call_typed<T: serde::de::DeserializeOwned>(
        &self,
        func_name: &str,
        args: Vec<String>,
    ) -> PyResult<T> {
        Python::with_gil(|py| {
            let module = self.module.bind(py);
            let func = module.getattr(func_name)?;
            let result = func.call1((args,))?;

            // Extract result and convert to JSON, then to type T
            let json_str: String = result.extract()?;
            serde_json::from_str(&json_str).map_err(|e| {
                PyErr::new::<pyo3::exceptions::PyTypeError, _>(
                    format!("JSON deserialization failed: {}", e),
                )
            })
        })
    }
}

/// Shared Python backend for use across Tauri commands
pub struct AppState {
    backend: Mutex<Option<PythonBackend>>,
}

impl AppState {
    pub fn new() -> Self {
        AppState {
            backend: Mutex::new(None),
        }
    }

    pub fn initialize(&self, module_name: &str) -> PyResult<()> {
        let backend = PythonBackend::new(module_name)?;
        *self.backend.lock().unwrap() = Some(backend);
        Ok(())
    }

    pub fn backend(&self) -> Option<std::sync::MutexGuard<Option<PythonBackend>>> {
        self.backend.lock().ok()
    }
}

// ============================================================================
// EXAMPLE: Data Processing Command
// ============================================================================

#[derive(Serialize, Deserialize)]
pub struct ProcessDataRequest {
    pub input: Vec<f64>,
    pub threshold: f64,
}

#[derive(Serialize, Deserialize)]
pub struct ProcessDataResponse {
    pub result: Vec<f64>,
    pub count: usize,
}

/// Call Python data processing function
///
/// Sends data to Python, which processes it, and returns structured result.
#[tauri::command]
pub fn process_data(
    request: ProcessDataRequest,
    state: tauri::State<AppState>,
) -> Result<ProcessDataResponse, String> {
    let backend_lock = state
        .backend()
        .ok_or("Backend not initialized".to_string())?;

    let backend = backend_lock
        .as_ref()
        .ok_or("Backend not initialized".to_string())?;

    // Prepare JSON payload
    let payload = serde_json::json!({
        "input": request.input,
        "threshold": request.threshold
    });

    // Call Python function
    match backend.call_function("process_data", vec![payload.to_string()]) {
        Ok(result_json) => {
            match serde_json::from_str::<ProcessDataResponse>(&result_json) {
                Ok(response) => Ok(response),
                Err(e) => Err(format!("Failed to parse response: {}", e)),
            }
        }
        Err(e) => Err(format!("Python error: {}", e)),
    }
}

// ============================================================================
// EXAMPLE: ML Model Inference Command
// ============================================================================

#[derive(Serialize, Deserialize)]
pub struct InferenceInput {
    pub model: String,
    pub features: Vec<f64>,
}

#[derive(Serialize, Deserialize)]
pub struct InferenceOutput {
    pub prediction: f64,
    pub confidence: f64,
}

/// Call Python ML inference function
///
/// Loads model and runs inference on provided features.
#[tauri::command]
pub fn run_inference(
    input: InferenceInput,
    state: tauri::State<AppState>,
) -> Result<InferenceOutput, String> {
    let backend_lock = state
        .backend()
        .ok_or("Backend not initialized".to_string())?;

    let backend = backend_lock
        .as_ref()
        .ok_or("Backend not initialized".to_string())?;

    // Prepare arguments
    let payload = serde_json::json!({
        "model": input.model,
        "features": input.features
    });

    // Call Python function with type-safe conversion
    match backend.call_typed::<InferenceOutput>("run_inference", vec![payload.to_string()]) {
        Ok(output) => Ok(output),
        Err(e) => Err(format!("Inference failed: {}", e)),
    }
}

// ============================================================================
// EXAMPLE: Async Python Function Call
// ============================================================================

#[cfg(feature = "async")]
use pyo3_asyncio::tokio::into_future_bound;

#[cfg(feature = "async")]
#[tauri::command]
pub async fn async_operation(
    input: String,
    state: tauri::State<'_, AppState>,
) -> Result<String, String> {
    let backend_lock = state
        .backend()
        .ok_or("Backend not initialized".to_string())?;

    let backend = backend_lock
        .as_ref()
        .ok_or("Backend not initialized".to_string())?;

    // Create async future
    let future = Python::with_gil(|py| {
        let module = backend.module.bind(py);

        let coro = module
            .getattr("async_operation")
            .map_err(|e| format!("Function not found: {}", e))?
            .call1((input,))
            .map_err(|e| format!("Call failed: {}", e))?;

        into_future_bound(coro.bind(py))
            .map_err(|e| format!("Future conversion failed: {}", e))
    })?;

    // Await the async operation
    future.await.map_err(|e| format!("Async execution failed: {}", e))
}

// ============================================================================
// EXAMPLE: Streaming Results
// ============================================================================

#[derive(Serialize)]
pub struct StreamEvent {
    pub id: usize,
    pub data: String,
    pub done: bool,
}

/// Stream results from Python function
///
/// Calls Python function and returns results as a stream of events.
#[tauri::command]
pub fn stream_results(
    request: serde_json::Value,
    state: tauri::State<AppState>,
) -> Result<Vec<StreamEvent>, String> {
    let backend_lock = state
        .backend()
        .ok_or("Backend not initialized".to_string())?;

    let backend = backend_lock
        .as_ref()
        .ok_or("Backend not initialized".to_string())?;

    Python::with_gil(|py| {
        let module = backend.module.bind(py);

        // Get the generator function
        let gen = module
            .getattr("stream_data")
            .map_err(|e| format!("Generator not found: {}", e))?
            .call1((request.to_string(),))
            .map_err(|e| format!("Call failed: {}", e))?;

        // Iterate over generator results
        let mut events = Vec::new();
        let mut id = 0;

        loop {
            match gen.call_method0("__next__") {
                Ok(item) => {
                    let data: String = item.extract().unwrap_or_default();
                    events.push(StreamEvent {
                        id,
                        data,
                        done: false,
                    });
                    id += 1;
                }
                Err(_) => {
                    // Iterator exhausted
                    if let Some(last) = events.last_mut() {
                        last.done = true;
                    }
                    break;
                }
            }
        }

        Ok(events)
    })
}

// ============================================================================
// EXAMPLE: Tauri App Builder with Python Backend
// ============================================================================

/// Initialize Tauri app with Python backend
///
/// Call this in your main.rs:
/// ```
/// fn main() {
///     tauri::Builder::default()
///         .manage(AppState::new())
///         .setup(|app| {
///             let app_state: tauri::State<AppState> = app.state();
///
///             // Initialize Python backend
///             if let Err(e) = app_state.initialize("backend") {
///                 eprintln!("Failed to initialize Python: {}", e);
///                 return Err(Box::new(e));
///             }
///
///             Ok(())
///         })
///         .invoke_handler(tauri::generate_handler![
///             process_data,
///             run_inference,
///             stream_results,
///         ])
///         .run(tauri::generate_context!())
///         .expect("error while running tauri application");
/// }
/// ```

// ============================================================================
// EXAMPLE: Error Handling Utilities
// ============================================================================

pub struct PythonError {
    pub message: String,
    pub error_type: String,
}

impl From<PyErr> for PythonError {
    fn from(err: PyErr) -> Self {
        Python::with_gil(|py| {
            let error_type = err.get_type_bound(py).to_string();
            PythonError {
                message: err.to_string(),
                error_type,
            }
        })
    }
}

impl From<PythonError> for String {
    fn from(err: PythonError) -> Self {
        format!("{}: {}", err.error_type, err.message)
    }
}

// ============================================================================
// EXAMPLE: Type-Safe Python Function Wrappers
// ============================================================================

impl PythonBackend {
    /// Example: Type-safe wrapper for a specific Python function
    pub fn analyze_image(&self, path: &str) -> PyResult<(Vec<String>, Vec<f64>)> {
        Python::with_gil(|py| {
            let module = self.module.bind(py);

            let result = module
                .getattr("analyze_image")?
                .call1((path,))?;

            // Extract as tuple
            let (labels, scores) = result.extract::<(Vec<String>, Vec<f64>)>()?;
            Ok((labels, scores))
        })
    }

    /// Example: Type-safe wrapper with error recovery
    pub fn preprocess_data(&self, data: Vec<f64>) -> PyResult<Vec<f64>> {
        Python::with_gil(|py| {
            let module = self.module.bind(py);

            // Create Python list
            let py_list = PyList::new_bound(py, &data);

            // Call preprocessing function
            let result = module
                .getattr("preprocess")?
                .call1((py_list,))?;

            // Extract result
            result.extract()
        })
    }
}

// ============================================================================
// EXAMPLE: Python Module Definition
// ============================================================================

/// Example Python module (backend.py) that works with this template:
///
/// ```python
/// import json
/// from typing import List, Tuple
///
/// def process_data(payload_json: str) -> str:
///     """Process data request and return JSON result."""
///     payload = json.loads(payload_json)
///     input_data = payload["input"]
///     threshold = payload["threshold"]
///
///     # Process the data
///     result = [x for x in input_data if x > threshold]
///
///     # Return as JSON
///     response = {
///         "result": result,
///         "count": len(result)
///     }
///     return json.dumps(response)
///
/// def run_inference(payload_json: str) -> str:
///     """Run ML model inference."""
///     payload = json.loads(payload_json)
///     model_name = payload["model"]
///     features = payload["features"]
///
///     # Load model and run inference
///     prediction = sum(features) / len(features)
///     confidence = 0.95
///
///     response = {
///         "prediction": prediction,
///         "confidence": confidence
///     }
///     return json.dumps(response)
///
/// def analyze_image(path: str) -> Tuple[List[str], List[float]]:
///     """Analyze image and return labels and scores."""
///     # Image processing code here
///     labels = ["cat", "dog", "bird"]
///     scores = [0.9, 0.05, 0.05]
///     return labels, scores
///
/// def preprocess(data: List[float]) -> List[float]:
///     """Preprocess data."""
///     return [x / 255.0 for x in data]
/// ```

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_python_backend_creation() {
        let result = PythonBackend::new("sys");
        assert!(result.is_ok());
    }

    #[test]
    fn test_app_state() {
        let state = AppState::new();
        let result = state.initialize("sys");
        assert!(result.is_ok());
    }
}
