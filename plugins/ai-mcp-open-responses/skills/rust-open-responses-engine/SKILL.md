---
name: rust-open-responses-engine
description: |
  Build Rust backends for OpenAI Responses and Open Responses APIs. Covers HTTP server
  implementation, streaming responses, and integration with Burn and SmartCore for
  local inference capabilities.
license: Complete terms in LICENSE.txt
---

# Rust Open Responses Engine

## When to Use

Use this skill when:

- Building a high-performance Rust backend for Open Responses / OpenAI Responses API
- Implementing streaming HTTP responses with Server-Sent Events (SSE)
- Integrating local inference engines (Burn, SmartCore, candle) into a Responses API server
- Creating a production-grade Rust HTTP server for LLM orchestration
- Optimizing for low-latency, high-throughput LLM request handling

---

## Concepts

### Architecture Overview

```
┌─────────────────────────────────────────────────────────────┐
│                    Rust Open Responses Engine               │
├─────────────────────────────────────────────────────────────┤
│  HTTP Layer (Axum/Actix)                                    │
│  ├── POST /v1/responses                                     │
│  ├── POST /v1/responses (streaming)                         │
│  └── GET  /v1/models                                        │
├─────────────────────────────────────────────────────────────┤
│  Request Processing                                         │
│  ├── Validation (JSON Schema)                               │
│  ├── Provider Routing                                       │
│  └── Tool Execution                                         │
├─────────────────────────────────────────────────────────────┤
│  Inference Backends                                         │
│  ├── Burn (GPU/CPU tensors)                                 │
│  ├── SmartCore (ML algorithms)                              │
│  ├── Candle (Hugging Face models)                           │
│  └── External APIs (OpenAI, Anthropic)                      │
└─────────────────────────────────────────────────────────────┘
```

### Key Components

| Component | Crate | Purpose |
|-----------|-------|---------|
| HTTP Server | `axum` or `actix-web` | Request handling, routing |
| Streaming | `tokio-stream`, `axum::response::Sse` | SSE streaming responses |
| Serialization | `serde`, `serde_json` | JSON parsing and generation |
| Validation | `validator`, `jsonschema` | Request validation |
| Inference | `burn`, `smartcore`, `candle` | Local model execution |

---

## Instructions

### Step 1: Project Setup

```bash
cargo new open-responses-engine
cd open-responses-engine
```

Add dependencies to `Cargo.toml`:

```toml
[package]
name = "open-responses-engine"
version = "0.1.0"
edition = "2021"

[dependencies]
# HTTP Server
axum = { version = "0.7", features = ["macros"] }
tokio = { version = "1", features = ["full"] }
tower = "0.4"
tower-http = { version = "0.5", features = ["cors", "trace"] }

# Serialization
serde = { version = "1", features = ["derive"] }
serde_json = "1"

# Streaming
tokio-stream = "0.1"
futures = "0.3"

# Validation
validator = { version = "0.18", features = ["derive"] }

# Inference (optional, choose based on needs)
burn = { version = "0.14", features = ["wgpu"] }
smartcore = "0.3"

# Utilities
uuid = { version = "1", features = ["v4"] }
chrono = { version = "0.4", features = ["serde"] }
tracing = "0.1"
tracing-subscriber = "0.3"
anyhow = "1"
thiserror = "1"
```

### Step 2: Define Request/Response Types

```rust
// src/types.rs
use serde::{Deserialize, Serialize};
use validator::Validate;

#[derive(Debug, Deserialize, Validate)]
pub struct CreateResponseRequest {
    pub model: String,
    pub input: Input,
    #[serde(default)]
    pub instructions: Option<String>,
    #[serde(default)]
    pub tools: Vec<ToolDefinition>,
    #[serde(default)]
    pub stream: bool,
    #[serde(default)]
    pub metadata: Option<serde_json::Value>,
}

#[derive(Debug, Deserialize)]
#[serde(untagged)]
pub enum Input {
    Text(String),
    Messages(Vec<Message>),
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Message {
    pub role: String,
    pub content: Vec<ContentBlock>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum ContentBlock {
    #[serde(rename = "text")]
    Text { text: String },
    #[serde(rename = "tool_use")]
    ToolUse { id: String, name: String, input: serde_json::Value },
    #[serde(rename = "tool_result")]
    ToolResult { tool_use_id: String, content: String },
}

#[derive(Debug, Serialize)]
pub struct ResponseOutput {
    pub id: String,
    pub object: String,
    pub created_at: i64,
    pub status: String,
    pub output: Vec<OutputItem>,
    pub usage: Usage,
}

#[derive(Debug, Serialize)]
pub struct Usage {
    pub input_tokens: u32,
    pub output_tokens: u32,
}
```

### Step 3: Implement HTTP Server

```rust
// src/main.rs
use axum::{
    extract::State,
    http::StatusCode,
    response::{sse::Event, Sse},
    routing::{get, post},
    Json, Router,
};
use std::sync::Arc;
use tokio_stream::StreamExt;
use tower_http::cors::CorsLayer;

mod types;
mod inference;
mod error;

use types::*;
use inference::InferenceEngine;

#[derive(Clone)]
struct AppState {
    engine: Arc<InferenceEngine>,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::init();

    let engine = Arc::new(InferenceEngine::new()?);
    let state = AppState { engine };

    let app = Router::new()
        .route("/v1/responses", post(create_response))
        .route("/v1/models", get(list_models))
        .route("/health", get(health_check))
        .layer(CorsLayer::permissive())
        .with_state(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:8080").await?;
    tracing::info!("Server running on http://0.0.0.0:8080");
    axum::serve(listener, app).await?;

    Ok(())
}

async fn create_response(
    State(state): State<AppState>,
    Json(request): Json<CreateResponseRequest>,
) -> Result<Json<ResponseOutput>, StatusCode> {
    let response = state.engine
        .generate(&request)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    Ok(Json(response))
}

async fn list_models(
    State(state): State<AppState>,
) -> Json<serde_json::Value> {
    Json(serde_json::json!({
        "object": "list",
        "data": state.engine.available_models()
    }))
}

async fn health_check() -> &'static str {
    "ok"
}
```

### Step 4: Implement Streaming Responses

```rust
// src/streaming.rs
use axum::response::sse::{Event, Sse};
use futures::stream::Stream;
use std::convert::Infallible;
use tokio_stream::wrappers::ReceiverStream;

pub async fn create_streaming_response(
    State(state): State<AppState>,
    Json(request): Json<CreateResponseRequest>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let (tx, rx) = tokio::sync::mpsc::channel::<Result<Event, Infallible>>(100);

    tokio::spawn(async move {
        let mut stream = state.engine.generate_stream(&request).await;

        while let Some(chunk) = stream.next().await {
            let event = Event::default()
                .event("response.output_text.delta")
                .json_data(&chunk)
                .unwrap();

            if tx.send(Ok(event)).await.is_err() {
                break;
            }
        }

        // Send done event
        let done = Event::default()
            .event("response.completed")
            .data("[DONE]");
        let _ = tx.send(Ok(done)).await;
    });

    Sse::new(ReceiverStream::new(rx))
}
```

### Step 5: Integrate Inference Engine

```rust
// src/inference.rs
use crate::types::*;
use anyhow::Result;
use burn::prelude::*;

pub struct InferenceEngine {
    // Model and tokenizer state
}

impl InferenceEngine {
    pub fn new() -> Result<Self> {
        // Initialize model, load weights
        Ok(Self {})
    }

    pub async fn generate(&self, request: &CreateResponseRequest) -> Result<ResponseOutput> {
        let id = uuid::Uuid::new_v4().to_string();
        let created_at = chrono::Utc::now().timestamp();

        // Process input and generate response
        let output_text = self.run_inference(request).await?;

        Ok(ResponseOutput {
            id: format!("resp_{}", id),
            object: "response".to_string(),
            created_at,
            status: "completed".to_string(),
            output: vec![OutputItem::Message {
                role: "assistant".to_string(),
                content: vec![ContentBlock::Text { text: output_text }],
            }],
            usage: Usage {
                input_tokens: 0,  // Calculate from tokenizer
                output_tokens: 0,
            },
        })
    }

    pub fn available_models(&self) -> Vec<serde_json::Value> {
        vec![
            serde_json::json!({
                "id": "local/default",
                "object": "model",
                "created": 0,
                "owned_by": "local"
            })
        ]
    }

    async fn run_inference(&self, request: &CreateResponseRequest) -> Result<String> {
        // Actual inference logic with Burn/SmartCore
        todo!("Implement inference")
    }
}
```

### Step 6: Error Handling

```rust
// src/error.rs
use axum::{
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ApiError {
    #[error("Invalid request: {0}")]
    BadRequest(String),

    #[error("Model not found: {0}")]
    ModelNotFound(String),

    #[error("Inference error: {0}")]
    InferenceError(String),

    #[error("Internal error")]
    Internal(#[from] anyhow::Error),
}

impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        let (status, message) = match &self {
            ApiError::BadRequest(msg) => (StatusCode::BAD_REQUEST, msg.clone()),
            ApiError::ModelNotFound(msg) => (StatusCode::NOT_FOUND, msg.clone()),
            ApiError::InferenceError(msg) => (StatusCode::INTERNAL_SERVER_ERROR, msg.clone()),
            ApiError::Internal(_) => (StatusCode::INTERNAL_SERVER_ERROR, "Internal error".to_string()),
        };

        let body = serde_json::json!({
            "error": {
                "type": "api_error",
                "message": message,
            }
        });

        (status, Json(body)).into_response()
    }
}
```

### Step 7: Integrate SmartCore for ML

```rust
// src/ml.rs
use smartcore::ensemble::random_forest_classifier::RandomForestClassifier;
use smartcore::linalg::basic::matrix::DenseMatrix;

pub struct ClassificationEngine {
    model: RandomForestClassifier<f64, i32, DenseMatrix<f64>, Vec<i32>>,
}

impl ClassificationEngine {
    pub fn predict(&self, features: &[f64]) -> i32 {
        let matrix = DenseMatrix::from_2d_vec(&vec![features.to_vec()]);
        self.model.predict(&matrix).unwrap()[0]
    }
}
```

---

## Production Considerations

- **Graceful Shutdown**: Implement signal handling for clean shutdown
- **Request Timeouts**: Add tower middleware for request timeouts
- **Rate Limiting**: Use tower-governor for rate limiting
- **Metrics**: Integrate prometheus metrics via `metrics` crate
- **Tracing**: Use OpenTelemetry for distributed tracing

---

## Additional Resources

- **`scripts/`** — Build scripts, benchmark utilities, deployment helpers
- **`templates/`** — API specification snippets, Cargo.toml templates
- **`reference/`** — Rust crate documentation links, architecture notes

Use these resources to accelerate your Rust backend development.
