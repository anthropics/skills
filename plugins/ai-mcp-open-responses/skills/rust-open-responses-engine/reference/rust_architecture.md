# Rust Open Responses Engine Architecture

## Overview

A high-performance Rust backend for Open Responses API, featuring async HTTP handling, streaming SSE responses, and optional local inference via Burn or SmartCore.

---

## Architecture Diagram

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Rust Open Responses Engine                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                         HTTP Layer (Axum)                               │ │
│  │  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐                  │ │
│  │  │ POST /v1/    │  │ GET /v1/     │  │ GET /health  │                  │ │
│  │  │  responses   │  │  models      │  │              │                  │ │
│  │  └──────┬───────┘  └──────┬───────┘  └──────────────┘                  │ │
│  └─────────┼─────────────────┼────────────────────────────────────────────┘ │
│            │                 │                                               │
│            ▼                 ▼                                               │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                      Request Processing                                 │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐   │ │
│  │  │   Parsing   │─▶│ Validation  │─▶│   Routing   │─▶│ Rate Limit  │   │ │
│  │  │   (Serde)   │  │   (Valid)   │  │             │  │             │   │ │
│  │  └─────────────┘  └─────────────┘  └──────┬──────┘  └─────────────┘   │ │
│  └───────────────────────────────────────────┼────────────────────────────┘ │
│                                              │                               │
│                    ┌─────────────────────────┼─────────────────────────┐    │
│                    │                         │                         │    │
│                    ▼                         ▼                         ▼    │
│  ┌─────────────────────┐  ┌─────────────────────┐  ┌─────────────────────┐ │
│  │   Local Inference   │  │   External API      │  │   Hybrid Mode       │ │
│  │                     │  │                     │  │                     │ │
│  │  ┌───────────────┐  │  │  ┌───────────────┐  │  │  Local + Fallback  │ │
│  │  │     Burn      │  │  │  │    OpenAI     │  │  │                     │ │
│  │  │  (GPU/CPU)    │  │  │  │   Anthropic   │  │  │                     │ │
│  │  └───────────────┘  │  │  │    Ollama     │  │  │                     │ │
│  │  ┌───────────────┐  │  │  └───────────────┘  │  │                     │ │
│  │  │   SmartCore   │  │  │                     │  │                     │ │
│  │  │  (Classical)  │  │  │                     │  │                     │ │
│  │  └───────────────┘  │  │                     │  │                     │ │
│  └─────────────────────┘  └─────────────────────┘  └─────────────────────┘ │
│                                              │                               │
│                                              ▼                               │
│  ┌────────────────────────────────────────────────────────────────────────┐ │
│  │                      Response Generation                                │ │
│  │  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐                     │ │
│  │  │   Sync      │  │  Streaming  │  │   Error     │                     │ │
│  │  │  Response   │  │    SSE      │  │  Handling   │                     │ │
│  │  └─────────────┘  └─────────────┘  └─────────────┘                     │ │
│  └────────────────────────────────────────────────────────────────────────┘ │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Crate Organization

```
open-responses-engine/
├── Cargo.toml              # Workspace configuration
├── Cargo.lock
├── crates/
│   ├── or-core/            # Core types and traits
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── types.rs    # Request/Response types
│   │       ├── error.rs    # Error definitions
│   │       └── traits.rs   # Provider traits
│   │
│   ├── or-server/          # HTTP server
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── main.rs
│   │       ├── handlers.rs
│   │       ├── middleware.rs
│   │       └── state.rs
│   │
│   ├── or-providers/       # LLM providers
│   │   ├── Cargo.toml
│   │   └── src/
│   │       ├── lib.rs
│   │       ├── openai.rs
│   │       ├── anthropic.rs
│   │       ├── ollama.rs
│   │       └── local.rs
│   │
│   └── or-inference/       # Local inference
│       ├── Cargo.toml
│       └── src/
│           ├── lib.rs
│           ├── burn.rs     # Burn integration
│           └── smartcore.rs # SmartCore integration
│
├── config/
│   ├── default.toml
│   └── production.toml
│
└── tests/
    ├── integration/
    └── e2e/
```

---

## Core Types

### Request Types

```rust
use serde::{Deserialize, Serialize};
use validator::Validate;

#[derive(Debug, Clone, Deserialize, Validate)]
#[serde(rename_all = "snake_case")]
pub struct CreateResponseRequest {
    pub model: String,

    #[validate(custom = "validate_input")]
    pub input: Input,

    #[serde(default)]
    pub instructions: Option<String>,

    #[serde(default)]
    pub tools: Vec<ToolDefinition>,

    #[serde(default)]
    pub tool_choice: Option<ToolChoice>,

    #[serde(default)]
    pub response_format: Option<ResponseFormat>,

    #[serde(default)]
    pub temperature: Option<f32>,

    #[serde(default)]
    pub top_p: Option<f32>,

    #[serde(default)]
    pub max_output_tokens: Option<u32>,

    #[serde(default)]
    pub stream: bool,

    #[serde(default)]
    pub metadata: Option<serde_json::Value>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(untagged)]
pub enum Input {
    Text(String),
    Messages(Vec<Message>),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub role: Role,
    pub content: Vec<ContentBlock>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Role {
    User,
    Assistant,
    System,
    Tool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum ContentBlock {
    Text { text: String },
    ToolUse { id: String, name: String, input: serde_json::Value },
    ToolResult { tool_use_id: String, content: String },
}
```

### Response Types

```rust
#[derive(Debug, Clone, Serialize)]
pub struct ResponseOutput {
    pub id: String,
    pub object: &'static str,
    pub created_at: i64,
    pub model: String,
    pub status: ResponseStatus,
    pub output: Vec<OutputItem>,
    pub usage: Usage,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub error: Option<ApiError>,
}

#[derive(Debug, Clone, Copy, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum ResponseStatus {
    Completed,
    RequiresAction,
    Failed,
    Cancelled,
    InProgress,
}

#[derive(Debug, Clone, Serialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum OutputItem {
    Message {
        id: String,
        role: Role,
        content: Vec<ContentBlock>,
    },
}

#[derive(Debug, Clone, Serialize, Default)]
pub struct Usage {
    pub input_tokens: u32,
    pub output_tokens: u32,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache_read_tokens: Option<u32>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cache_write_tokens: Option<u32>,
}
```

---

## Provider Trait

```rust
use async_trait::async_trait;
use futures::Stream;
use std::pin::Pin;

pub type StreamResult = Pin<Box<dyn Stream<Item = Result<StreamEvent, ApiError>> + Send>>;

#[async_trait]
pub trait Provider: Send + Sync {
    /// Provider name for routing
    fn name(&self) -> &str;

    /// Check if provider supports the given model
    fn supports_model(&self, model: &str) -> bool;

    /// Generate a response synchronously
    async fn generate(&self, request: CreateResponseRequest) -> Result<ResponseOutput, ApiError>;

    /// Generate a streaming response
    async fn generate_stream(&self, request: CreateResponseRequest) -> Result<StreamResult, ApiError>;

    /// List available models
    async fn list_models(&self) -> Result<Vec<ModelInfo>, ApiError>;

    /// Health check
    async fn health_check(&self) -> Result<HealthStatus, ApiError>;
}
```

---

## Streaming Implementation

```rust
use axum::response::sse::{Event, Sse};
use futures::stream::{self, Stream};
use std::convert::Infallible;
use tokio::sync::mpsc;

pub async fn handle_streaming_response(
    State(state): State<AppState>,
    Json(request): Json<CreateResponseRequest>,
) -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let (tx, rx) = mpsc::channel::<StreamEvent>(100);

    // Spawn generation task
    tokio::spawn(async move {
        let provider = state.router.route(&request.model);

        match provider.generate_stream(request).await {
            Ok(mut stream) => {
                while let Some(event) = stream.next().await {
                    match event {
                        Ok(e) => {
                            if tx.send(e).await.is_err() {
                                break;
                            }
                        }
                        Err(e) => {
                            let _ = tx.send(StreamEvent::Error(e)).await;
                            break;
                        }
                    }
                }
            }
            Err(e) => {
                let _ = tx.send(StreamEvent::Error(e)).await;
            }
        }
    });

    // Convert to SSE stream
    let stream = tokio_stream::wrappers::ReceiverStream::new(rx).map(|event| {
        let (event_type, data) = match event {
            StreamEvent::Created(r) => ("response.created", serde_json::to_string(&r).unwrap()),
            StreamEvent::TextDelta(d) => ("response.output_text.delta", serde_json::json!({"delta": d}).to_string()),
            StreamEvent::Completed(r) => ("response.completed", serde_json::to_string(&r).unwrap()),
            StreamEvent::Error(e) => ("error", serde_json::to_string(&e).unwrap()),
        };

        Ok(Event::default().event(event_type).data(data))
    });

    Sse::new(stream).keep_alive(
        axum::response::sse::KeepAlive::new()
            .interval(Duration::from_secs(15))
            .text("keep-alive"),
    )
}
```

---

## Error Handling

```rust
use axum::{
    http::StatusCode,
    response::{IntoResponse, Response},
    Json,
};
use thiserror::Error;

#[derive(Error, Debug)]
pub enum ApiError {
    #[error("Invalid request: {message}")]
    InvalidRequest { message: String, param: Option<String> },

    #[error("Authentication failed")]
    AuthenticationError,

    #[error("Model not found: {0}")]
    ModelNotFound(String),

    #[error("Rate limit exceeded")]
    RateLimitExceeded { retry_after: u32 },

    #[error("Provider error: {0}")]
    ProviderError(String),

    #[error("Internal error")]
    InternalError(#[from] anyhow::Error),
}

impl IntoResponse for ApiError {
    fn into_response(self) -> Response {
        let (status, error_type, message) = match &self {
            ApiError::InvalidRequest { message, .. } => {
                (StatusCode::BAD_REQUEST, "invalid_request_error", message.clone())
            }
            ApiError::AuthenticationError => {
                (StatusCode::UNAUTHORIZED, "authentication_error", "Invalid API key".into())
            }
            ApiError::ModelNotFound(model) => {
                (StatusCode::NOT_FOUND, "not_found_error", format!("Model '{}' not found", model))
            }
            ApiError::RateLimitExceeded { .. } => {
                (StatusCode::TOO_MANY_REQUESTS, "rate_limit_error", "Rate limit exceeded".into())
            }
            ApiError::ProviderError(msg) => {
                (StatusCode::BAD_GATEWAY, "api_error", msg.clone())
            }
            ApiError::InternalError(_) => {
                (StatusCode::INTERNAL_SERVER_ERROR, "api_error", "Internal server error".into())
            }
        };

        let body = serde_json::json!({
            "error": {
                "type": error_type,
                "message": message,
            }
        });

        (status, Json(body)).into_response()
    }
}
```

---

## Configuration

```rust
use config::{Config, ConfigError, File};
use serde::Deserialize;
use std::path::Path;

#[derive(Debug, Deserialize)]
pub struct Settings {
    pub server: ServerSettings,
    pub providers: ProvidersSettings,
    pub cache: CacheSettings,
    pub logging: LoggingSettings,
}

#[derive(Debug, Deserialize)]
pub struct ServerSettings {
    pub host: String,
    pub port: u16,
    pub workers: usize,
    pub timeout_secs: u64,
}

#[derive(Debug, Deserialize)]
pub struct ProvidersSettings {
    pub openai: Option<OpenAISettings>,
    pub anthropic: Option<AnthropicSettings>,
    pub ollama: Option<OllamaSettings>,
    pub local: Option<LocalSettings>,
}

impl Settings {
    pub fn load(config_path: impl AsRef<Path>) -> Result<Self, ConfigError> {
        let config = Config::builder()
            .add_source(File::from(config_path.as_ref()))
            .add_source(config::Environment::with_prefix("OR").separator("__"))
            .build()?;

        config.try_deserialize()
    }
}
```

---

## Performance Optimizations

### Connection Pooling

```rust
use reqwest::Client;
use std::time::Duration;

pub fn create_http_client() -> Client {
    Client::builder()
        .pool_max_idle_per_host(100)
        .pool_idle_timeout(Duration::from_secs(90))
        .connect_timeout(Duration::from_secs(10))
        .timeout(Duration::from_secs(300))
        .tcp_keepalive(Duration::from_secs(60))
        .tcp_nodelay(true)
        .build()
        .expect("Failed to create HTTP client")
}
```

### Response Caching

```rust
use moka::future::Cache;
use std::sync::Arc;

pub struct ResponseCache {
    cache: Cache<String, Arc<ResponseOutput>>,
}

impl ResponseCache {
    pub fn new(max_capacity: u64, ttl_secs: u64) -> Self {
        let cache = Cache::builder()
            .max_capacity(max_capacity)
            .time_to_live(Duration::from_secs(ttl_secs))
            .build();

        Self { cache }
    }

    pub fn cache_key(request: &CreateResponseRequest) -> String {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(serde_json::to_vec(request).unwrap_or_default());
        format!("{:x}", hasher.finalize())
    }
}
```

---

## Testing

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use axum::http::StatusCode;
    use axum_test::TestServer;

    #[tokio::test]
    async fn test_create_response() {
        let app = create_app().await;
        let server = TestServer::new(app).unwrap();

        let response = server
            .post("/v1/responses")
            .json(&serde_json::json!({
                "model": "test/model",
                "input": "Hello, world!"
            }))
            .await;

        assert_eq!(response.status_code(), StatusCode::OK);
    }

    #[tokio::test]
    async fn test_streaming_response() {
        let app = create_app().await;
        let server = TestServer::new(app).unwrap();

        let response = server
            .post("/v1/responses")
            .json(&serde_json::json!({
                "model": "test/model",
                "input": "Hello, world!",
                "stream": true
            }))
            .await;

        assert_eq!(response.status_code(), StatusCode::OK);
        assert_eq!(
            response.headers().get("content-type").unwrap(),
            "text/event-stream"
        );
    }
}
```
