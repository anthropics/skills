# Rust MCP Server Implementation Guide

## Overview

This document provides Rust-specific best practices and examples for implementing MCP servers using the official `rmcp` crate. It covers project structure, server setup, tool registration with macros, error handling, transport options, and complete working examples.

---

## Quick Reference

### Key Dependencies (Cargo.toml)
```toml
[dependencies]
rmcp = { version = "0.8.1", features = ["server"] }
tokio = { version = "1", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
schemars = { version = "0.8", features = ["derive"] }
anyhow = "1.0"
tracing = "0.1"
tracing-subscriber = "0.3"
```

### Server Initialization
```rust
let server = Server::builder()
    .with_handler(handler)
    .with_capabilities(ServerCapabilities {
        tools: Some(Default::default()),
        ..Default::default()
    })
    .build(transport)?;
```

### Tool Registration Pattern (Macro)
```rust
#[tool(name = "service_action", annotations(read_only_hint = true))]
pub async fn my_tool(params: Parameters<MyInput>) -> Result<String, String> {
    // Implementation
}
```

---

## rmcp SDK

The official Rust SDK (`rmcp`) provides:
- `Server` builder for server initialization
- `ServerHandler` trait for implementing tool/resource/prompt handlers
- `#[tool]`, `#[tool_router]`, and `#[tool_handler]` macros for declarative registration
- `schemars` integration for automatic JSON Schema generation from Rust types
- `StdioTransport`, `SseServerTransport`, and `StreamableHttpTransport`

**Two approaches:**
- **Macro-based** (recommended): Use `#[tool]` and `#[tool_router]` for declarative tool definitions with automatic schema generation
- **Manual**: Implement `ServerHandler` trait directly for full control

## Server Naming Convention

Rust MCP servers should follow this naming pattern:
- **Crate name**: `{service}-mcp-server` (lowercase with hyphens)
- **Server info name**: `{service}-mcp`
- **Examples**: crate `github-mcp-server`, server name `github-mcp`

## Project Structure

```
{service}-mcp-server/
├── Cargo.toml
├── src/
│   ├── main.rs           # Server entry point
│   ├── handler.rs        # ServerHandler implementation
│   ├── tools/
│   │   ├── mod.rs
│   │   └── repos.rs      # Tool params, handlers
│   ├── resources/
│   │   └── mod.rs
│   └── client.rs         # HTTP client, auth
└── tests/
    └── integration.rs
```

## Tool Implementation

### Using the `#[tool]` Macro

```rust
use rmcp::tool;
use rmcp::model::Parameters;
use schemars::JsonSchema;
use serde::Deserialize;

#[derive(Debug, Deserialize, JsonSchema)]
pub struct SearchInput {
    /// Search query string
    pub query: String,
    /// Maximum results to return (1-100)
    #[serde(default = "default_limit")]
    pub limit: Option<u32>,
}

fn default_limit() -> Option<u32> { Some(20) }

/// Search for items by query. Returns matching records with ID, name, and status.
#[tool(
    name = "service_search",
    description = "Search for items. Returns matching records.",
    annotations(read_only_hint = true, idempotent_hint = true)
)]
pub async fn search(params: Parameters<SearchInput>) -> Result<String, String> {
    let input = params.inner();
    let limit = input.limit.unwrap_or(20);

    let results = api_client::search(&input.query, limit)
        .await
        .map_err(|e| format!("Search failed: {e}"))?;

    serde_json::to_string_pretty(&results)
        .map_err(|e| format!("Serialization failed: {e}"))
}
```

### Tool Router with Multiple Tools

```rust
use rmcp::{tool_router, tool_handler};

pub struct ToolsHandler {
    tool_router: ToolRouter,
    client: ApiClient,
}

#[tool_router]
impl ToolsHandler {
    #[tool(annotations(read_only_hint = true))]
    async fn list_repos(&self, params: Parameters<ListReposInput>) -> Result<String, String> {
        let repos = self.client.list_repos(&params.inner().owner).await
            .map_err(|e| format!("Failed to list repos: {e}"))?;
        serde_json::to_string_pretty(&repos).map_err(|e| e.to_string())
    }

    #[tool(annotations(destructive_hint = true))]
    async fn delete_repo(&self, params: Parameters<DeleteRepoInput>) -> Result<String, String> {
        self.client.delete_repo(&params.inner().owner, &params.inner().name).await
            .map_err(|e| format!("Failed to delete repo: {e}"))?;
        Ok("Repository deleted successfully".to_string())
    }

    pub fn new(client: ApiClient) -> Self {
        Self {
            tool_router: Self::tool_router(),
            client,
        }
    }
}

#[tool_handler]
impl ServerHandler for ToolsHandler {}
```

### Tool Annotations

```rust
#[tool(
    name = "delete_resource",
    annotations(
        destructive_hint = true,
        read_only_hint = false,
        idempotent_hint = false,
        open_world_hint = true
    )
)]
```

| Annotation | When to set |
| ---------- | ----------- |
| `read_only_hint = true` | GET-equivalent, no side effects |
| `destructive_hint = true` | DELETE or irreversible operations |
| `idempotent_hint = true` | PUT/UPSERT, safe to retry |
| `open_world_hint = true` | Calls external APIs |

## Schema Definition with schemars

Derive `JsonSchema` for automatic schema generation:

```rust
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, JsonSchema)]
pub struct CreateUserInput {
    /// User's full name
    pub name: String,
    /// Email address
    pub email: String,
    /// User's age (0-150)
    #[schemars(range(min = 0, max = 150))]
    pub age: u32,
    /// Optional team assignment
    pub team: Option<String>,
}
```

## Error Handling

### ErrorData for MCP errors

```rust
use rmcp::ErrorData;

fn validate_params(value: &str) -> Result<(), ErrorData> {
    if value.is_empty() {
        return Err(ErrorData::invalid_params("Value cannot be empty"));
    }
    Ok(())
}
```

### Actionable tool errors

```rust
#[tool]
async fn get_repo(params: Parameters<GetRepoInput>) -> Result<String, String> {
    let input = params.inner();
    match client.get_repo(&input.owner, &input.name).await {
        Ok(repo) => serde_json::to_string_pretty(&repo).map_err(|e| e.to_string()),
        Err(ApiError::NotFound) => Err(format!(
            "Repository {}/{} not found — verify the owner and repo name; use list_repos to discover available repositories",
            input.owner, input.name
        )),
        Err(ApiError::Forbidden) => Err(
            "Access denied — check that your API token has the required scopes".to_string()
        ),
        Err(e) => Err(format!("API request failed: {e}")),
    }
}
```

## Transport Configuration

### stdio (local, default)

```rust
use rmcp::transport::StdioTransport;

let transport = StdioTransport::new();
let server = Server::builder()
    .with_handler(handler)
    .build(transport)?;
server.run(signal::ctrl_c()).await?;
```

### Streamable HTTP with Axum

```rust
use rmcp::transport::StreamableHttpTransport;
use axum::{Router, routing::post};

let transport = StreamableHttpTransport::new();
let app = Router::new().route("/mcp", post(transport.handler()));

let listener = tokio::net::TcpListener::bind("127.0.0.1:3000").await?;
axum::serve(listener, app).await?;
```

### SSE Transport

```rust
use rmcp::transport::SseServerTransport;

let addr: std::net::SocketAddr = "127.0.0.1:8000".parse()?;
let transport = SseServerTransport::new(addr);
let server = Server::builder().with_handler(handler).build(transport)?;
server.run(signal::ctrl_c()).await?;
```

## Resource Implementation

```rust
async fn list_resources(
    &self,
    _request: Option<PaginatedRequestParam>,
    _context: RequestContext<RoleServer>,
) -> Result<ListResourcesResult, ErrorData> {
    Ok(ListResourcesResult {
        resources: vec![Resource {
            uri: "config://settings".to_string(),
            name: "Settings".to_string(),
            description: Some("Server configuration".to_string()),
            mime_type: Some("application/json".to_string()),
        }],
    })
}

async fn read_resource(
    &self,
    request: ReadResourceRequestParam,
    _context: RequestContext<RoleServer>,
) -> Result<ReadResourceResult, ErrorData> {
    match request.uri.as_str() {
        "config://settings" => Ok(ReadResourceResult {
            contents: vec![ResourceContents::text(load_settings())
                .with_uri(request.uri)
                .with_mime_type("application/json")],
        }),
        _ => Err(ErrorData::invalid_params("Unknown resource")),
    }
}
```

## Complete Example

```rust
use rmcp::{tool, tool_router, tool_handler};
use rmcp::model::Parameters;
use rmcp::server::{Server, ServerHandler};
use rmcp::transport::StdioTransport;
use rmcp::protocol::ServerCapabilities;
use schemars::JsonSchema;
use serde::Deserialize;
use tokio::signal;

#[derive(Debug, Deserialize, JsonSchema)]
pub struct ListReposInput {
    /// GitHub organization or username
    pub owner: String,
    /// Results per page (1-100)
    pub per_page: Option<u32>,
}

pub struct MyHandler {
    tool_router: ToolRouter,
}

#[tool_router]
impl MyHandler {
    /// List repositories for an owner. Returns name, description, and star count.
    #[tool(name = "list_repos", annotations(read_only_hint = true))]
    async fn list_repos(&self, params: Parameters<ListReposInput>) -> Result<String, String> {
        let input = params.inner();
        let per_page = input.per_page.unwrap_or(30);
        Ok(format!(r#"{{"repos": [{{"name": "example", "stars": 42}}], "total": 1}}"#))
    }

    pub fn new() -> Self {
        Self { tool_router: Self::tool_router() }
    }
}

#[tool_handler]
impl ServerHandler for MyHandler {}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt::init();

    let api_token = std::env::var("API_TOKEN")
        .expect("API_TOKEN environment variable is required");

    let handler = MyHandler::new();
    let transport = StdioTransport::new();

    let server = Server::builder()
        .with_handler(handler)
        .with_capabilities(ServerCapabilities {
            tools: Some(Default::default()),
            ..Default::default()
        })
        .build(transport)?;

    server.run(signal::ctrl_c()).await?;
    Ok(())
}
```

---

## Quality Checklist

Before finalizing your Rust MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names are `snake_case` with consistent service prefix
- [ ] Error messages guide agents toward correct usage with recovery hints

### Implementation Quality
- [ ] Tools use `#[tool]` macro with `name`, `description`, and `annotations`
- [ ] Input types derive `Deserialize` and `JsonSchema` with doc comments on fields
- [ ] Annotations correctly set (read_only_hint, destructive_hint, idempotent_hint, open_world_hint)
- [ ] Tool errors return `Result::Err(String)` with actionable messages
- [ ] `ErrorData::invalid_params` used for validation failures

### Rust Quality
- [ ] All async operations use `tokio` runtime
- [ ] No `unwrap()` or `expect()` in tool handlers — return `Result` errors
- [ ] Error chains preserved with `map_err` and context
- [ ] No hardcoded credentials — all secrets via environment variables
- [ ] `tracing` used for structured logging

### Project Configuration
- [ ] `Cargo.toml` includes `rmcp`, `tokio`, `serde`, `schemars`, `tracing`
- [ ] Crate name follows format: `{service}-mcp-server`
- [ ] `cargo build` succeeds with no errors
- [ ] `cargo clippy` passes with no warnings

### Testing
- [ ] `cargo build` compiles without errors
- [ ] `cargo clippy` passes
- [ ] `cargo test` passes
- [ ] Manual test with MCP Inspector: `npx @modelcontextprotocol/inspector cargo run`
