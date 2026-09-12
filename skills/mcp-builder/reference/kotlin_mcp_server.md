# Kotlin MCP Server Implementation Guide

## Overview

This document provides Kotlin-specific best practices and examples for implementing MCP servers using the official `io.modelcontextprotocol:kotlin-sdk`. It covers server setup, tool registration, coroutine-based handlers, transport options, and complete working examples.

---

## Quick Reference

### Key Dependencies (build.gradle.kts)
```kotlin
dependencies {
    implementation("io.modelcontextprotocol:kotlin-sdk:0.7.2")
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.7.3")
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.9.0")
}
```

### Server Initialization
```kotlin
val server = Server(
    serverInfo = Implementation(name = "service-mcp", version = "1.0.0"),
    options = ServerOptions(
        capabilities = ServerCapabilities(tools = ServerCapabilities.Tools())
    )
) { "Service MCP Server" }
```

### Tool Registration Pattern
```kotlin
server.addTool(
    name = "service_action",
    description = "What this tool does and returns",
    inputSchema = buildJsonObject { /* ... */ }
) { request -> CallToolResult(content = listOf(TextContent(text = "result"))) }
```

---

## Kotlin SDK

The official Kotlin SDK provides:
- `Server` class for server initialization with DSL-style configuration
- `addTool`, `addResource`, `addPrompt` methods for registration
- Full Kotlin coroutines support (`suspend` functions)
- `kotlinx.serialization` for JSON schema construction
- `StdioServerTransport` for local and Ktor SSE for remote
- Kotlin Multiplatform support (JVM, Wasm, iOS)

## Server Naming Convention

Kotlin MCP servers should follow this naming pattern:
- **Format**: `{service}-mcp` (lowercase with hyphens)
- **Artifact**: `{service}-mcp-server`
- **Examples**: `github-mcp`, `jira-mcp`, `stripe-mcp`

## Project Structure

```
{service}-mcp-server/
├── build.gradle.kts
├── settings.gradle.kts
├── src/main/kotlin/
│   └── com/example/mcp/
│       ├── Main.kt        # Entry point, server setup
│       ├── Tools.kt       # Tool definitions and handlers
│       ├── Resources.kt
│       ├── Prompts.kt
│       └── Client.kt      # API client, auth
└── src/test/kotlin/
    └── com/example/mcp/
        └── ServerTest.kt
```

## Tool Implementation

### Registering Tools

```kotlin
import io.modelcontextprotocol.kotlin.sdk.*
import kotlinx.serialization.json.*

server.addTool(
    name = "service_search",
    description = "Search for items by query. Returns matching records with ID, name, and status.",
    inputSchema = buildJsonObject {
        put("type", "object")
        putJsonObject("properties") {
            putJsonObject("query") {
                put("type", "string")
                put("description", "Search query string")
            }
            putJsonObject("limit") {
                put("type", "integer")
                put("description", "Maximum results to return (1-100)")
                put("default", 20)
            }
        }
        putJsonArray("required") { add("query") }
    }
) { request ->
    val query = request.params.arguments["query"] as? String
        ?: throw IllegalArgumentException("query is required")
    val limit = (request.params.arguments["limit"] as? Number)?.toInt() ?: 20

    val results = apiClient.search(query, limit)

    if (results.isEmpty()) {
        CallToolResult(
            content = listOf(TextContent(text = "No results found for '$query'")),
            isError = true
        )
    } else {
        CallToolResult(
            content = listOf(TextContent(text = Json.encodeToString(results)))
        )
    }
}
```

### Parallel Operations with Coroutines

```kotlin
server.addTool(
    name = "service_parallel_search",
    description = "Search multiple sources in parallel"
) { request ->
    coroutineScope {
        val source1 = async { searchSource1(query) }
        val source2 = async { searchSource2(query) }

        val combined = source1.await() + source2.await()
        CallToolResult(content = listOf(TextContent(text = combined.joinToString("\n"))))
    }
}
```

## JSON Schema with kotlinx.serialization

Build schemas using the JSON DSL:

```kotlin
fun createSearchSchema(): JsonObject = buildJsonObject {
    put("type", "object")
    putJsonObject("properties") {
        putJsonObject("query") {
            put("type", "string")
            put("description", "Search query")
        }
        putJsonObject("limit") {
            put("type", "integer")
            put("default", 10)
            put("minimum", 1)
            put("maximum", 100)
        }
        putJsonObject("filters") {
            put("type", "array")
            putJsonObject("items") { put("type", "string") }
        }
    }
    putJsonArray("required") { add("query") }
}
```

## Resource Implementation

```kotlin
server.addResource(
    uri = "config://settings",
    name = "App Settings",
    description = "Current application configuration",
    mimeType = "application/json"
) { request ->
    val content = loadSettings()
    ReadResourceResult(
        contents = listOf(
            TextResourceContents(text = content, uri = request.uri, mimeType = "application/json")
        )
    )
}

// Notify clients when resources change
server.notifyResourceListChanged()
```

## Prompt Implementation

```kotlin
server.addPrompt(
    name = "analyze",
    description = "Analyze a topic in depth",
    arguments = listOf(
        PromptArgument(name = "topic", description = "Topic to analyze", required = true),
        PromptArgument(name = "depth", description = "Analysis depth", required = false)
    )
) { request ->
    val topic = request.params.arguments?.get("topic") as? String
        ?: throw IllegalArgumentException("topic is required")
    val depth = request.params.arguments?.get("depth") as? String ?: "basic"

    GetPromptResult(
        description = "Analysis of $topic",
        messages = listOf(
            PromptMessage(role = Role.User, content = TextContent(text = "Analyze: $topic at $depth depth"))
        )
    )
}
```

## Transport Configuration

### stdio (local, default)

```kotlin
import io.modelcontextprotocol.kotlin.sdk.server.StdioServerTransport

suspend fun main() {
    val transport = StdioServerTransport()
    server.connect(transport)
}
```

### SSE with Ktor

```kotlin
import io.ktor.server.engine.*
import io.ktor.server.netty.*
import io.modelcontextprotocol.kotlin.sdk.server.mcp

fun main() {
    embeddedServer(Netty, port = 8080) {
        mcp {
            Server(
                serverInfo = Implementation(name = "service-mcp", version = "1.0.0"),
                options = ServerOptions(capabilities = ServerCapabilities(tools = ServerCapabilities.Tools()))
            ) { "SSE-based MCP server" }
        }
    }.start(wait = true)
}
```

## Error Handling

```kotlin
server.addTool(name = "service_get_item", description = "Get item by ID") { request ->
    try {
        val id = request.params.arguments["id"] as? String
            ?: throw IllegalArgumentException("id is required")

        require(id.isNotBlank()) { "id cannot be blank" }

        val result = apiClient.getItem(id)
        CallToolResult(content = listOf(TextContent(text = Json.encodeToString(result))))
    } catch (e: IllegalArgumentException) {
        CallToolResult(isError = true, content = listOf(TextContent(text = "Validation error: ${e.message}")))
    } catch (e: NotFoundException) {
        CallToolResult(isError = true, content = listOf(
            TextContent(text = "Item not found — verify the ID; use service_list_items to discover available items")
        ))
    }
}
```

## Gradle Configuration

```kotlin
plugins {
    kotlin("jvm") version "2.1.0"
    kotlin("plugin.serialization") version "2.1.0"
}

repositories { mavenCentral() }

dependencies {
    implementation("io.modelcontextprotocol:kotlin-sdk:0.7.2")
    implementation("io.ktor:ktor-client-cio:3.0.0")        // Client transport
    implementation("io.ktor:ktor-server-netty:3.0.0")       // Server transport (SSE)
    implementation("org.jetbrains.kotlinx:kotlinx-serialization-json:1.7.3")
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.9.0")
}
```

## Complete Example

```kotlin
import io.modelcontextprotocol.kotlin.sdk.*
import io.modelcontextprotocol.kotlin.sdk.server.Server
import io.modelcontextprotocol.kotlin.sdk.server.ServerOptions
import io.modelcontextprotocol.kotlin.sdk.server.StdioServerTransport
import kotlinx.serialization.json.*

suspend fun main() {
    val token = System.getenv("API_TOKEN")
        ?: error("API_TOKEN environment variable is required")

    val server = Server(
        serverInfo = Implementation(name = "example-mcp", version = "1.0.0"),
        options = ServerOptions(capabilities = ServerCapabilities(tools = ServerCapabilities.Tools()))
    ) { "Example MCP Server" }

    server.addTool(
        name = "list_repos",
        description = "List repositories for an owner. Returns name, description, and star count.",
        inputSchema = buildJsonObject {
            put("type", "object")
            putJsonObject("properties") {
                putJsonObject("owner") {
                    put("type", "string")
                    put("description", "GitHub org or username")
                }
                putJsonObject("perPage") {
                    put("type", "integer")
                    put("description", "Results per page (1-100)")
                    put("default", 30)
                }
            }
            putJsonArray("required") { add("owner") }
        }
    ) { request ->
        val owner = request.params.arguments["owner"] as? String ?: ""
        CallToolResult(content = listOf(
            TextContent(text = """{"repos": [{"name": "example", "stars": 42}], "total": 1}""")
        ))
    }

    val transport = StdioServerTransport()
    server.connect(transport)
}
```

---

## Quality Checklist

Before finalizing your Kotlin MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names are `snake_case` with consistent service prefix
- [ ] Error messages guide agents toward correct usage

### Implementation Quality
- [ ] All tools registered with `name`, `description`, and `inputSchema`
- [ ] JSON schemas built with `buildJsonObject` DSL with property descriptions
- [ ] `required` arrays list all mandatory parameters
- [ ] Error responses use `isError = true` with actionable messages
- [ ] All handlers use Kotlin coroutines properly

### Kotlin Quality
- [ ] Uses `suspend` functions for I/O operations
- [ ] `coroutineScope` used for parallel operations
- [ ] Proper `try`/`catch` with specific exception types
- [ ] No hardcoded credentials — all secrets via `System.getenv`
- [ ] `kotlinx.serialization` used for JSON handling

### Project Configuration
- [ ] `build.gradle.kts` includes `kotlin-sdk`, `kotlinx-serialization`, `kotlinx-coroutines`
- [ ] `gradle build` succeeds with no errors
- [ ] Server name follows format: `{service}-mcp`

### Testing
- [ ] `gradle build` compiles without errors
- [ ] `gradle test` passes
- [ ] Manual test with MCP Inspector: `npx @modelcontextprotocol/inspector gradle run`
