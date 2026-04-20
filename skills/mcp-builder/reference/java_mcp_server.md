# Java MCP Server Implementation Guide

## Overview

This document provides Java-specific best practices and examples for implementing MCP servers using the official MCP Java SDK (`io.modelcontextprotocol.sdk:mcp`). It covers server setup with reactive streams, tool registration, Spring Boot integration, and complete working examples.

---

## Quick Reference

### Key Dependency (Maven)
```xml
<dependency>
    <groupId>io.modelcontextprotocol.sdk</groupId>
    <artifactId>mcp</artifactId>
    <version>0.14.1</version>
</dependency>
```

### Server Initialization
```java
McpServer server = McpServerBuilder.builder()
    .serverInfo("service-mcp-server", "1.0.0")
    .capabilities(cap -> cap.tools(true).resources(true).prompts(true))
    .build();
```

### Tool Registration Pattern
```java
server.addToolHandler("service_action", (args) -> {
    return Mono.just(ToolResponse.success()
        .addTextContent("Result")
        .build());
});
```

---

## MCP Java SDK

The official Java SDK provides:
- `McpServerBuilder` for fluent server construction
- `Tool.builder()` for tool definitions with JSON Schema
- Reactive Streams (Project Reactor) for async handlers returning `Mono<T>`
- `McpSyncServer` for synchronous blocking facade
- `StdioServerTransport`, `ServletServerTransport`
- Spring Boot starter for enterprise integration

**Two programming models:**
- **Reactive** (recommended): Return `Mono<ToolResponse>` for non-blocking async
- **Synchronous**: Use `server.toSyncServer()` for blocking handlers

## Server Naming Convention

Java MCP servers should follow this naming pattern:
- **Artifact**: `{service}-mcp-server` (lowercase with hyphens)
- **Server info name**: `{service}-mcp-server`
- **Examples**: `github-mcp-server`, `jira-mcp-server`, `stripe-mcp-server`

## Project Structure

### Maven
```
{service}-mcp-server/
├── pom.xml
├── src/main/java/
│   └── com/example/mcp/
│       ├── Application.java    # Entry point
│       ├── tools/
│       │   ├── SearchTools.java
│       │   └── ManageTools.java
│       ├── prompts/
│       │   └── AnalyzePrompts.java
│       └── client/
│           └── ApiClient.java
└── src/test/java/
    └── com/example/mcp/
        └── ToolsTest.java
```

### Gradle (build.gradle.kts)
```kotlin
dependencies {
    implementation("io.modelcontextprotocol.sdk:mcp:0.14.1")
}
```

## Tool Implementation

### Defining Tools

```java
Tool searchTool = Tool.builder()
    .name("service_search")
    .description("Search for items by query. Returns matching records with ID, name, and status.")
    .inputSchema(JsonSchema.object()
        .property("query", JsonSchema.string()
            .description("Search query string")
            .required(true))
        .property("limit", JsonSchema.integer()
            .description("Maximum results to return (1-100)")
            .minimum(1).maximum(100)
            .defaultValue(20))
        .additionalProperties(false))
    .build();
```

### Reactive Tool Handler

```java
server.addToolHandler("service_search", (args) -> {
    return Mono.fromCallable(() -> {
        String query = args.get("query").asText();
        int limit = args.has("limit") ? args.get("limit").asInt() : 20;

        List<Item> results = apiClient.search(query, limit);

        if (results.isEmpty()) {
            return ToolResponse.error()
                .message("No results found for '" + query + "'")
                .build();
        }

        return ToolResponse.success()
            .addTextContent(objectMapper.writeValueAsString(
                Map.of("total", results.size(), "results", results)))
            .build();
    }).subscribeOn(Schedulers.boundedElastic());
});
```

### Synchronous Tool Handler

```java
McpSyncServer syncServer = server.toSyncServer();

syncServer.addToolHandler("service_ping", (args) -> {
    return ToolResponse.success()
        .addTextContent("pong")
        .build();
});
```

## JSON Schema Construction

Use the fluent schema builder:

```java
JsonSchema schema = JsonSchema.object()
    .property("name", JsonSchema.string()
        .description("User's full name")
        .minLength(1).maxLength(100)
        .required(true))
    .property("email", JsonSchema.string()
        .description("Email address")
        .format("email")
        .required(true))
    .property("age", JsonSchema.integer()
        .description("User's age")
        .minimum(0).maximum(150))
    .property("tags", JsonSchema.array()
        .items(JsonSchema.string())
        .uniqueItems(true))
    .additionalProperties(false)
    .build();
```

## Resource Implementation

```java
server.addResourceListHandler(() -> {
    return Mono.just(List.of(
        Resource.builder()
            .uri("config://settings")
            .name("Settings")
            .description("Server configuration")
            .mimeType("application/json")
            .build()
    ));
});

server.addResourceReadHandler((uri) -> {
    if (uri.equals("config://settings")) {
        String content = loadSettings();
        return Mono.just(ResourceContent.text(content, uri));
    }
    throw new ResourceNotFoundException(uri);
});
```

## Prompt Implementation

```java
server.addPromptListHandler(() -> {
    return Mono.just(List.of(
        Prompt.builder()
            .name("analyze")
            .description("Analyze a topic in depth")
            .argument(PromptArgument.builder()
                .name("topic").description("Topic to analyze").required(true).build())
            .argument(PromptArgument.builder()
                .name("depth").description("Analysis depth").required(false).build())
            .build()
    ));
});

server.addPromptGetHandler((name, arguments) -> {
    if ("analyze".equals(name)) {
        String topic = arguments.getOrDefault("topic", "general");
        String depth = arguments.getOrDefault("depth", "basic");

        return Mono.just(PromptResult.builder()
            .description("Analysis of " + topic)
            .messages(List.of(
                PromptMessage.user("Analyze: " + topic + " at " + depth + " depth")
            ))
            .build());
    }
    throw new PromptNotFoundException(name);
});
```

## Transport Configuration

### stdio (local, default)

```java
StdioServerTransport transport = new StdioServerTransport();
server.start(transport).block();
```

### HTTP Servlet Transport

```java
public class McpServlet extends HttpServlet {
    private final McpServer server = createMcpServer();
    private final ServletServerTransport transport = new ServletServerTransport();

    @Override
    protected void doPost(HttpServletRequest req, HttpServletResponse resp) {
        transport.handleRequest(server, req, resp).block();
    }
}
```

## Spring Boot Integration

### Dependency

```xml
<dependency>
    <groupId>io.modelcontextprotocol.sdk</groupId>
    <artifactId>mcp-spring-boot-starter</artifactId>
    <version>0.14.1</version>
</dependency>
```

### Configuration

```java
@Configuration
public class McpConfiguration {
    @Bean
    public McpServerConfigurer mcpServerConfigurer() {
        return server -> server
            .serverInfo("service-mcp-server", "1.0.0")
            .capabilities(cap -> cap.tools(true).resources(true));
    }
}
```

### Spring Bean Tool Handler

```java
@Component
public class SearchToolHandler implements ToolHandler {
    @Override
    public String getName() { return "service_search"; }

    @Override
    public Tool getTool() {
        return Tool.builder()
            .name("service_search")
            .description("Search for items")
            .inputSchema(JsonSchema.object()
                .property("query", JsonSchema.string().required(true)))
            .build();
    }

    @Override
    public Mono<ToolResponse> handle(JsonNode arguments) {
        String query = arguments.get("query").asText();
        return Mono.just(ToolResponse.success()
            .addTextContent("Results for: " + query)
            .build());
    }
}
```

## Error Handling

```java
server.addToolHandler("service_risky", (args) -> {
    return Mono.fromCallable(() -> {
        try {
            String result = riskyOperation(args);
            return ToolResponse.success().addTextContent(result).build();
        } catch (ValidationException e) {
            return ToolResponse.error()
                .message("Invalid input: " + e.getMessage())
                .build();
        } catch (NotFoundException e) {
            return ToolResponse.error()
                .message("Resource not found — verify the ID; use service_list to discover available items")
                .build();
        }
    });
});
```

## Reactive Best Practices

```java
// Use bounded elastic scheduler for blocking calls
server.addToolHandler("service_blocking", (args) -> {
    return Mono.fromCallable(() -> blockingApiCall(args))
        .timeout(Duration.ofSeconds(30))
        .onErrorResume(TimeoutException.class, e ->
            Mono.just(ToolResponse.error().message("Operation timed out").build()))
        .subscribeOn(Schedulers.boundedElastic());
});

// Propagate reactive context
server.addToolHandler("service_traced", (args) -> {
    return Mono.deferContextual(ctx -> {
        String traceId = ctx.get("traceId");
        log.info("Processing with traceId: {}", traceId);
        return Mono.just(ToolResponse.success().addTextContent("Done").build());
    });
});
```

## Logging

Use SLF4J (not System.out):

```java
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

private static final Logger log = LoggerFactory.getLogger(MyServer.class);

server.addToolHandler("service_process", (args) -> {
    log.info("Tool called: service_process, args: {}", args);
    return Mono.fromCallable(() -> {
        String result = process(args);
        log.debug("Processing completed");
        return ToolResponse.success().addTextContent(result).build();
    }).doOnError(error -> log.error("Processing failed", error));
});
```

## Server Lifecycle

```java
Disposable serverDisposable = server.start(transport).subscribe();

Runtime.getRuntime().addShutdownHook(new Thread(() -> {
    log.info("Shutting down MCP server");
    serverDisposable.dispose();
    server.stop().block();
}));
```

## Complete Example

```java
import io.mcp.server.*;
import io.mcp.server.tool.*;
import io.mcp.server.transport.StdioServerTransport;
import reactor.core.publisher.Mono;

public class Application {
    public static void main(String[] args) {
        String token = System.getenv("API_TOKEN");
        if (token == null || token.isEmpty()) {
            System.err.println("API_TOKEN environment variable is required");
            System.exit(1);
        }

        McpServer server = McpServerBuilder.builder()
            .serverInfo("example-mcp-server", "1.0.0")
            .capabilities(cap -> cap.tools(true))
            .build();

        Tool listRepos = Tool.builder()
            .name("list_repos")
            .description("List repos for an owner. Returns name, description, and star count.")
            .inputSchema(JsonSchema.object()
                .property("owner", JsonSchema.string()
                    .description("GitHub org or username").required(true))
                .property("perPage", JsonSchema.integer()
                    .description("Results per page (1-100)").defaultValue(30)))
            .build();

        server.addToolHandler("list_repos", (arguments) -> {
            String owner = arguments.get("owner").asText();
            return Mono.just(ToolResponse.success()
                .addTextContent("{\"repos\": [{\"name\": \"example\", \"stars\": 42}], \"total\": 1}")
                .build());
        });

        StdioServerTransport transport = new StdioServerTransport();
        server.start(transport).block();
    }
}
```

---

## Quality Checklist

Before finalizing your Java MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names are `snake_case` with consistent service prefix
- [ ] Error messages guide agents toward correct usage

### Implementation Quality
- [ ] All tools defined with `Tool.builder()` including `name`, `description`, `inputSchema`
- [ ] JSON schemas use `JsonSchema.object()` with property descriptions and constraints
- [ ] Required fields marked with `.required(true)`
- [ ] Error responses use `ToolResponse.error().message(...)` with actionable messages
- [ ] All async handlers return `Mono<ToolResponse>`

### Java Quality
- [ ] Uses SLF4J for logging (not `System.out`)
- [ ] `Schedulers.boundedElastic()` for blocking operations in reactive chains
- [ ] Proper `try`/`catch` with specific exception types
- [ ] No hardcoded credentials — all secrets via `System.getenv`
- [ ] Graceful shutdown with `Runtime.addShutdownHook`

### Project Configuration
- [ ] `pom.xml` or `build.gradle.kts` includes `mcp` SDK dependency
- [ ] `mvn compile` / `gradle build` succeeds with no errors
- [ ] Server name follows format: `{service}-mcp-server`

### Spring Boot (if applicable)
- [ ] `mcp-spring-boot-starter` dependency added
- [ ] `McpServerConfigurer` bean defined
- [ ] Tool handlers registered as Spring `@Component` beans

### Testing
- [ ] Build compiles without errors
- [ ] Unit tests pass (use `McpSyncServer` for simpler test setup)
- [ ] Manual test with MCP Inspector: `npx @modelcontextprotocol/inspector java -jar target/*.jar`
