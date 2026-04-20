# Swift MCP Server Implementation Guide

## Overview

This document provides Swift-specific best practices and examples for implementing MCP servers using the official MCP Swift SDK (`modelcontextprotocol/swift-sdk`). It covers server setup, tool registration, resource and prompt handlers, transport configuration, and complete working examples.

---

## Quick Reference

### Key Imports
```swift
import MCP
import Logging
```

### Server Initialization
```swift
let server = Server(
    name: "service-mcp",
    version: "1.0.0",
    capabilities: .init(
        tools: .init(listChanged: true),
        resources: .init(subscribe: true, listChanged: true),
        prompts: .init(listChanged: true)
    )
)
```

### Tool Registration Pattern
```swift
await server.withMethodHandler(ListTools.self) { _ in
    .init(tools: [myTool])
}
await server.withMethodHandler(CallTool.self) { params in
    // Handle tool call by params.name
}
```

---

## MCP Swift SDK

The official Swift SDK provides:
- `Server` class with actor-based concurrency safety
- `withMethodHandler` for registering tool, resource, and prompt handlers
- `StdioTransport` for local subprocess communication
- Full Swift concurrency (`async`/`await`) integration

**IMPORTANT - Use `withMethodHandler`:**
- Register `ListTools.self` and `CallTool.self` handlers for tools
- Register `ListResources.self` and `ReadResource.self` handlers for resources
- Register `ListPrompts.self` and `GetPrompt.self` handlers for prompts
- All handlers are `async` and run in the server's actor context

## Server Naming Convention

Swift MCP servers should follow this naming pattern:
- **Format**: `{service}-mcp` (lowercase with hyphens)
- **Examples**: `github-mcp`, `jira-mcp`, `stripe-mcp`

The name should be:
- General (not tied to specific features)
- Descriptive of the service/API being integrated
- Easy to infer from the task description
- Without version numbers or dates

## Project Structure

```
{service}-mcp/
├── Package.swift         # Swift Package Manager manifest
├── Sources/
│   └── {Service}MCP/
│       ├── main.swift    # Entry point, server setup, transport start
│       ├── Tools.swift   # Tool definitions and handlers
│       ├── Resources.swift
│       ├── Prompts.swift
│       └── Client.swift  # API client and auth helpers
└── Tests/
    └── {Service}MCPTests/
        └── ServerTests.swift
```

## Tool Implementation

### Defining Tools

Tools are defined as `Tool` instances with JSON Schema input:

```swift
let searchTool = Tool(
    name: "service_search",
    description: "Search for items. Returns matching records with ID, name, and status.",
    inputSchema: .object([
        "properties": .object([
            "query": .object([
                "type": .string("string"),
                "description": .string("Search query string")
            ]),
            "limit": .object([
                "type": .string("integer"),
                "description": .string("Maximum results to return (1-100)"),
                "default": .number(20)
            ])
        ]),
        "required": .array([.string("query")])
    ])
)
```

### Registering Tool Handlers

```swift
await server.withMethodHandler(ListTools.self) { _ in
    .init(tools: [searchTool, createTool, deleteTool])
}

await server.withMethodHandler(CallTool.self) { params in
    switch params.name {
    case "service_search":
        let query = params.arguments?["query"]?.stringValue ?? ""
        let limit = params.arguments?["limit"]?.intValue ?? 20

        let results = try await apiClient.search(query: query, limit: limit)

        if results.isEmpty {
            return .init(
                content: [.text("No results found for '\(query)'")],
                isError: true
            )
        }

        let json = try JSONEncoder().encode(results)
        return .init(
            content: [.text(String(data: json, encoding: .utf8)!)],
            isError: false
        )

    default:
        return .init(
            content: [.text("Unknown tool: \(params.name)")],
            isError: true
        )
    }
}
```

## JSON Schema with Value Type

Build schemas using the `Value` enum:

```swift
let schema = Value.object([
    "type": .string("object"),
    "properties": .object([
        "name": .object([
            "type": .string("string"),
            "description": .string("User's name")
        ]),
        "age": .object([
            "type": .string("integer"),
            "minimum": .number(0),
            "maximum": .number(150)
        ]),
        "email": .object([
            "type": .string("string"),
            "format": .string("email")
        ])
    ]),
    "required": .array([.string("name"), .string("email")])
])
```

## Resource Implementation

```swift
await server.withMethodHandler(ListResources.self) { _ in
    .init(resources: [
        Resource(
            name: "App Config",
            uri: "config://app/settings",
            description: "Current application configuration",
            mimeType: "application/json"
        )
    ], nextCursor: nil)
}

await server.withMethodHandler(ReadResource.self) { params in
    switch params.uri {
    case "config://app/settings":
        let content = try await loadSettings()
        return .init(contents: [
            Resource.Content.text(content, uri: params.uri, mimeType: "application/json")
        ])
    default:
        throw MCPError.invalidParams("Unknown resource URI: \(params.uri)")
    }
}
```

## Prompt Implementation

```swift
await server.withMethodHandler(ListPrompts.self) { _ in
    .init(prompts: [
        Prompt(
            name: "analyze",
            description: "Analyze a topic in depth",
            arguments: [
                .init(name: "topic", description: "Topic to analyze", required: true),
                .init(name: "depth", description: "Analysis depth", required: false)
            ]
        )
    ], nextCursor: nil)
}

await server.withMethodHandler(GetPrompt.self) { params in
    let topic = params.arguments?["topic"]?.stringValue ?? "general"
    let depth = params.arguments?["depth"]?.stringValue ?? "basic"

    return .init(
        description: "Analysis of \(topic)",
        messages: [
            .user("Please analyze this topic: \(topic) at \(depth) depth")
        ]
    )
}
```

## Transport Configuration

### stdio (local, default)

```swift
import MCP
import Logging

let logger = Logger(label: "com.example.service-mcp")
let transport = StdioTransport(logger: logger)
try await server.start(transport: transport)
```

### HTTP Transport (client side)

```swift
let transport = HTTPClientTransport(
    endpoint: URL(string: "http://localhost:8080")!,
    streaming: true
)
try await client.connect(transport: transport)
```

## Concurrency and Actors

The server is an actor, ensuring thread-safe access. Use additional actors for shared state:

```swift
actor ServerState {
    private var subscriptions: Set<String> = []

    func addSubscription(_ uri: String) { subscriptions.insert(uri) }
    func getSubscriptions() -> Set<String> { subscriptions }
}

let state = ServerState()

await server.withMethodHandler(ResourceSubscribe.self) { params in
    await state.addSubscription(params.uri)
    return .init()
}
```

## Error Handling

Use Swift's error handling with `MCPError`:

```swift
await server.withMethodHandler(CallTool.self) { params in
    do {
        guard let query = params.arguments?["query"]?.stringValue else {
            throw MCPError.invalidParams("Missing required parameter: query")
        }

        let result = try await performOperation(query: query)
        return .init(content: [.text(result)], isError: false)
    } catch let error as MCPError {
        return .init(content: [.text(error.localizedDescription)], isError: true)
    } catch {
        return .init(content: [.text("Unexpected error: \(error.localizedDescription)")], isError: true)
    }
}
```

## Graceful Shutdown with ServiceLifecycle

```swift
import ServiceLifecycle

struct MCPService: Service {
    let server: Server
    let transport: Transport

    func run() async throws {
        try await server.start(transport: transport)
        try await Task.sleep(for: .days(365 * 100))
    }
}

let serviceGroup = ServiceGroup(
    services: [MCPService(server: server, transport: transport)],
    configuration: .init(gracefulShutdownSignals: [.sigterm, .sigint]),
    logger: logger
)
try await serviceGroup.run()
```

## Swift Package Manager Setup

```swift
// swift-tools-version: 6.0
import PackageDescription

let package = Package(
    name: "{Service}MCP",
    platforms: [.macOS(.v13), .iOS(.v16)],
    dependencies: [
        .package(url: "https://github.com/modelcontextprotocol/swift-sdk.git", from: "0.10.0"),
        .package(url: "https://github.com/apple/swift-log.git", from: "1.5.0")
    ],
    targets: [
        .executableTarget(
            name: "{Service}MCP",
            dependencies: [
                .product(name: "MCP", package: "swift-sdk"),
                .product(name: "Logging", package: "swift-log")
            ]
        )
    ]
)
```

## Complete Example

```swift
import MCP
import Logging

@main
struct ExampleMCP {
    static func main() async throws {
        let logger = Logger(label: "com.example.mcp")

        let server = Server(
            name: "example-mcp",
            version: "1.0.0",
            capabilities: .init(tools: .init(listChanged: true))
        )

        let listReposTool = Tool(
            name: "list_repos",
            description: "List repositories for an owner. Returns name and star count.",
            inputSchema: .object([
                "properties": .object([
                    "owner": .object([
                        "type": .string("string"),
                        "description": .string("GitHub org or username")
                    ])
                ]),
                "required": .array([.string("owner")])
            ])
        )

        await server.withMethodHandler(ListTools.self) { _ in
            .init(tools: [listReposTool])
        }

        await server.withMethodHandler(CallTool.self) { params in
            switch params.name {
            case "list_repos":
                let owner = params.arguments?["owner"]?.stringValue ?? ""
                return .init(
                    content: [.text("Repos for \(owner): [example-repo (42 stars)]")],
                    isError: false
                )
            default:
                return .init(content: [.text("Unknown tool")], isError: true)
            }
        }

        let transport = StdioTransport(logger: logger)
        try await server.start(transport: transport)
    }
}
```

---

## Quality Checklist

Before finalizing your Swift MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names reflect natural task subdivisions with service prefix
- [ ] Error messages guide agents toward correct usage

### Implementation Quality
- [ ] All tools registered via `withMethodHandler(ListTools.self)` and `withMethodHandler(CallTool.self)`
- [ ] Tool `inputSchema` uses `Value` type with proper property types and descriptions
- [ ] `required` arrays list all mandatory parameters
- [ ] Error responses use `isError: true` with actionable messages
- [ ] All handlers are `async` and use `await` for I/O

### Swift Quality
- [ ] Uses Swift concurrency (`async`/`await`) throughout
- [ ] Actor isolation used for shared mutable state
- [ ] Proper `do`/`catch` error handling in all handlers
- [ ] No force-unwraps in production paths
- [ ] Logging via `swift-log` to stderr (not stdout)

### Project Configuration
- [ ] Package.swift targets macOS 13+ / iOS 16+
- [ ] `swift-sdk` and `swift-log` dependencies declared
- [ ] `swift build` succeeds with no errors
- [ ] Server name follows format: `{service}-mcp`

### Testing
- [ ] `swift build` compiles without errors
- [ ] `swift test` passes
- [ ] Manual test with MCP Inspector: `npx @modelcontextprotocol/inspector swift run`
