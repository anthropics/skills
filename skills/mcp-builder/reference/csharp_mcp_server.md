# C# MCP Server Implementation Guide

## Overview

This document provides C#-specific best practices and examples for implementing MCP servers using the official `ModelContextProtocol` NuGet package. It covers attribute-based tool registration, dependency injection, transport configuration, and complete working examples.

---

## Quick Reference

### Key Package
```bash
dotnet add package ModelContextProtocol --prerelease
```

### Server Initialization
```csharp
var builder = Host.CreateApplicationBuilder(args);
builder.Logging.AddConsole(options =>
    options.LogToStandardErrorThreshold = LogLevel.Trace);
builder.Services
    .AddMcpServer()
    .WithStdioServerTransport()
    .WithToolsFromAssembly();
await builder.Build().RunAsync();
```

### Tool Registration Pattern
```csharp
[McpServerToolType]
public static class MyTools
{
    [McpServerTool, Description("What this tool does")]
    public static string ToolName(
        [Description("Parameter description")] string param) =>
        $"Result: {param}";
}
```

---

## ModelContextProtocol SDK

The official C# SDK provides:
- `[McpServerToolType]` and `[McpServerTool]` attributes for tool registration
- `[McpServerPromptType]` and `[McpServerPrompt]` for prompts
- `WithToolsFromAssembly()` for auto-discovery of all annotated tools
- Full dependency injection support — inject `HttpClient`, `McpServer`, or custom services
- `WithStdioServerTransport()` for local and `ModelContextProtocol.AspNetCore` for HTTP

**Package variants:**
- `ModelContextProtocol` — full server SDK (recommended)
- `ModelContextProtocol.AspNetCore` — HTTP transport for ASP.NET Core
- `ModelContextProtocol.Core` — minimal dependencies for clients or low-level APIs

## Server Naming Convention

C# MCP servers should follow this naming pattern:
- **Format**: `{Service}.Mcp.Server` (PascalCase with dots, .NET convention)
- **Assembly/project name**: `{Service}.Mcp.Server`
- **Server info name**: `{service}-mcp-server` (lowercase with hyphens for MCP protocol)
- **Examples**: project `GitHub.Mcp.Server`, server name `github-mcp-server`

## Project Structure

```
{Service}.Mcp.Server/
├── {Service}.Mcp.Server.csproj
├── Program.cs           # Host builder, DI, transport setup
├── Tools/
│   ├── SearchTools.cs
│   └── ManageTools.cs
├── Prompts/
│   └── AnalyzePrompts.cs
├── Services/
│   └── ApiClient.cs     # HTTP client, auth
└── Tests/
    └── ToolsTests.cs
```

## Tool Implementation

### Simple Tool

```csharp
using System.ComponentModel;
using ModelContextProtocol.Server;

[McpServerToolType]
public static class SearchTools
{
    [McpServerTool, Description("Search for items by query. Returns matching records with ID, name, and status.")]
    public static string ServiceSearch(
        [Description("Search query string")] string query,
        [Description("Maximum results to return (1-100)")] int limit = 20)
    {
        var results = ApiClient.Search(query, limit);
        return JsonSerializer.Serialize(new { total = results.Count, results });
    }
}
```

### Async Tool with Dependency Injection

```csharp
[McpServerToolType]
public static class DataTools
{
    [McpServerTool, Description("Fetch data from a URL. Returns the response body as text.")]
    public static async Task<string> ServiceFetchData(
        HttpClient httpClient,
        [Description("The URL to fetch")] string url,
        CancellationToken cancellationToken) =>
        await httpClient.GetStringAsync(url, cancellationToken);
}
```

### Tool with Sampling (Client LLM)

```csharp
[McpServerToolType]
public static class AnalysisTools
{
    [McpServerTool, Description("Analyze content using the client's LLM capabilities.")]
    public static async Task<string> ServiceAnalyze(
        McpServer server,
        [Description("Content to analyze")] string content,
        CancellationToken cancellationToken)
    {
        var messages = new ChatMessage[]
        {
            new(ChatRole.User, $"Analyze this: {content}")
        };
        return await server.AsSamplingChatClient()
            .GetResponseAsync(messages, cancellationToken: cancellationToken);
    }
}
```

### Tool with Complex Return Types

Tools can return simple types or complex objects (auto-serialized to JSON):

```csharp
[McpServerTool, Description("Get user details by ID. Returns user profile with name, email, and role.")]
public static async Task<UserProfile> ServiceGetUser(
    IUserService userService,
    [Description("User ID")] string userId,
    CancellationToken cancellationToken) =>
    await userService.GetProfileAsync(userId, cancellationToken);
```

## Prompt Implementation

```csharp
[McpServerPromptType]
public static class AnalyzePrompts
{
    [McpServerPrompt, Description("Analyze a topic in depth")]
    public static ChatMessage[] Analyze(
        [Description("Topic to analyze")] string topic,
        [Description("Analysis depth")] string depth = "basic") =>
        new[]
        {
            new ChatMessage(ChatRole.User, $"Please analyze this topic at {depth} depth: {topic}")
        };
}
```

## Transport Configuration

### stdio (local, default)

```csharp
builder.Services
    .AddMcpServer()
    .WithStdioServerTransport()
    .WithToolsFromAssembly();
```

### ASP.NET Core HTTP

```bash
dotnet add package ModelContextProtocol.AspNetCore --prerelease
```

```csharp
var builder = WebApplication.CreateBuilder(args);
builder.Services.AddMcpServer().WithToolsFromAssembly();

var app = builder.Build();
app.MapMcp();
app.Run();
```

## Dependency Injection

Register services in the DI container and inject into tool methods:

```csharp
var builder = Host.CreateApplicationBuilder(args);

// Register services
builder.Services.AddHttpClient();
builder.Services.AddSingleton<IApiClient, ApiClient>();

// Register MCP server
builder.Services
    .AddMcpServer()
    .WithStdioServerTransport()
    .WithToolsFromAssembly();

await builder.Build().RunAsync();
```

## Error Handling

Use `McpProtocolException` for protocol-level errors:

```csharp
[McpServerTool, Description("Get item by ID")]
public static async Task<string> ServiceGetItem(
    IApiClient client,
    [Description("Item ID")] string id,
    CancellationToken ct)
{
    if (string.IsNullOrWhiteSpace(id))
        throw new McpProtocolException(McpErrorCode.InvalidParams, "Item ID cannot be empty");

    var item = await client.GetItemAsync(id, ct)
        ?? throw new McpProtocolException(McpErrorCode.InvalidParams,
            $"Item '{id}' not found — verify the ID; use service_list_items to discover available items");

    return JsonSerializer.Serialize(item);
}
```

## Logging

Always log to stderr to avoid interfering with stdio transport:

```csharp
builder.Logging.AddConsole(options =>
    options.LogToStandardErrorThreshold = LogLevel.Trace);
```

## Fine-Grained Control with McpServerOptions

For advanced scenarios, use custom handlers:

```csharp
builder.Services.AddMcpServer(options =>
{
    options.ServerInfo = new() { Name = "service-mcp-server", Version = "1.0.0" };
    options.Capabilities = new()
    {
        Tools = new() { ListChanged = true },
        Resources = new() { ListChanged = true }
    };
});
```

## Complete Example

```csharp
using System.ComponentModel;
using System.Text.Json;
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using ModelContextProtocol.Server;

var builder = Host.CreateApplicationBuilder(args);
builder.Logging.AddConsole(options =>
    options.LogToStandardErrorThreshold = LogLevel.Trace);

builder.Services.AddHttpClient();
builder.Services
    .AddMcpServer()
    .WithStdioServerTransport()
    .WithToolsFromAssembly();

await builder.Build().RunAsync();

[McpServerToolType]
public static class RepoTools
{
    [McpServerTool, Description("List repositories for an owner. Returns name, description, and star count.")]
    public static async Task<string> ListRepos(
        HttpClient httpClient,
        [Description("GitHub org or username")] string owner,
        [Description("Results per page (1-100)")] int perPage = 30,
        CancellationToken cancellationToken = default)
    {
        var token = Environment.GetEnvironmentVariable("API_TOKEN")
            ?? throw new InvalidOperationException("API_TOKEN environment variable is required");

        // ... fetch repos ...
        var result = new { repos = new[] { new { name = "example", stars = 42 } }, total = 1 };
        return JsonSerializer.Serialize(result);
    }
}
```

---

## Quality Checklist

Before finalizing your C# MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names are `snake_case` with consistent service prefix (in `[Description]`)
- [ ] Error messages guide agents toward correct usage

### Implementation Quality
- [ ] All tool classes use `[McpServerToolType]` attribute
- [ ] All tool methods use `[McpServerTool]` with `[Description]`
- [ ] All parameters have `[Description]` attributes
- [ ] `CancellationToken` included in async tool methods
- [ ] `McpProtocolException` used for validation errors with `McpErrorCode.InvalidParams`

### C# Quality
- [ ] Uses `Microsoft.Extensions.Hosting` for DI and lifecycle
- [ ] Logging configured to stderr (`LogToStandardErrorThreshold`)
- [ ] Async methods return `Task<T>` with proper `await`
- [ ] No hardcoded credentials — all secrets via `Environment.GetEnvironmentVariable`
- [ ] Services registered in DI container and injected into tool methods

### Project Configuration
- [ ] `.csproj` references `ModelContextProtocol` NuGet package
- [ ] `dotnet build` succeeds with no errors
- [ ] Project name follows format: `{Service}.Mcp.Server`

### Testing
- [ ] `dotnet build` compiles without errors
- [ ] `dotnet test` passes
- [ ] Manual test with MCP Inspector: `npx @modelcontextprotocol/inspector dotnet run`
