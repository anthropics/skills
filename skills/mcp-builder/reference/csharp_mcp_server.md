# C#/.NET MCP Server Implementation Guide

## Overview

This guide provides C#/.NET-specific patterns and conventions for building MCP servers using the official MCP C# SDK. It covers project structure, attribute-based tool registration, dependency injection, transport configuration, error handling, and complete working examples.

## Quick Reference

### Key Imports

```csharp
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using ModelContextProtocol.Server;
using System.ComponentModel;
using System.Text.Json;
```

### Server Initialization

```csharp
var builder = Host.CreateApplicationBuilder(args);
builder.Logging.AddConsole(o => o.LogToStandardErrorThreshold = LogLevel.Trace);
builder.Services.AddMcpServer().WithStdioServerTransport().WithToolsFromAssembly();
await builder.Build().RunAsync();
```

### Tool Registration Pattern

```csharp
[McpServerToolType]
public static class ServiceTools
{
    [McpServerTool(Name = "service_action"), Description("What it does")]
    public static async Task<string> ActionMethod(
        [Description("Param description")] string param,
        CancellationToken ct = default)
    {
        return JsonSerializer.Serialize(result);
    }
}
```

## MCP C# SDK

The official MCP C# SDK provides attribute-based tool registration with full .NET host integration:

- **NuGet packages**: `ModelContextProtocol` (main), `ModelContextProtocol.AspNetCore` (HTTP/SSE), `ModelContextProtocol.Core` (minimal)
- Uses `[McpServerTool]` and `[McpServerToolType]` attributes for tool registration
- Integrates with `Microsoft.Extensions.Hosting` for lifecycle management
- Supports dependency injection natively via method parameter injection
- Target .NET 9+

**Use Modern APIs Only:**
- Use `[McpServerTool]` attribute, `[McpServerToolType]` attribute, `WithToolsFromAssembly()`
- Use `AddMcpServer()` with fluent configuration
- The attribute-based approach provides automatic schema generation and assembly scanning

## Server Naming Convention

All MCP servers follow a consistent naming pattern:
- **Format**: `{service}-mcp-server` (lowercase with hyphens)
- **Examples**: `github-mcp-server`, `jira-mcp-server`, `stripe-mcp-server`

The name should be general (not tied to specific features), descriptive of the service being integrated, easy to infer from the task description, and without version numbers or dates. The NuGet package name should match the server name.

## Project Structure

```
{Service}McpServer/
+-- {Service}McpServer.csproj
+-- Program.cs
+-- Tools/
|   +-- UserTools.cs
|   +-- ProjectTools.cs
+-- Services/
|   +-- ApiClient.cs
+-- Models/
|   +-- User.cs
+-- Constants.cs
+-- .mcp/
    +-- server.json
```

## Tool Implementation

### Tool Naming

Use snake_case for tool names via the `Name` property (e.g., `Name = "search_users"`, `Name = "create_project"`) with clear, action-oriented names. C# method names remain PascalCase per .NET convention.

**Avoid naming conflicts** by including the service context:
- `Name = "slack_send_message"` instead of `"send_message"`
- `Name = "github_create_issue"` instead of `"create_issue"`
- `Name = "asana_list_tasks"` instead of `"list_tasks"`

### Tool Structure

Tools are defined using `[McpServerToolType]` on the class and `[McpServerTool]` on each method, with `[Description]` attributes for documentation:

```csharp
using System.ComponentModel;
using System.Net.Http.Json;
using System.Text.Json;
using ModelContextProtocol.Server;

[McpServerToolType]
public static class UserTools
{
    private static readonly JsonSerializerOptions JsonOptions = new() { WriteIndented = true };

    [McpServerTool(Name = "example_search_users"), Description(
        """
        Search for users in the Example system by name, email, or team.

        This tool searches across all user profiles. It does NOT create or
        modify users, only searches existing ones.

        Args:
          - query (string): Search string to match against names/emails (min 2 chars)
          - limit (int): Maximum results to return, 1-100 (default: 20)
          - offset (int): Number of results to skip for pagination (default: 0)

        Returns:
          JSON with total, count, offset, users array, has_more, next_offset

        Examples:
          - "Find marketing team members" -> query="team:marketing"
          - "Search for John" -> query="john"
        """)]
    public static async Task<string> SearchUsers(
        IHttpClientFactory httpClientFactory,
        [Description("Search string to match against names/emails (min 2 chars)")] string query,
        [Description("Maximum results to return (1-100, default: 20)")] int limit = 20,
        [Description("Number of results to skip for pagination (default: 0)")] int offset = 0,
        CancellationToken ct = default)
    {
        if (query.Length < 2)
            return "Error: Query must be at least 2 characters.";

        limit = Math.Clamp(limit, 1, 100);
        offset = Math.Max(0, offset);

        try
        {
            var client = httpClientFactory.CreateClient("ExampleApi");
            var data = await client.GetFromJsonAsync<SearchResult>(
                $"users/search?q={Uri.EscapeDataString(query)}&limit={limit}&offset={offset}", ct);

            if (data?.Users is not { Count: > 0 })
                return $"No users found matching '{query}'";

            var result = new
            {
                total = data.Total,
                count = data.Users.Count,
                offset,
                users = data.Users,
                has_more = data.Total > offset + data.Users.Count,
                next_offset = data.Total > offset + data.Users.Count
                    ? offset + data.Users.Count
                    : (int?)null
            };

            return JsonSerializer.Serialize(result, JsonOptions);
        }
        catch (HttpRequestException ex)
        {
            return HandleApiError(ex);
        }
    }

    private static string HandleApiError(HttpRequestException ex) => ex.StatusCode switch
    {
        System.Net.HttpStatusCode.NotFound =>
            "Error: Resource not found. Please check the ID is correct.",
        System.Net.HttpStatusCode.Forbidden =>
            "Error: Permission denied. You don't have access to this resource.",
        (System.Net.HttpStatusCode)429 =>
            "Error: Rate limit exceeded. Please wait before making more requests.",
        _ => $"Error: API request failed with status {ex.StatusCode}"
    };
}
```

## Descriptions

Two approaches for providing tool and parameter descriptions:

### [Description] Attribute (Recommended)

```csharp
[McpServerTool(Name = "service_get_user"), Description("Get user details by ID")]
public static async Task<string> GetUser(
    [Description("The user ID (e.g., 'U123456')")] string userId,
    CancellationToken ct = default)
{
    // ...
}
```

### XML Comments on Partial Methods

```csharp
/// <summary>Get user details by ID</summary>
/// <param name="userId">The user ID (e.g., 'U123456')</param>
[McpServerTool(Name = "service_get_user")]
public static partial Task<string> GetUser(string userId, CancellationToken ct = default);
```

XML comments auto-generate `[Description]` attributes when methods are `partial`. This keeps descriptions close to the code and enables IDE tooltips.

## Dependency Injection

C# has native DI support through `Microsoft.Extensions.DependencyInjection`, a significant advantage over TypeScript and Python MCP servers. Services registered in `Program.cs` are automatically injected as tool method parameters without any manual wiring.

```csharp
// Program.cs
builder.Services.AddHttpClient("ExampleApi", client =>
{
    client.BaseAddress = new Uri(
        Environment.GetEnvironmentVariable("API_BASE_URL") ?? "https://api.example.com/v1/");
    client.DefaultRequestHeaders.Add("Accept", "application/json");
    client.Timeout = TimeSpan.FromSeconds(30);
});
builder.Services.AddSingleton<ICacheService, RedisCacheService>();

// Tools/DataTools.cs
[McpServerTool(Name = "service_get_data"), Description("Get cached data")]
public static async Task<string> GetData(
    IHttpClientFactory httpClientFactory,
    ICacheService cache,
    McpServer server,
    [Description("Resource ID")] string id,
    CancellationToken ct = default)
{
    var cached = await cache.GetAsync(id, ct);
    if (cached is not null) return cached;

    var client = httpClientFactory.CreateClient("ExampleApi");
    var result = await client.GetStringAsync($"data/{id}", ct);
    await cache.SetAsync(id, result, ct);
    return result;
}
```

Parameters without `[Description]` are resolved from DI. Parameters with `[Description]` are treated as tool inputs from the caller.

## Response Format Options

Support multiple output formats for flexibility:

```csharp
[McpServerTool(Name = "service_list_users"), Description("List users with format option")]
public static async Task<string> ListUsers(
    IHttpClientFactory httpClientFactory,
    [Description("Output format: 'markdown' or 'json' (default: markdown)")] string responseFormat = "markdown",
    [Description("Max results (1-100, default: 20)")] int limit = 20,
    CancellationToken ct = default)
{
    var users = await FetchUsers(httpClientFactory, limit, ct);

    return responseFormat.ToLowerInvariant() switch
    {
        "json" => JsonSerializer.Serialize(users, new JsonSerializerOptions { WriteIndented = true }),
        _ => FormatAsMarkdown(users)
    };
}

private static string FormatAsMarkdown(List<User> users)
{
    var sb = new StringBuilder();
    sb.AppendLine("# Users");
    sb.AppendLine();
    foreach (var user in users)
    {
        sb.AppendLine($"## {user.Name} ({user.Id})");
        sb.AppendLine($"- **Email**: {user.Email}");
        if (user.Team is not null) sb.AppendLine($"- **Team**: {user.Team}");
        sb.AppendLine();
    }
    return sb.ToString();
}
```

**Markdown**: Use headers, lists, and formatting for clarity. Convert timestamps to human-readable format. Show display names with IDs in parentheses. Group related information logically.

**JSON**: Return complete, structured data suitable for programmatic processing. Include all available fields and metadata. Use consistent field names and types.

## Pagination Implementation

```csharp
[McpServerTool(Name = "service_list_items"), Description("List items with pagination")]
public static async Task<string> ListItems(
    IHttpClientFactory httpClientFactory,
    [Description("Max results (1-100, default: 20)")] int limit = 20,
    [Description("Results to skip (default: 0)")] int offset = 0,
    CancellationToken ct = default)
{
    limit = Math.Clamp(limit, 1, 100);
    offset = Math.Max(0, offset);

    var data = await FetchItems(httpClientFactory, limit, offset, ct);

    var response = new
    {
        total = data.Total,
        count = data.Items.Count,
        offset,
        items = data.Items,
        has_more = data.Total > offset + data.Items.Count,
        next_offset = data.Total > offset + data.Items.Count
            ? offset + data.Items.Count
            : (int?)null
    };

    return JsonSerializer.Serialize(response, new JsonSerializerOptions { WriteIndented = true });
}
```

## Character Limits and Truncation

Define a constant to prevent overwhelming responses:

```csharp
public static class Constants
{
    public const int CharacterLimit = 25000;
}
```

Apply truncation in tool implementations:

```csharp
var options = new JsonSerializerOptions { WriteIndented = true };
var result = JsonSerializer.Serialize(data, options);

if (result.Length > Constants.CharacterLimit)
{
    var truncated = data.Take(data.Count / 2).ToList();
    var response = new
    {
        data = truncated,
        truncated = true,
        truncation_message =
            $"Response truncated from {data.Count} to {truncated.Count} items. " +
            "Use 'offset' parameter or add filters to see more results."
    };
    result = JsonSerializer.Serialize(response, options);
}
```

## Error Handling

Use two levels of error handling to distinguish protocol errors from tool errors:

```csharp
// Protocol-level errors (invalid params, unknown tool) -- throw exceptions
throw new McpException("Missing required argument 'id'");

// Tool-level errors (API failures, validation) -- return as content
private static string HandleApiError(Exception error) => error switch
{
    HttpRequestException { StatusCode: System.Net.HttpStatusCode.NotFound } =>
        "Error: Resource not found. Please check the ID is correct.",
    HttpRequestException { StatusCode: System.Net.HttpStatusCode.Forbidden } =>
        "Error: Permission denied. You don't have access to this resource.",
    HttpRequestException { StatusCode: (System.Net.HttpStatusCode)429 } =>
        "Error: Rate limit exceeded. Please wait before making more requests.",
    HttpRequestException ex =>
        $"Error: API request failed with status {ex.StatusCode}",
    TaskCanceledException =>
        "Error: Request timed out. Please try again.",
    _ => $"Error: Unexpected error occurred: {error.Message}"
};
```

Tool-level errors should be returned as string content so the LLM can reason about them. Protocol-level errors (malformed requests) should throw exceptions.

## Shared Utilities

Extract common functionality into DI-registered services:

```csharp
// Services/ApiClient.cs
public class ApiClient(IHttpClientFactory httpClientFactory)
{
    public async Task<T?> GetAsync<T>(string endpoint, CancellationToken ct = default)
    {
        var client = httpClientFactory.CreateClient("ServiceApi");
        var response = await client.GetAsync(endpoint, ct);
        response.EnsureSuccessStatusCode();
        return await response.Content.ReadFromJsonAsync<T>(cancellationToken: ct);
    }

    public async Task<T?> PostAsync<T>(string endpoint, object data, CancellationToken ct = default)
    {
        var client = httpClientFactory.CreateClient("ServiceApi");
        var response = await client.PostAsJsonAsync(endpoint, data, ct);
        response.EnsureSuccessStatusCode();
        return await response.Content.ReadFromJsonAsync<T>(cancellationToken: ct);
    }
}

// Program.cs
builder.Services.AddSingleton<ApiClient>();
builder.Services.AddHttpClient("ServiceApi", client =>
{
    client.BaseAddress = new Uri(
        Environment.GetEnvironmentVariable("API_BASE_URL")
        ?? throw new InvalidOperationException("API_BASE_URL environment variable is not set"));
    client.DefaultRequestHeaders.Add("Accept", "application/json");
    client.Timeout = TimeSpan.FromSeconds(30);
});
```

## Async/Await Best Practices

All tool methods performing I/O must use async/await with `CancellationToken`:

```csharp
[McpServerTool(Name = "service_fetch"), Description("Fetch resource by ID")]
public static async Task<string> FetchResource(
    IHttpClientFactory factory,
    [Description("Resource ID")] string id,
    CancellationToken ct = default)
{
    var client = factory.CreateClient("ServiceApi");
    var response = await client.GetAsync($"resource/{id}", ct);
    response.EnsureSuccessStatusCode();
    return await response.Content.ReadAsStringAsync(ct);
}
```

Rules:
- Always pass `CancellationToken` through to async operations
- Never use `.Result` or `.Wait()` -- these cause deadlocks in hosted environments
- Never instantiate `HttpClient` directly -- use `IHttpClientFactory` to avoid socket exhaustion
- Use `ConfigureAwait(false)` in library code but not in tool methods

## C# Best Practices

1. **No `dynamic`** -- Use strongly typed models or `JsonElement` for unknown shapes
2. **Nullable reference types** -- Enable `<Nullable>enable</Nullable>` in .csproj
3. **Pattern matching** -- Use `switch` expressions for error handling and branching
4. **Raw string literals** -- Use `"""..."""` for multi-line descriptions
5. **`IHttpClientFactory`** -- Never `new HttpClient()` directly (socket exhaustion)
6. **`CancellationToken`** -- Accept on all async tool methods as the last parameter
7. **Source-generated JSON** -- Use `JsonSerializerContext` for AOT compatibility
8. **Record types** -- Use for immutable DTOs: `public record User(string Id, string Name);`
9. **Primary constructors** -- Use for DI in service classes: `public class ApiClient(IHttpClientFactory factory)`
10. **File-scoped namespaces** -- Use `namespace Foo;` instead of `namespace Foo { ... }`

```csharp
public record User(string Id, string Name, string Email, string? Team = null);
public record SearchResult(int Total, List<User> Users);

async Task<string> GetUser(string id, CancellationToken ct)
{
    var user = await client.GetFromJsonAsync<User>($"users/{id}", ct);
    return user is not null
        ? JsonSerializer.Serialize(user, options)
        : "Error: User not found.";
}
```

## Logging

**CRITICAL**: For stdio transport, all logs must go to stderr. stdout is reserved for MCP protocol messages -- logging to stdout breaks the protocol.

```csharp
builder.Logging.AddConsole(options =>
{
    options.LogToStandardErrorThreshold = LogLevel.Trace;
});
```

Inject `ILogger` into tool methods via DI for structured logging:

```csharp
[McpServerTool(Name = "service_process"), Description("Process data")]
public static async Task<string> ProcessData(
    ILogger<ServiceTools> logger,
    [Description("Data ID")] string id,
    CancellationToken ct = default)
{
    logger.LogInformation("Processing data {Id}", id);
    // ...
}
```

## McpServer Injection (Sampling)

Tools can request the `McpServer` instance via DI to make sampling requests back to the client. This enables server-initiated LLM calls for tasks like summarization:

```csharp
[McpServerTool(Name = "service_summarize"), Description("Summarize content from URL")]
public static async Task<string> SummarizeContent(
    McpServer server,
    IHttpClientFactory factory,
    [Description("URL to fetch and summarize")] string url,
    CancellationToken ct = default)
{
    var client = factory.CreateClient();
    var content = await client.GetStringAsync(url, ct);

    ChatMessage[] messages = [
        new(ChatRole.User, "Briefly summarize:"),
        new(ChatRole.User, content),
    ];

    var response = await server.AsSamplingChatClient()
        .GetResponseAsync(messages, new() { MaxOutputTokens = 256 }, ct);

    return $"Summary: {response}";
}
```

## Package Configuration

### .csproj

```xml
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <OutputType>Exe</OutputType>
    <TargetFramework>net9.0</TargetFramework>
    <Nullable>enable</Nullable>
    <ImplicitUsings>enable</ImplicitUsings>
  </PropertyGroup>

  <ItemGroup>
    <PackageReference Include="ModelContextProtocol" Version="*-*" />
    <PackageReference Include="Microsoft.Extensions.Hosting" Version="9.*" />
  </ItemGroup>

  <!-- Optional: Container publishing -->
  <PropertyGroup>
    <EnableSdkContainerSupport>true</EnableSdkContainerSupport>
    <ContainerRepository>myorg/service-mcp-server</ContainerRepository>
    <ContainerFamily>alpine</ContainerFamily>
  </PropertyGroup>
</Project>
```

### Publishing Options

```bash
# NuGet package
dotnet pack -c Release

# Container image
dotnet publish /t:PublishContainer -c Release

# Container to registry
dotnet publish /t:PublishContainer -p ContainerRegistry=docker.io

# Native AOT (smaller, faster startup)
dotnet publish -c Release -r linux-x64 --self-contained /p:PublishAot=true
```

### NuGet MCP Server Metadata

Create `.mcp/server.json` for discoverability:

```json
{
  "name": "service-mcp-server",
  "version": "1.0.0",
  "description": "MCP server for Service API",
  "transport": "stdio"
}
```

## HTTP/SSE Transport

For servers that require HTTP transport instead of stdio:

```csharp
using ModelContextProtocol.AspNetCore;

var builder = WebApplication.CreateBuilder(args);
builder.Services.AddMcpServer().WithToolsFromAssembly();
var app = builder.Build();
app.MapMcp();
app.Run();
```

Requires the `ModelContextProtocol.AspNetCore` NuGet package. The `MapMcp()` extension method registers the Streamable HTTP endpoint.

## Code Best Practices

### Composability

Structure tool classes by domain so they can be composed independently:

```csharp
// Tools/UserTools.cs
[McpServerToolType]
public static class UserTools { /* user-related tools */ }

// Tools/ProjectTools.cs
[McpServerToolType]
public static class ProjectTools { /* project-related tools */ }
```

`WithToolsFromAssembly()` discovers all `[McpServerToolType]` classes automatically. For selective registration, use `WithTools<UserTools>()` to include specific tool classes.

### Code Reuse

Extract shared logic into DI services rather than duplicating across tool classes:

```csharp
public class PaginationHelper
{
    public static (int limit, int offset) Clamp(int limit, int offset)
        => (Math.Clamp(limit, 1, 100), Math.Max(0, offset));

    public static object BuildResponse<T>(List<T> items, int total, int offset) => new
    {
        total,
        count = items.Count,
        offset,
        items,
        has_more = total > offset + items.Count,
        next_offset = total > offset + items.Count ? offset + items.Count : (int?)null
    };
}
```

## Advanced MCP Features

### Resource Registration

The MCP C# SDK supports resource registration through attributes, following the same pattern as tools. Consult the SDK documentation for the latest resource registration APIs as this area is under active development.

### Transport Options

| Transport | Use Case | Entry Point |
|-----------|----------|-------------|
| **stdio** | CLI tools, local processes | `WithStdioServerTransport()` |
| **HTTP/SSE** | Web services, remote access | `MapMcp()` via ASP.NET Core |

stdio is the default for most MCP servers. Use HTTP/SSE when the server must be accessible over the network or integrated into an existing web application.

## Complete Example

A fully working MCP server with search, get, and create operations:

```csharp
// Program.cs
using Microsoft.Extensions.DependencyInjection;
using Microsoft.Extensions.Hosting;
using Microsoft.Extensions.Logging;
using ModelContextProtocol.Server;
using System.ComponentModel;
using System.Net.Http.Json;
using System.Text;
using System.Text.Json;

var builder = Host.CreateApplicationBuilder(args);
builder.Logging.AddConsole(o => o.LogToStandardErrorThreshold = LogLevel.Trace);

builder.Services.AddHttpClient("ExampleApi", client =>
{
    client.BaseAddress = new Uri(
        Environment.GetEnvironmentVariable("EXAMPLE_API_URL") ?? "https://api.example.com/v1/");
    client.DefaultRequestHeaders.Add("Accept", "application/json");
    client.Timeout = TimeSpan.FromSeconds(30);
});

builder.Services
    .AddMcpServer()
    .WithStdioServerTransport()
    .WithToolsFromAssembly();

await builder.Build().RunAsync();

// Models/User.cs
public record User(string Id, string Name, string Email, string? Team = null);
public record SearchResult(int Total, List<User> Users);

// Tools/ExampleTools.cs
[McpServerToolType]
public static class ExampleTools
{
    private const int CharacterLimit = 25000;
    private static readonly JsonSerializerOptions JsonOptions = new() { WriteIndented = true };

    [McpServerTool(Name = "example_search_users"), Description(
        """
        Search for users in the Example system by name, email, or team.

        This tool searches across all user profiles. It does NOT create or
        modify users, only searches existing ones.

        Args:
          - query (string): Search string (min 2 chars)
          - limit (int): Max results 1-100 (default: 20)
          - offset (int): Skip results for pagination (default: 0)
          - responseFormat (string): 'markdown' or 'json' (default: markdown)

        Returns:
          Search results with total count, user details, and pagination info.
        """)]
    public static async Task<string> SearchUsers(
        IHttpClientFactory httpClientFactory,
        [Description("Search query (min 2 chars)")] string query,
        [Description("Max results 1-100 (default: 20)")] int limit = 20,
        [Description("Skip results (default: 0)")] int offset = 0,
        [Description("Output format: 'markdown' or 'json' (default: markdown)")] string responseFormat = "markdown",
        CancellationToken ct = default)
    {
        if (query.Length < 2)
            return "Error: Query must be at least 2 characters.";

        limit = Math.Clamp(limit, 1, 100);
        offset = Math.Max(0, offset);

        try
        {
            var client = httpClientFactory.CreateClient("ExampleApi");
            var data = await client.GetFromJsonAsync<SearchResult>(
                $"users/search?q={Uri.EscapeDataString(query)}&limit={limit}&offset={offset}", ct);

            if (data?.Users is not { Count: > 0 })
                return $"No users found matching '{query}'";

            var output = new
            {
                total = data.Total,
                count = data.Users.Count,
                offset,
                users = data.Users,
                has_more = data.Total > offset + data.Users.Count,
                next_offset = data.Total > offset + data.Users.Count
                    ? offset + data.Users.Count
                    : (int?)null
            };

            if (responseFormat.Equals("json", StringComparison.OrdinalIgnoreCase))
                return Truncate(JsonSerializer.Serialize(output, JsonOptions));

            var sb = new StringBuilder();
            sb.AppendLine($"# User Search Results: '{query}'");
            sb.AppendLine();
            sb.AppendLine($"Found {data.Total} users (showing {data.Users.Count})");
            sb.AppendLine();
            foreach (var user in data.Users)
            {
                sb.AppendLine($"## {user.Name} ({user.Id})");
                sb.AppendLine($"- **Email**: {user.Email}");
                if (user.Team is not null)
                    sb.AppendLine($"- **Team**: {user.Team}");
                sb.AppendLine();
            }
            if (output.has_more)
                sb.AppendLine($"_More results available. Use offset={output.next_offset} to see next page._");

            return sb.ToString();
        }
        catch (HttpRequestException ex)
        {
            return HandleError(ex);
        }
    }

    [McpServerTool(Name = "example_get_user"), Description(
        """
        Get detailed information about a specific user by their ID.

        Args:
          - userId (string): The user ID (e.g., 'U123456')

        Returns:
          JSON with user details including id, name, email, and team.
        """)]
    public static async Task<string> GetUser(
        IHttpClientFactory httpClientFactory,
        [Description("User ID (e.g., 'U123456')")] string userId,
        CancellationToken ct = default)
    {
        try
        {
            var client = httpClientFactory.CreateClient("ExampleApi");
            var user = await client.GetFromJsonAsync<User>(
                $"users/{Uri.EscapeDataString(userId)}", ct);
            return JsonSerializer.Serialize(user, JsonOptions);
        }
        catch (HttpRequestException ex)
        {
            return HandleError(ex);
        }
    }

    [McpServerTool(Name = "example_create_user"), Description(
        """
        Create a new user in the Example system.

        Args:
          - name (string): User's full name (required)
          - email (string): User's email address (required)
          - team (string): Team assignment (optional)

        Returns:
          JSON with the created user including their generated ID.
        """)]
    public static async Task<string> CreateUser(
        IHttpClientFactory httpClientFactory,
        [Description("User's full name")] string name,
        [Description("User's email address")] string email,
        [Description("Team assignment (optional)")] string? team = null,
        CancellationToken ct = default)
    {
        if (string.IsNullOrWhiteSpace(name))
            return "Error: Name is required.";
        if (string.IsNullOrWhiteSpace(email) || !email.Contains('@'))
            return "Error: A valid email address is required.";

        try
        {
            var client = httpClientFactory.CreateClient("ExampleApi");
            var payload = new { name, email, team };
            var response = await client.PostAsJsonAsync("users", payload, ct);
            response.EnsureSuccessStatusCode();

            var created = await response.Content.ReadFromJsonAsync<User>(cancellationToken: ct);
            return JsonSerializer.Serialize(created, JsonOptions);
        }
        catch (HttpRequestException ex)
        {
            return HandleError(ex);
        }
    }

    private static string HandleError(HttpRequestException ex) => ex.StatusCode switch
    {
        System.Net.HttpStatusCode.NotFound =>
            "Error: Resource not found. Please check the ID is correct.",
        System.Net.HttpStatusCode.Forbidden =>
            "Error: Permission denied. You don't have access to this resource.",
        System.Net.HttpStatusCode.Unauthorized =>
            "Error: Invalid API authentication. Check your API key.",
        (System.Net.HttpStatusCode)429 =>
            "Error: Rate limit exceeded. Please wait before making more requests.",
        _ => $"Error: API request failed with status {ex.StatusCode}"
    };

    private static string Truncate(string result)
    {
        if (result.Length <= CharacterLimit) return result;

        var response = new
        {
            truncated = true,
            truncation_message = "Response exceeded character limit and was truncated. " +
                "Use 'offset' parameter or add filters to see more results."
        };
        return JsonSerializer.Serialize(response, JsonOptions);
    }
}
```

## Quality Checklist

### Strategic Design

- [ ] Server name follows `{service}-mcp-server` format
- [ ] Tool names are `snake_case` with service prefix via `Name = "..."`
- [ ] Tool descriptions document args, return values, and examples
- [ ] Response format options (JSON + Markdown) where applicable
- [ ] Pagination on list/search tools (`limit`, `offset`, `has_more`)
- [ ] `CharacterLimit` constant with truncation handling

### Implementation Quality

- [ ] Uses `[McpServerToolType]` on tool classes and `[McpServerTool]` on methods
- [ ] All tools have `[Description]` on both method and parameters
- [ ] Input validation with clear error messages
- [ ] Centralized error handling (no leaked internals or stack traces)
- [ ] Tool-level errors returned as content, protocol errors thrown as exceptions

### C# Quality

- [ ] DI for services (`IHttpClientFactory`, not `new HttpClient()`)
- [ ] `CancellationToken` on all async tool methods
- [ ] No `dynamic` types -- use strongly typed models or records
- [ ] Nullable reference types enabled (`<Nullable>enable</Nullable>`)
- [ ] Record types for DTOs, primary constructors for services
- [ ] No `.Result` or `.Wait()` calls on tasks

### Advanced Features

- [ ] `McpServer` injection for sampling where applicable
- [ ] Appropriate transport selected (stdio vs HTTP/SSE)
- [ ] `Microsoft.Extensions.Hosting` for lifecycle management

### Project Configuration

- [ ] .csproj targets .NET 9+
- [ ] Container or NuGet publishing configured
- [ ] `.mcp/server.json` metadata for discoverability
- [ ] API keys from environment variables, never hardcoded

### Code Quality

- [ ] Shared utilities extracted into DI services
- [ ] Tool classes organized by domain
- [ ] Consistent `JsonSerializerOptions` usage

### Testing and Build

- [ ] Logging to stderr (`LogToStandardErrorThreshold = LogLevel.Trace`)
- [ ] `AddMcpServer()` with appropriate transport configured
- [ ] Server builds and runs without errors