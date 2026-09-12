# Go MCP Server Implementation Guide

## Overview

This document provides Go-specific best practices and examples for implementing MCP servers using the official `modelcontextprotocol/go-sdk`. It covers project structure, server setup, tool registration patterns, schema definition with struct tags, error handling, and complete working examples.

---

## Quick Reference

### Key Imports
```go
import (
    "context"
    "fmt"
    "log"

    "github.com/modelcontextprotocol/go-sdk/mcp"
)
```

### Server Initialization
```go
server := mcp.NewServer(&mcp.Implementation{
    Name:    "service-mcp",
    Version: "1.0.0",
}, nil)
```

### Tool Registration Pattern
```go
mcp.AddTool(server, &mcp.Tool{
    Name:        "service_action",
    Description: "What this tool does and returns",
    Annotations: &mcp.ToolAnnotations{ReadOnlyHint: true},
}, handlerFunc)
```

---

## MCP Go SDK

The official Go SDK (`github.com/modelcontextprotocol/go-sdk/mcp`) provides:
- `mcp.NewServer` for server initialization
- `mcp.AddTool` generic function for type-safe tool registration
- Automatic JSON Schema inference from Go struct tags
- `mcp.StdioTransport` and `mcp.NewStreamableHTTPHandler` for transport

**IMPORTANT - Use the Generic API:**
- **DO use**: `mcp.AddTool[In, Out](server, tool, handler)` with typed handler functions
- **DO NOT use**: Low-level request handler registration or manual schema construction (unless you need custom constraints)
- The generic `AddTool` function provides automatic schema inference, type-safe handlers, and input validation before your code runs

## Server Naming Convention

Go MCP servers must follow this naming pattern:
- **Format**: `{service}-mcp` (lowercase with hyphens)
- **Examples**: `github-mcp`, `jira-mcp`, `stripe-mcp`

The name should be:
- General (not tied to specific features)
- Descriptive of the service/API being integrated
- Easy to infer from the task description
- Without version numbers or dates

## Project Structure

Create the following structure for Go MCP servers:

```
{service}-mcp/
├── main.go          # Entry point: wire server, register tools, start transport
├── tools/
│   ├── repos.go     # Tool types and handlers for repository operations
│   └── issues.go    # Tool types and handlers for issue operations
├── client/
│   └── client.go    # HTTP client, auth, base URL config
└── go.mod
```

## Tool Implementation

### Tool Naming

Use snake_case for tool names (e.g., `search_users`, `create_project`, `get_channel_info`) with clear, action-oriented names.

**Avoid Naming Conflicts**: Include the service context to prevent overlaps:
- Use `slack_send_message` instead of just `send_message`
- Use `github_create_issue` instead of just `create_issue`
- Use `asana_list_tasks` instead of just `list_tasks`

### Tool Structure

Tools are registered using the generic `mcp.AddTool` function. The handler signature is:

```go
func(ctx context.Context, req *mcp.CallToolRequest, input In) (*mcp.CallToolResult, Out, error)
```

The SDK automatically:
- Infers the JSON Schema from your `In` struct type
- Validates input against that schema before calling your handler
- Serializes the `Out` value as structured JSON content

```go
// Input type — struct tags define the schema
type UserSearchInput struct {
    Query   string `json:"query"   jsonschema:"Search string to match against names/emails"`
    Limit   *int   `json:"limit,omitempty"   jsonschema:"Maximum results to return (1-100), default 20"`
    Offset  *int   `json:"offset,omitempty"  jsonschema:"Number of results to skip for pagination"`
}

// Output type
type UserSearchOutput struct {
    Total   int           `json:"total"   jsonschema:"Total number of matches found"`
    Count   int           `json:"count"   jsonschema:"Number of results in this response"`
    Users   []UserSummary `json:"users"   jsonschema:"Matching user records"`
    HasMore bool          `json:"hasMore" jsonschema:"Whether more results are available"`
}

type UserSummary struct {
    ID    string `json:"id"`
    Name  string `json:"name"`
    Email string `json:"email"`
    Team  string `json:"team,omitempty"`
}

// Register the tool
mcp.AddTool(server, &mcp.Tool{
    Name: "example_search_users",
    Description: `Search for users in the Example system by name, email, or team.

Returns matching user records with ID, name, email, and team. Supports pagination
via limit and offset parameters. Use example_get_user for full details on a single user.`,
    Annotations: &mcp.ToolAnnotations{
        ReadOnlyHint:   true,
        IdempotentHint: true,
        OpenWorldHint:  mcp.Ptr(true),
    },
}, handleSearchUsers)

// Handler implementation
func handleSearchUsers(ctx context.Context, req *mcp.CallToolRequest, in UserSearchInput) (*mcp.CallToolResult, UserSearchOutput, error) {
    limit := 20
    if in.Limit != nil {
        limit = *in.Limit
    }
    offset := 0
    if in.Offset != nil {
        offset = *in.Offset
    }

    data, err := apiClient.SearchUsers(ctx, in.Query, limit, offset)
    if err != nil {
        return nil, UserSearchOutput{}, fmt.Errorf("searching users for %q: %w", in.Query, err)
    }

    users := data.Users
    if len(users) == 0 {
        return nil, UserSearchOutput{}, fmt.Errorf("no users found matching %q", in.Query)
    }

    return nil, UserSearchOutput{
        Total:   data.Total,
        Count:   len(users),
        Users:   users,
        HasMore: data.Total > offset+len(users),
    }, nil
}
```

## Schema Definition with Struct Tags

### Basic — auto-inferred from struct tags

```go
type Input struct {
    // Non-pointer = required field in the generated schema
    Owner string `json:"owner" jsonschema:"GitHub organization or username"`

    // Pointer = optional field
    PerPage *int    `json:"perPage,omitempty" jsonschema:"Results per page (1-100), default 30"`
    Sort    *string `json:"sort,omitempty"    jsonschema:"Sort field: created, updated, pushed, or full_name"`
}
```

The `jsonschema:"..."` tag value becomes the field's description in the schema.

### Custom constraints — enum, min/max

When you need enum values, numeric ranges, or other constraints, override the schema:

```go
import (
    "reflect"
    "github.com/google/jsonschema-go/jsonschema"
)

type SortField string

const (
    SortCreated  SortField = "created"
    SortUpdated  SortField = "updated"
    SortPushed   SortField = "pushed"
    SortFullName SortField = "full_name"
)

// Build the schema with custom type overrides
inputSchema, err := jsonschema.For[ListReposInput](&jsonschema.ForOptions{
    TypeSchemas: map[reflect.Type]*jsonschema.Schema{
        reflect.TypeFor[SortField](): {
            Type: "string",
            Enum: []any{SortCreated, SortUpdated, SortPushed, SortFullName},
        },
    },
})
if err != nil {
    log.Fatal(err)
}

// Optionally mutate individual properties after inference
inputSchema.Properties["perPage"].Minimum = jsonschema.Ptr(1.0)
inputSchema.Properties["perPage"].Maximum = jsonschema.Ptr(100.0)

// Pass the override when registering the tool
mcp.AddTool(server, &mcp.Tool{
    Name:        "github_list_repos",
    Description: "List repositories for an organization or user.",
    InputSchema: inputSchema,
}, handleListRepos)
```

> Only import `github.com/google/jsonschema-go/jsonschema` when you need schema customization. For most tools, struct tags alone are sufficient.

## Handler Patterns

### Minimal handler (structured output only)

Return `nil` for `*mcp.CallToolResult` — the SDK auto-populates content from your output value as JSON:

```go
func handleListRepos(ctx context.Context, req *mcp.CallToolRequest, in ListReposInput) (*mcp.CallToolResult, ListReposOutput, error) {
    perPage := 30
    if in.PerPage != nil {
        perPage = *in.PerPage
    }

    repos, err := apiClient.ListRepos(ctx, in.Owner, perPage)
    if err != nil {
        return nil, ListReposOutput{}, fmt.Errorf("listing repos for %q: %w", in.Owner, err)
    }
    return nil, ListReposOutput{Repos: repos, Total: len(repos)}, nil
}
```

### Handler with explicit text content

Return a `*mcp.CallToolResult` when you want to control the text shown in the content field:

```go
func handleGetSummary(ctx context.Context, req *mcp.CallToolRequest, in SummaryInput) (*mcp.CallToolResult, any, error) {
    text, err := apiClient.GetSummary(ctx, in.ID)
    if err != nil {
        return nil, nil, fmt.Errorf("getting summary for %q: %w", in.ID, err)
    }
    return &mcp.CallToolResult{
        Content: []mcp.Content{&mcp.TextContent{Text: text}},
    }, nil, nil
}
```

### Handler with no output type

Use `any` as the output type when you have no structured output:

```go
mcp.AddTool(server, &mcp.Tool{Name: "ping", Description: "Check connectivity"},
    func(ctx context.Context, req *mcp.CallToolRequest, _ any) (*mcp.CallToolResult, any, error) {
        return &mcp.CallToolResult{
            Content: []mcp.Content{&mcp.TextContent{Text: "pong"}},
        }, nil, nil
    })
```

## Response and Error Handling

### Tool errors vs protocol errors

| Situation | How to return |
| --------- | ------------- |
| Business/tool error (not found, bad input, API 404) | `return nil, zero, fmt.Errorf("message")` — SDK sets `IsError: true` |
| Explicit tool error with custom content | `return &mcp.CallToolResult{IsError: true, Content: [...]}, zero, nil` |
| Infrastructure/protocol failure (unrecoverable) | `return nil, zero, err` — framework-level error |

**Critical distinction**: returning a non-nil `error` from a handler is treated as a **tool error** — the SDK packs it into `CallToolResult.Content` with `IsError: true`. This is the correct behavior for business logic failures.

### Actionable error messages

```go
// Bad
return nil, out, fmt.Errorf("not found")

// Good
return nil, out, fmt.Errorf("repository %q/%q not found — verify the owner login and repository name; use list_repos to discover available repositories", owner, repo)
```

### Wrapping API errors

```go
repos, err := apiClient.ListRepos(ctx, in.Owner, perPage)
if err != nil {
    var apiErr *APIError
    if errors.As(err, &apiErr) {
        switch apiErr.StatusCode {
        case 404:
            return nil, ListReposOutput{}, fmt.Errorf("owner %q not found", in.Owner)
        case 403:
            return nil, ListReposOutput{}, fmt.Errorf("access denied — check that your API token has the required scopes")
        case 429:
            return nil, ListReposOutput{}, fmt.Errorf("rate limit exceeded — wait before making more requests")
        }
    }
    return nil, ListReposOutput{}, fmt.Errorf("API request failed: %w", err)
}
```

## Shared Utilities

Extract common functionality into reusable packages:

```go
// client/client.go
package client

import (
    "context"
    "encoding/json"
    "fmt"
    "net/http"
    "time"
)

type Client struct {
    token   string
    baseURL string
    http    *http.Client
}

func New(token, baseURL string) *Client {
    return &Client{
        token:   token,
        baseURL: baseURL,
        http:    &http.Client{Timeout: 30 * time.Second},
    }
}

func (c *Client) Do(ctx context.Context, method, endpoint string, body, result any) error {
    // Build request, set auth header, execute, decode response
    req, err := http.NewRequestWithContext(ctx, method, c.baseURL+"/"+endpoint, nil)
    if err != nil {
        return fmt.Errorf("creating request: %w", err)
    }
    req.Header.Set("Authorization", "Bearer "+c.token)
    req.Header.Set("Accept", "application/json")

    resp, err := c.http.Do(req)
    if err != nil {
        return fmt.Errorf("executing request: %w", err)
    }
    defer resp.Body.Close()

    if resp.StatusCode >= 400 {
        return &APIError{StatusCode: resp.StatusCode}
    }

    if result != nil {
        if err := json.NewDecoder(resp.Body).Decode(result); err != nil {
            return fmt.Errorf("decoding response: %w", err)
        }
    }
    return nil
}

type APIError struct {
    StatusCode int
    Message    string
}

func (e *APIError) Error() string {
    return fmt.Sprintf("API %d: %s", e.StatusCode, e.Message)
}
```

## Tool Annotations

Set annotations on `&mcp.Tool{}` via the `Annotations` field:

```go
&mcp.Tool{
    Name:        "delete_repo",
    Description: "Permanently delete a repository. This cannot be undone.",
    Annotations: &mcp.ToolAnnotations{
        ReadOnlyHint:    false,
        DestructiveHint: mcp.Ptr(true),  // *bool fields use mcp.Ptr()
        IdempotentHint:  false,
        OpenWorldHint:   mcp.Ptr(true),
    },
}
```

| Field | Type | Default | When to set |
| ----- | ---- | ------- | ----------- |
| `ReadOnlyHint` | `bool` | `false` | `true` for GET-equivalent operations |
| `DestructiveHint` | `*bool` | `true` | `false` for additive-only operations |
| `IdempotentHint` | `bool` | `false` | `true` for PUT/UPSERT operations |
| `OpenWorldHint` | `*bool` | `true` | `false` only for closed-world (e.g. in-memory) tools |

> `*bool` fields (`DestructiveHint`, `OpenWorldHint`) use pointer types because `nil` means "unset" (use default). Use `mcp.Ptr(true)` or `mcp.Ptr(false)`.

## Transport: stdio vs HTTP

### stdio (local, default)

For servers invoked directly by an MCP client (e.g., Claude Desktop, VS Code extension):

```go
if err := server.Run(context.Background(), &mcp.StdioTransport{}); err != nil {
    log.Fatalf("server error: %v", err)
}
```

Configure in `claude_desktop_config.json`:

```json
{
  "mcpServers": {
    "myserver": {
      "command": "/path/to/myserver",
      "env": { "API_TOKEN": "your-token" }
    }
  }
}
```

Or via `go run`:

```json
{
  "mcpServers": {
    "myserver": {
      "command": "go",
      "args": ["run", "/path/to/myserver"],
      "env": { "API_TOKEN": "your-token" }
    }
  }
}
```

### Streamable HTTP (remote)

```go
import "net/http"

handler := mcp.NewStreamableHTTPHandler(func(req *http.Request) *mcp.Server {
    return server
}, nil)

log.Println("MCP server listening on :8080")
if err := http.ListenAndServe(":8080", handler); err != nil {
    log.Fatalf("HTTP server error: %v", err)
}
```

**Transport selection:**
- **stdio**: Command-line tools, local development, subprocess integration
- **Streamable HTTP**: Web services, remote access, multiple clients

## Graceful Shutdown

Handle shutdown signals properly:

```go
ctx, cancel := context.WithCancel(context.Background())
defer cancel()

sigCh := make(chan os.Signal, 1)
signal.Notify(sigCh, os.Interrupt, syscall.SIGTERM)

go func() {
    <-sigCh
    cancel()
}()

if err := server.Run(ctx, &mcp.StdioTransport{}); err != nil {
    log.Fatal(err)
}
```

## Pagination Implementation

For tools that list resources:

```go
type ListInput struct {
    Limit  *int `json:"limit,omitempty"  jsonschema:"Maximum results to return (1-100), default 20"`
    Offset *int `json:"offset,omitempty" jsonschema:"Number of results to skip for pagination"`
}

type ListOutput struct {
    Total      int  `json:"total"      jsonschema:"Total number of items"`
    Count      int  `json:"count"      jsonschema:"Number of items in this response"`
    Offset     int  `json:"offset"     jsonschema:"Current pagination offset"`
    HasMore    bool `json:"hasMore"    jsonschema:"Whether more results are available"`
    NextOffset *int `json:"nextOffset,omitempty" jsonschema:"Offset for next page if hasMore is true"`
    // Items field added by the specific list type
}
```

## Complete Example

```go
package main

import (
    "context"
    "errors"
    "fmt"
    "log"
    "net/http"
    "os"
    "time"

    "github.com/modelcontextprotocol/go-sdk/mcp"
)

// --- Input/Output types ---

type ListReposInput struct {
    Owner   string `json:"owner"              jsonschema:"GitHub organization or username"`
    PerPage *int   `json:"perPage,omitempty"  jsonschema:"Results per page (1-100), defaults to 30"`
}

type RepoSummary struct {
    Name        string `json:"name"`
    Description string `json:"description"`
    Stars       int    `json:"stars"`
    Language    string `json:"language,omitempty"`
}

type ListReposOutput struct {
    Repos []RepoSummary `json:"repos" jsonschema:"list of matching repositories"`
    Total int           `json:"total" jsonschema:"total number of repos returned"`
}

// --- API client ---

type APIError struct {
    StatusCode int
    Message    string
}

func (e *APIError) Error() string { return fmt.Sprintf("API %d: %s", e.StatusCode, e.Message) }

type Client struct {
    token string
    http  *http.Client
}

func NewClient(token string) *Client {
    return &Client{token: token, http: &http.Client{Timeout: 30 * time.Second}}
}

func (c *Client) ListRepos(ctx context.Context, owner string, perPage int) ([]RepoSummary, error) {
    // ... make HTTP request, parse response ...
    return []RepoSummary{{Name: "example", Stars: 42}}, nil
}

// --- Tool handler ---

var apiClient *Client

func handleListRepos(ctx context.Context, req *mcp.CallToolRequest, in ListReposInput) (*mcp.CallToolResult, ListReposOutput, error) {
    perPage := 30
    if in.PerPage != nil {
        perPage = *in.PerPage
    }

    repos, err := apiClient.ListRepos(ctx, in.Owner, perPage)
    if err != nil {
        var apiErr *APIError
        if errors.As(err, &apiErr) && apiErr.StatusCode == 404 {
            return nil, ListReposOutput{}, fmt.Errorf("owner %q not found — verify the login name", in.Owner)
        }
        return nil, ListReposOutput{}, fmt.Errorf("listing repos: %w", err)
    }

    return nil, ListReposOutput{Repos: repos, Total: len(repos)}, nil
}

// --- Main ---

func main() {
    token := os.Getenv("API_TOKEN")
    if token == "" {
        log.Fatal("API_TOKEN environment variable is required")
    }
    apiClient = NewClient(token)

    server := mcp.NewServer(&mcp.Implementation{
        Name:    "example-mcp",
        Version: "1.0.0",
    }, nil)

    mcp.AddTool(server, &mcp.Tool{
        Name:        "list_repos",
        Description: "List repositories for an owner. Returns name, description, stars, and language.",
        Annotations: &mcp.ToolAnnotations{ReadOnlyHint: true},
    }, handleListRepos)

    if err := server.Run(context.Background(), &mcp.StdioTransport{}); err != nil {
        log.Fatalf("server error: %v", err)
    }
}
```

---

## Advanced MCP Features

### Resource Registration

Expose data as resources for URI-based access:

```go
mcp.AddResource(server,
    &mcp.Resource{
        URI:         "config://settings",
        Name:        "Server Settings",
        Description: "Current server configuration",
        MIMEType:    "application/json",
    },
    func(ctx context.Context, req *mcp.ReadResourceRequest) (*mcp.ReadResourceResult, error) {
        settings, err := loadSettings(ctx)
        if err != nil {
            return nil, err
        }
        return &mcp.ReadResourceResult{
            Contents: []any{
                &mcp.TextResourceContents{
                    ResourceContents: mcp.ResourceContents{
                        URI:      req.URI,
                        MIMEType: "application/json",
                    },
                    Text: settings,
                },
            },
        }, nil
    },
)
```

**When to use Resources vs Tools:**
- **Resources**: For data access with simple URI-based parameters
- **Tools**: For complex operations requiring validation and business logic

### Prompt Registration

Expose reusable prompt templates:

```go
type AnalyzeInput struct {
    Topic string `json:"topic" jsonschema:"the topic to analyze"`
}

mcp.AddPrompt(server,
    &mcp.Prompt{
        Name:        "analyze",
        Description: "Analyze a topic in depth",
        Arguments: []mcp.PromptArgument{
            {Name: "topic", Description: "The topic to analyze", Required: true},
        },
    },
    func(ctx context.Context, req *mcp.GetPromptRequest, input AnalyzeInput) (*mcp.GetPromptResult, error) {
        return &mcp.GetPromptResult{
            Description: "Analyze the given topic",
            Messages: []mcp.PromptMessage{
                {
                    Role:    mcp.RoleUser,
                    Content: mcp.TextContent{Text: fmt.Sprintf("Analyze this topic: %s", input.Topic)},
                },
            },
        }, nil
    },
)
```

---

## Code Best Practices

### Code Composability and Reusability

Your implementation MUST prioritize composability and code reuse:

1. **Extract Common Functionality**:
   - Create reusable helper functions for operations used across multiple tools
   - Build shared API clients for HTTP requests instead of duplicating code
   - Centralize error handling logic in utility functions
   - Extract business logic into dedicated functions that can be composed

2. **Avoid Duplication**:
   - NEVER copy-paste similar code between tools
   - If you find yourself writing similar logic twice, extract it into a function
   - Common operations like pagination, filtering, and formatting should be shared
   - Authentication/authorization logic should be centralized

### Go-Specific Best Practices

1. **Use `context.Context`**: Always pass and respect context for cancellation and deadlines
2. **Struct tags for schemas**: Use `json` and `jsonschema` tags on all input/output types
3. **Pointer types for optionals**: Non-pointer fields are required; use `*Type` for optional fields
4. **Error wrapping**: Use `fmt.Errorf("context: %w", err)` to preserve error chains
5. **No panics in handlers**: Always return errors; never `log.Fatal` or `panic` in tool handlers
6. **Structured logging**: Use `log/slog` for structured, leveled logging to stderr
7. **Constants**: Define module-level constants for configuration values

## Building and Running

```bash
# Build the project
go build ./...

# Run vet and lint
go vet ./...

# Run tests
go test ./...

# Run the server
go run .

# Test with MCP Inspector
npx @modelcontextprotocol/inspector go run .
```

Always ensure `go build ./...` and `go vet ./...` complete successfully before considering the implementation complete.

## Quality Checklist

Before finalizing your Go MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names reflect natural task subdivisions
- [ ] Response formats optimize for agent context efficiency
- [ ] Human-readable identifiers used where appropriate
- [ ] Error messages guide agents toward correct usage

### Implementation Quality
- [ ] FOCUSED IMPLEMENTATION: Most important and valuable tools implemented
- [ ] All tools registered using `mcp.AddTool` with complete configuration
- [ ] All tools include `Name`, `Description`, and `Annotations`
- [ ] Annotations correctly set (ReadOnlyHint, DestructiveHint, IdempotentHint, OpenWorldHint)
- [ ] All input types use struct tags (`json`, `jsonschema`) for schema generation
- [ ] Required fields are non-pointer; optional fields use pointer types
- [ ] All tools have comprehensive descriptions that state what they return
- [ ] Error messages are clear, actionable, and educational

### Go Quality
- [ ] `context.Context` passed through all I/O operations
- [ ] No panics or `log.Fatal` in tool handlers — errors returned properly
- [ ] Error chains preserved with `fmt.Errorf("...: %w", err)`
- [ ] API errors mapped to descriptive messages with recovery hints
- [ ] No hardcoded credentials — all secrets via environment variables
- [ ] Token validated at startup with clear error message if missing

### Advanced Features (where applicable)
- [ ] Resources registered for appropriate data endpoints
- [ ] Prompts registered for reusable templates
- [ ] Appropriate transport configured (stdio or streamable HTTP)
- [ ] Graceful shutdown with signal handling

### Project Configuration
- [ ] `go.mod` includes correct module path and SDK dependency
- [ ] Server name follows format: `{service}-mcp`
- [ ] `go build ./...` succeeds with no errors
- [ ] `go vet ./...` passes with no warnings

### Code Quality
- [ ] Pagination is properly implemented where applicable
- [ ] List endpoints support `limit` and `offset` (or `page`/`perPage`) parameters
- [ ] Common functionality is extracted into reusable functions
- [ ] Return types are consistent across similar operations
- [ ] All network operations handle timeouts via context or client config

### Testing and Build
- [ ] `go build ./...` compiles without errors
- [ ] `go vet ./...` passes
- [ ] `go test ./...` passes
- [ ] Manual test with MCP Inspector: `npx @modelcontextprotocol/inspector go run .`
- [ ] Sample tool calls work as expected
