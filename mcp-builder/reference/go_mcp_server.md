# Go MCP Server Implementation Guide

## Overview

This document provides Go-specific best practices and examples for implementing MCP servers using the Official Go MCP SDK. It covers server setup, tool registration patterns, input validation with JSON Schema, error handling, and complete working examples.

---

## Quick Reference

### Key Imports
```go
import (
  "context"
  "encoding/json"
  "log"

  "github.com/modelcontextprotocol/go-sdk/mcp"
  "github.com/google/jsonschema-go/jsonschema"
)
```

### Server Initialisation
```go
server := mcp.NewServer(&mcp.Implementation{
  Name:    "service-mcp-server",
  Version: "1.0.0",
}, nil)
```

### Tool Registration Pattern
```go
mcp.AddTool(server, &mcp.Tool{
  Name:        "tool_name",
  Description: "Tool description",
}, toolHandler)
```

---

## Official Go MCP SDK

The official Go MCP SDK is developed and maintained by Anthropic and the Go team. It provides:
- Type-safe tool registration with generic type parameters
- Automatic JSON Schema inference from Go structs
- Built-in validation and marshalling
- Multiple transport options (stdio, HTTP, SSE)
- Middleware support for cross-cutting concerns

**For complete SDK documentation, use WebFetch to load:**
`https://raw.githubusercontent.com/modelcontextprotocol/go-sdk/main/README.md`

**Package documentation:**
`https://pkg.go.dev/github.com/modelcontextprotocol/go-sdk/mcp`

## Server Naming Convention

Go MCP servers must follow this naming pattern:
- **Format**: `{service}-mcp-server` (lowercase with hyphens)
- **Examples**: `github-mcp-server`, `jira-mcp-server`, `stripe-mcp-server`

The name should be:
- General (not tied to specific features)
- Descriptive of the service/API being integrated
- Easy to infer from the task description
- Without version numbers or dates

## Project Structure

Create the following structure for Go MCP servers:

```
{service}-mcp-server/
├── go.mod                    # Go module definition
├── go.sum                    # Dependency checksums
├── README.md                 # Server documentation
├── main.go                   # Main entry point
├── tools.go                  # Tool implementations
├── types.go                  # Input/output type definitions
├── utils.go                  # Shared utilities
└── constants.go              # Constants (CHARACTER_LIMIT, API_URL)
```

For larger projects, you may organise into packages:

```
{service}-mcp-server/
├── go.mod
├── go.sum
├── README.md
├── cmd/
│   └── server/
│       └── main.go           # Main entry point
├── internal/
│   ├── tools/                # Tool implementations
│   ├── api/                  # API client
│   ├── types/                # Type definitions
│   └── utils/                # Shared utilities
```

## Tool Implementation

### Tool Naming

Use snake_case for tool names (e.g., "search_users", "create_project", "get_channel_info") with clear, action-oriented names.

**Avoid Naming Conflicts**: Include the service context to prevent overlaps:
- Use "slack_send_message" instead of just "send_message"
- Use "github_create_issue" instead of just "create_issue"
- Use "asana_list_tasks" instead of just "list_tasks"

### Tool Structure

Tools in Go are registered using the generic `mcp.AddTool` function, which provides automatic schema inference and validation:

```go
// Define input and output types
type UserSearchInput struct {
  Query  string `json:"query" jsonschema:"Search string to match against names/emails,minLength=2,maxLength=200"`
  Limit  int    `json:"limit,omitempty" jsonschema:"Maximum results to return,minimum=1,maximum=100"`
  Offset int    `json:"offset,omitempty" jsonschema:"Number of results to skip for pagination,minimum=0"`
}

type UserSearchOutput struct {
  Total int     `json:"total" jsonschema:"Total number of matches found"`
  Users []User  `json:"users" jsonschema:"List of matching users"`
}

// Tool handler function
func searchUsers(
  ctx context.Context,
  req *mcp.CallToolRequest,
  input UserSearchInput,
) (*mcp.CallToolResult, UserSearchOutput, error) {
  // Perform search using validated input
  users, total, err := apiSearchUsers(ctx, input.Query, input.Limit, input.Offset)
  if err != nil {
    // Tool errors: return in CallToolResult with IsError: true
    return &mcp.CallToolResult{
      Content: []mcp.Content{
        &mcp.TextContent{Text: fmt.Sprintf("Error: %v", err)},
      },
      IsError: true,
    }, UserSearchOutput{}, nil
  }

  // Success: return nil for CallToolResult (SDK auto-populates it)
  return nil, UserSearchOutput{
    Total: total,
    Users: users,
  }, nil
}

// Register the tool
mcp.AddTool(server, &mcp.Tool{
  Name:        "example_search_users",
  Description: "Search for users by name, email, or team",
}, searchUsers)
```

### Understanding the Three-Return Pattern

The Go SDK uses a unique three-return pattern for tool handlers:

```go
func toolHandler(
  ctx context.Context,
  req *mcp.CallToolRequest,
  input InputType,
) (*mcp.CallToolResult, OutputType, error)
```

**When to return what:**

1. **Success case**: `return nil, outputData, nil`
   - The SDK automatically populates `CallToolResult` from `outputData`
   - `outputData` is serialised to both `StructuredContent` and `Content`

2. **Tool error case** (validation failed, business logic error):
   ```go
   return &mcp.CallToolResult{
       Content: []mcp.Content{&mcp.TextContent{Text: "Error message"}},
       IsError: true,
   }, OutputType{}, nil
   ```
   - Use this for errors that should be reported to the LLM
   - The third return is `nil` (not a protocol error)

3. **Protocol error case**: `return nil, OutputType{}, err`
   - Use this for protocol-level failures (e.g., can't connect to API)
   - These are rare and indicate the tool cannot execute at all

## Input Validation with JSON Schema

The Go SDK provides automatic schema inference from struct tags, as well as manual schema construction for more control.

### Automatic Schema Inference

Use `json` and `jsonschema` struct tags to define schemas:

```go
type CreateUserInput struct {
  Name  string `json:"name" jsonschema:"User's full name,minLength=1,maxLength=100"`
  Email string `json:"email" jsonschema:"User's email address,format=email"`
  Age   int    `json:"age,omitempty" jsonschema:"User's age,minimum=0,maximum=150"`
  Tags  []string `json:"tags,omitempty" jsonschema:"User tags,maxItems=10"`
}

// The SDK automatically generates and validates against this schema:
// {
//   "type": "object",
//   "properties": {
//     "name": {"type": "string", "description": "User's full name", "minLength": 1, "maxLength": 100},
//     "email": {"type": "string", "description": "User's email address", "format": "email"},
//     "age": {"type": "integer", "description": "User's age", "minimum": 0, "maximum": 150},
//     "tags": {"type": "array", "items": {"type": "string"}, "maxItems": 10}
//   },
//   "required": ["name", "email"]
// }
```

**Supported jsonschema tag constraints:**
- **String**: `minLength`, `maxLength`, `pattern`, `format` (email, uri, date-time, etc.)
- **Number**: `minimum`, `maximum`, `exclusiveMinimum`, `exclusiveMaximum`, `multipleOf`
- **Array**: `minItems`, `maxItems`, `uniqueItems`
- **Object**: `minProperties`, `maxProperties`

### Manual Schema Construction

For more control, construct schemas explicitly:

```go
// Build custom schema
inputSchema := &jsonschema.Schema{
  Type: "object",
  Properties: map[string]*jsonschema.Schema{
    "query": {
      Type:      "string",
      MinLength: jsonschema.Ptr(2),
      MaxLength: jsonschema.Ptr(200),
    },
    "limit": {
      Type:    "integer",
      Minimum: jsonschema.Ptr(1.0),
      Maximum: jsonschema.Ptr(100.0),
      Default: 20,
    },
  },
  Required: []string{"query"},
}

// Register tool with explicit schema
mcp.AddTool(server, &mcp.Tool{
  Name:        "search",
  Description: "Search with custom schema",
  InputSchema: inputSchema,
}, searchHandler)
```

### Customising Inferred Schemas

You can also infer a schema and then customise it:

```go
// Infer base schema from type
schema, err := jsonschema.For[UserSearchInput](nil)
if err != nil {
  log.Fatal(err)
}

// Customise specific properties
schema.Properties["query"].Pattern = "^[a-zA-Z0-9 ]+$"
schema.Properties["limit"].Default = 25

// Use customised schema
mcp.AddTool(server, &mcp.Tool{
  Name:        "search_users",
  InputSchema: schema,
}, searchUsers)
```

## Response Format Options

Support multiple output formats for flexibility:

```go
type ResponseFormat string

const (
  ResponseFormatMarkdown ResponseFormat = "markdown"
  ResponseFormatJSON     ResponseFormat = "json"
)

type UserSearchInput struct {
  Query          string         `json:"query" jsonschema:"Search query"`
  ResponseFormat ResponseFormat `json:"response_format,omitempty" jsonschema:"Output format: 'markdown' or 'json'"`
}

func searchUsers(
  ctx context.Context,
  req *mcp.CallToolRequest,
  input UserSearchInput,
) (*mcp.CallToolResult, any, error) {
  // Fetch data
  users, err := apiSearchUsers(ctx, input.Query)
  if err != nil {
    return &mcp.CallToolResult{
      Content: []mcp.Content{&mcp.TextContent{Text: "Error: " + err.Error()}},
      IsError: true,
    }, nil, nil
  }

  // Format based on requested format
  if input.ResponseFormat == ResponseFormatMarkdown {
    var sb strings.Builder
    sb.WriteString("# User Search Results\n\n")
    for _, user := range users {
      sb.WriteString(fmt.Sprintf("## %s (%s)\n", user.Name, user.ID))
      sb.WriteString(fmt.Sprintf("- **Email**: %s\n", user.Email))
      if user.Team != "" {
        sb.WriteString(fmt.Sprintf("- **Team**: %s\n", user.Team))
      }
      sb.WriteString("\n")
    }
    return &mcp.CallToolResult{
      Content: []mcp.Content{&mcp.TextContent{Text: sb.String()}},
    }, nil, nil
  }

  // JSON format: return structured output
  return nil, map[string]any{
    "total": len(users),
    "users": users,
  }, nil
}
```

**Markdown format guidelines:**
- Use headers, lists, and formatting for clarity
- Convert timestamps to human-readable format (e.g., "2024-01-15 10:30:00 UTC")
- Show display names with IDs in parentheses (e.g., "@john.doe (U123456)")
- Omit verbose metadata
- Group related information logically

**JSON format guidelines:**
- Return complete, structured data
- Include all available fields and metadata
- Use consistent field names and types

## Pagination Implementation

The Go SDK handles pagination automatically on the server side. Configuration is minimal:

```go
// Server-side: Configure page size (optional)
server := mcp.NewServer(&mcp.Implementation{
  Name: "example-mcp-server",
}, &mcp.ServerOptions{
  PageSize: 50, // Default page size for list operations
})
```

For tools that list resources, include pagination parameters in your input type:

```go
type ListInput struct {
  Limit  int `json:"limit,omitempty" jsonschema:"Maximum results to return,minimum=1,maximum=100"`
  Offset int `json:"offset,omitempty" jsonschema:"Number of results to skip,minimum=0"`
}

type ListOutput struct {
  Total      int      `json:"total" jsonschema:"Total number of items available"`
  Count      int      `json:"count" jsonschema:"Number of items in this response"`
  Offset     int      `json:"offset" jsonschema:"Current offset"`
  Items      []Item   `json:"items" jsonschema:"List of items"`
  HasMore    bool     `json:"has_more" jsonschema:"Whether more results are available"`
  NextOffset *int     `json:"next_offset,omitempty" jsonschema:"Offset for next page if has_more is true"`
}

func listItems(
  ctx context.Context,
  req *mcp.CallToolRequest,
  input ListInput,
) (*mcp.CallToolResult, ListOutput, error) {
  // Apply defaults
  if input.Limit == 0 {
    input.Limit = 20
  }

  // Fetch paginated data
  items, total, err := apiListItems(ctx, input.Limit, input.Offset)
  if err != nil {
    return &mcp.CallToolResult{
      Content: []mcp.Content{&mcp.TextContent{Text: "Error: " + err.Error()}},
      IsError: true,
    }, ListOutput{}, nil
  }

  // Calculate pagination metadata
  hasMore := total > input.Offset+len(items)
  var nextOffset *int
  if hasMore {
    next := input.Offset + len(items)
    nextOffset = &next
  }

  return nil, ListOutput{
    Total:      total,
    Count:      len(items),
    Offset:     input.Offset,
    Items:      items,
    HasMore:    hasMore,
    NextOffset: nextOffset,
  }, nil
}
```

## Character Limits and Truncation

Add a CHARACTER_LIMIT constant to prevent overwhelming responses:

```go
// At package level
const CHARACTER_LIMIT = 25000 // Maximum response size in characters

func searchTool(
  ctx context.Context,
  req *mcp.CallToolRequest,
  input SearchInput,
) (*mcp.CallToolResult, any, error) {
  // Generate response
  result := generateResponse(data)

  // Check character limit and truncate if needed
  if len(result) > CHARACTER_LIMIT {
    // Truncate data and add notice
    truncatedData := data[:max(1, len(data)/2)]
    result = generateResponse(truncatedData)
    result += fmt.Sprintf("\n\n**Note**: Response truncated from %d to %d items. "+
      "Use 'offset' parameter or add filters to see more results.",
      len(data), len(truncatedData))
  }

  return &mcp.CallToolResult{
    Content: []mcp.Content{&mcp.TextContent{Text: result}},
  }, nil, nil
}
```

## Error Handling

Provide clear, actionable error messages that guide the LLM:

```go
// Shared error handling function
func handleAPIError(err error) *mcp.CallToolResult {
  var msg string

  // Type switch on error type
  switch e := err.(type) {
  case *HTTPError:
    switch e.StatusCode {
    case 404:
      msg = "Error: Resource not found. Please check the ID is correct."
    case 403:
      msg = "Error: Permission denied. You don't have access to this resource."
    case 429:
      msg = "Error: Rate limit exceeded. Please wait before making more requests."
    default:
      msg = fmt.Sprintf("Error: API request failed with status %d", e.StatusCode)
    }
  case *TimeoutError:
    msg = "Error: Request timed out. Please try again."
  default:
    msg = fmt.Sprintf("Error: Unexpected error occurred: %v", err)
  }

  return &mcp.CallToolResult{
    Content: []mcp.Content{&mcp.TextContent{Text: msg}},
    IsError: true,
  }
}

// Use in tool handlers
func myTool(ctx context.Context, req *mcp.CallToolRequest, input Input) (*mcp.CallToolResult, Output, error) {
  data, err := apiCall(ctx, input)
  if err != nil {
    return handleAPIError(err), Output{}, nil
  }
  return nil, Output{Data: data}, nil
}
```

## Shared Utilities

Extract common functionality into reusable functions:

```go
// Shared API request function
func makeAPIRequest(ctx context.Context, method, endpoint string, body any) ([]byte, error) {
  var reqBody io.Reader
  if body != nil {
    jsonData, err := json.Marshal(body)
    if err != nil {
      return nil, fmt.Errorf("marshal request: %w", err)
    }
    reqBody = bytes.NewReader(jsonData)
  }

  req, err := http.NewRequestWithContext(ctx, method, API_BASE_URL+endpoint, reqBody)
  if err != nil {
    return nil, fmt.Errorf("create request: %w", err)
  }

  req.Header.Set("Content-Type", "application/json")
  req.Header.Set("Accept", "application/json")

  client := &http.Client{Timeout: 30 * time.Second}
  resp, err := client.Do(req)
  if err != nil {
    return nil, fmt.Errorf("execute request: %w", err)
  }
  defer resp.Body.Close()

  data, err := io.ReadAll(resp.Body)
  if err != nil {
    return nil, fmt.Errorf("read response: %w", err)
  }

  if resp.StatusCode >= 400 {
    return nil, &HTTPError{StatusCode: resp.StatusCode, Body: string(data)}
  }

  return data, nil
}

// Custom error type
type HTTPError struct {
  StatusCode int
  Body       string
}

func (e *HTTPError) Error() string {
  return fmt.Sprintf("HTTP %d: %s", e.StatusCode, e.Body)
}
```

## Context and Cancellation

Always use `context.Context` for operations that can be cancelled or have timeouts:

```go
func fetchData(ctx context.Context, resourceID string) (Data, error) {
  // Create request with context
  req, err := http.NewRequestWithContext(ctx, "GET", API_URL+"/resource/"+resourceID, nil)
  if err != nil {
    return Data{}, err
  }

  // Check for cancellation before proceeding
  select {
  case <-ctx.Done():
    return Data{}, ctx.Err()
  default:
  }

  // Execute request (will be cancelled if context is cancelled)
  client := &http.Client{}
  resp, err := client.Do(req)
  if err != nil {
    return Data{}, err
  }
  defer resp.Body.Close()

  // Parse response
  var data Data
  if err := json.NewDecoder(resp.Body).Decode(&data); err != nil {
    return Data{}, err
  }

  return data, nil
}

// Use in tool handler
func myTool(ctx context.Context, req *mcp.CallToolRequest, input Input) (*mcp.CallToolResult, Output, error) {
  // Context is automatically passed and handles cancellation
  data, err := fetchData(ctx, input.ResourceID)
  if err != nil {
    if ctx.Err() != nil {
      // Context was cancelled
      return &mcp.CallToolResult{
        Content: []mcp.Content{&mcp.TextContent{Text: "Operation cancelled"}},
        IsError: true,
      }, Output{}, nil
    }
    return handleAPIError(err), Output{}, nil
  }
  return nil, Output{Data: data}, nil
}
```

## Type Safety Best Practices

1. **Avoid `any` and `interface{}`**: Use specific types where possible
   ```go
   // Good: Specific type
   type User struct {
       ID   string
       Name string
   }

   // Avoid: Overly generic
   type Response map[string]any
   ```

2. **Use type parameters for generic utilities**:
   ```go
   func makeTypedAPICall[T any](ctx context.Context, endpoint string) (T, error) {
       var result T
       data, err := makeAPIRequest(ctx, "GET", endpoint, nil)
       if err != nil {
           return result, err
       }
       if err := json.Unmarshal(data, &result); err != nil {
           return result, fmt.Errorf("unmarshal response: %w", err)
       }
       return result, nil
   }
   ```

3. **Type assertions with safety**:
   ```go
   // Always check type assertions
   if content, ok := result.Content[0].(*mcp.TextContent); ok {
       fmt.Println(content.Text)
   }
   ```

4. **Define clear interfaces**:
   ```go
   type APIClient interface {
       SearchUsers(ctx context.Context, query string) ([]User, error)
       GetUser(ctx context.Context, id string) (User, error)
   }
   ```

## Package Configuration

### go.mod

```go
module github.com/myorg/example-mcp-server

go 1.23

require (
  github.com/modelcontextprotocol/go-sdk v0.1.0
  github.com/google/jsonschema-go v0.0.0-20250101000000-abcdef123456
)
```

### Project Dependencies

Install dependencies:
```bash
go mod download
```

Update dependencies:
```bash
go get -u github.com/modelcontextprotocol/go-sdk
go mod tidy
```

## Build and Run

### Build the Server

```bash
# Build for current platform
go build -o example-mcp-server

# Build with optimisation
go build -ldflags="-s -w" -o example-mcp-server

# Build for specific platform
GOOS=linux GOARCH=amd64 go build -o example-mcp-server
```

### Run the Server

```bash
# Run with stdio transport (default)
./example-mcp-server

# Run with environment variables
API_KEY=your_key ./example-mcp-server

# Run with HTTP transport
./example-mcp-server -http :8080
```

### Development Workflow

```bash
# Format code
go fmt ./...

# Vet code for issues
go vet ./...

# Run linters (if using golangci-lint)
golangci-lint run

# Test compilation without creating binary
go build -o /dev/null
```

## Complete Example

Below is a complete, runnable example of an MCP server:

```go
package main

import (
  "context"
  "encoding/json"
  "fmt"
  "io"
  "log"
  "net/http"
  "os"
  "strings"
  "time"

  "github.com/modelcontextprotocol/go-sdk/mcp"
)

// Constants
const (
  API_BASE_URL     = "https://api.example.com/v1"
  CHARACTER_LIMIT  = 25000
)

// Response format enum
type ResponseFormat string

const (
  ResponseFormatMarkdown ResponseFormat = "markdown"
  ResponseFormatJSON     ResponseFormat = "json"
)

// Input types
type UserSearchInput struct {
  Query          string         `json:"query" jsonschema:"Search string to match against names/emails,minLength=2,maxLength=200"`
  Limit          int            `json:"limit,omitempty" jsonschema:"Maximum results to return,minimum=1,maximum=100"`
  Offset         int            `json:"offset,omitempty" jsonschema:"Number of results to skip,minimum=0"`
  ResponseFormat ResponseFormat `json:"response_format,omitempty" jsonschema:"Output format: 'markdown' or 'json'"`
}

type CreateUserInput struct {
  Name  string `json:"name" jsonschema:"User's full name,minLength=1,maxLength=100"`
  Email string `json:"email" jsonschema:"User's email address,format=email"`
}

// Output types
type User struct {
  ID    string `json:"id"`
  Name  string `json:"name"`
  Email string `json:"email"`
  Team  string `json:"team,omitempty"`
}

type UserSearchOutput struct {
  Total  int    `json:"total"`
  Count  int    `json:"count"`
  Offset int    `json:"offset"`
  Users  []User `json:"users"`
}

// HTTP error type
type HTTPError struct {
  StatusCode int
  Body       string
}

func (e *HTTPError) Error() string {
  return fmt.Sprintf("HTTP %d: %s", e.StatusCode, e.Body)
}

// Shared utilities
func makeAPIRequest(ctx context.Context, method, endpoint string, body any) ([]byte, error) {
  var reqBody io.Reader
  if body != nil {
    jsonData, err := json.Marshal(body)
    if err != nil {
      return nil, fmt.Errorf("marshal request: %w", err)
    }
    reqBody = strings.NewReader(string(jsonData))
  }

  req, err := http.NewRequestWithContext(ctx, method, API_BASE_URL+endpoint, reqBody)
  if err != nil {
    return nil, fmt.Errorf("create request: %w", err)
  }

  req.Header.Set("Content-Type", "application/json")
  req.Header.Set("Accept", "application/json")

  apiKey := os.Getenv("EXAMPLE_API_KEY")
  if apiKey != "" {
    req.Header.Set("Authorization", "Bearer "+apiKey)
  }

  client := &http.Client{Timeout: 30 * time.Second}
  resp, err := client.Do(req)
  if err != nil {
    return nil, fmt.Errorf("execute request: %w", err)
  }
  defer resp.Body.Close()

  data, err := io.ReadAll(resp.Body)
  if err != nil {
    return nil, fmt.Errorf("read response: %w", err)
  }

  if resp.StatusCode >= 400 {
    return nil, &HTTPError{StatusCode: resp.StatusCode, Body: string(data)}
  }

  return data, nil
}

func handleAPIError(err error) *mcp.CallToolResult {
  var msg string
  switch e := err.(type) {
  case *HTTPError:
    switch e.StatusCode {
    case 404:
      msg = "Error: Resource not found. Please check the ID is correct."
    case 403:
      msg = "Error: Permission denied. You don't have access to this resource."
    case 429:
      msg = "Error: Rate limit exceeded. Please wait before making more requests."
    default:
      msg = fmt.Sprintf("Error: API request failed with status %d", e.StatusCode)
    }
  default:
    msg = fmt.Sprintf("Error: %v", err)
  }

  return &mcp.CallToolResult{
    Content: []mcp.Content{&mcp.TextContent{Text: msg}},
    IsError: true,
  }
}

// Tool handlers
func searchUsers(
  ctx context.Context,
  req *mcp.CallToolRequest,
  input UserSearchInput,
) (*mcp.CallToolResult, any, error) {
  // Apply defaults
  if input.Limit == 0 {
    input.Limit = 20
  }
  if input.ResponseFormat == "" {
    input.ResponseFormat = ResponseFormatMarkdown
  }

  // Make API request
  endpoint := fmt.Sprintf("/users/search?q=%s&limit=%d&offset=%d",
    input.Query, input.Limit, input.Offset)
  data, err := makeAPIRequest(ctx, "GET", endpoint, nil)
  if err != nil {
    return handleAPIError(err), nil, nil
  }

  // Parse response
  var apiResp struct {
    Total int    `json:"total"`
    Users []User `json:"users"`
  }
  if err := json.Unmarshal(data, &apiResp); err != nil {
    return &mcp.CallToolResult{
      Content: []mcp.Content{&mcp.TextContent{Text: "Error parsing response"}},
      IsError: true,
    }, nil, nil
  }

  // Format based on requested format
  if input.ResponseFormat == ResponseFormatMarkdown {
    var sb strings.Builder
    sb.WriteString(fmt.Sprintf("# User Search Results: '%s'\n\n", input.Query))
    sb.WriteString(fmt.Sprintf("Found %d users (showing %d)\n\n", apiResp.Total, len(apiResp.Users)))

    for _, user := range apiResp.Users {
      sb.WriteString(fmt.Sprintf("## %s (%s)\n", user.Name, user.ID))
      sb.WriteString(fmt.Sprintf("- **Email**: %s\n", user.Email))
      if user.Team != "" {
        sb.WriteString(fmt.Sprintf("- **Team**: %s\n", user.Team))
      }
      sb.WriteString("\n")
    }

    result := sb.String()
    if len(result) > CHARACTER_LIMIT {
      result = result[:CHARACTER_LIMIT] + "\n\n**Response truncated. Use filters to narrow results.**"
    }

    return &mcp.CallToolResult{
      Content: []mcp.Content{&mcp.TextContent{Text: result}},
    }, nil, nil
  }

  // JSON format
  return nil, UserSearchOutput{
    Total:  apiResp.Total,
    Count:  len(apiResp.Users),
    Offset: input.Offset,
    Users:  apiResp.Users,
  }, nil
}

func createUser(
  ctx context.Context,
  req *mcp.CallToolRequest,
  input CreateUserInput,
) (*mcp.CallToolResult, User, error) {
  // Make API request
  data, err := makeAPIRequest(ctx, "POST", "/users", input)
  if err != nil {
    return handleAPIError(err), User{}, nil
  }

  // Parse response
  var user User
  if err := json.Unmarshal(data, &user); err != nil {
    return &mcp.CallToolResult{
      Content: []mcp.Content{&mcp.TextContent{Text: "Error parsing response"}},
      IsError: true,
    }, User{}, nil
  }

  return nil, user, nil
}

func main() {
  // Verify API key is set
  if os.Getenv("EXAMPLE_API_KEY") == "" {
    log.Println("Warning: EXAMPLE_API_KEY environment variable not set")
  }

  // Create server
  server := mcp.NewServer(&mcp.Implementation{
    Name:    "example-mcp-server",
    Version: "1.0.0",
  }, &mcp.ServerOptions{
    PageSize: 50,
  })

  // Register tools
  mcp.AddTool(server, &mcp.Tool{
    Name:        "example_search_users",
    Description: "Search for users in the Example system by name, email, or team",
  }, searchUsers)

  mcp.AddTool(server, &mcp.Tool{
    Name:        "example_create_user",
    Description: "Create a new user in the Example system",
  }, createUser)

  // Run server over stdio
  if err := server.Run(context.Background(), &mcp.StdioTransport{}); err != nil {
    log.Printf("Server failed: %v", err)
  }
}
```

---

## Advanced Go SDK Features

### Server Features

The Go SDK supports all MCP server features:

#### Adding Prompts

```go
prompt := &mcp.Prompt{
  Name:        "code_review",
  Description: "Generate a code review",
  Arguments: []*mcp.PromptArgument{
    {
      Name:        "code",
      Description: "The code to review",
      Required:    true,
    },
  },
}

promptHandler := func(ctx context.Context, req *mcp.GetPromptRequest) (*mcp.GetPromptResult, error) {
  code := req.Params.Arguments["code"]
  return &mcp.GetPromptResult{
    Messages: []*mcp.PromptMessage{
      {
        Role:    "user",
        Content: &mcp.TextContent{Text: "Please review this code:\n\n" + code},
      },
    },
  }, nil
}

server.AddPrompt(prompt, promptHandler)
```

#### Adding Resources

```go
resource := &mcp.Resource{
  URI:      "file:///config.json",
  Name:     "Configuration",
  MIMEType: "application/json",
}

resourceHandler := func(ctx context.Context, req *mcp.ReadResourceRequest) (*mcp.ReadResourceResult, error) {
  config := loadConfig()
  data, _ := json.Marshal(config)
  return &mcp.ReadResourceResult{
    Contents: []*mcp.ResourceContents{
      {URI: req.Params.URI, MIMEType: "application/json", Text: string(data)},
    },
  }, nil
}

server.AddResource(resource, resourceHandler)
```

#### Adding Resource Templates

```go
template := &mcp.ResourceTemplate{
  URITemplate: "file:///documents/{name}",
  Name:        "Document",
  MIMEType:    "text/plain",
}

templateHandler := func(ctx context.Context, req *mcp.ReadResourceRequest) (*mcp.ReadResourceResult, error) {
  // Extract name from URI
  name := extractNameFromURI(req.Params.URI)
  content := loadDocument(name)
  return &mcp.ReadResourceResult{
    Contents: []*mcp.ResourceContents{
      {URI: req.Params.URI, MIMEType: "text/plain", Text: content},
    },
  }, nil
}

server.AddResourceTemplate(template, templateHandler)
```

### Middleware

The Go SDK provides powerful middleware support for cross-cutting concerns:

```go
// Logging middleware
func loggingMiddleware(next mcp.MethodHandler) mcp.MethodHandler {
  return func(ctx context.Context, method string, req mcp.Request) (mcp.Result, error) {
    log.Printf("Request: %s", method)
    result, err := next(ctx, method, req)
    log.Printf("Response: %v, %v", result, err)
    return result, err
  }
}

// Authentication middleware
func authMiddleware(next mcp.MethodHandler) mcp.MethodHandler {
  return func(ctx context.Context, method string, req mcp.Request) (mcp.Result, error) {
    // Check authentication
    if !isAuthenticated(ctx) {
      return nil, fmt.Errorf("authentication required")
    }
    return next(ctx, method, req)
  }
}

// Add middleware to server
server.AddReceivingMiddleware(authMiddleware, loggingMiddleware)
```

### Progress Reporting

```go
func longRunningTool(
  ctx context.Context,
  req *mcp.CallToolRequest,
  input Input,
) (*mcp.CallToolResult, Output, error) {
  // Only report progress if client provided a progress token
  if req.Params.Meta.ProgressToken != nil {
    // Get server session from context (if available)
    // Report progress at key points
    // session.NotifyProgress(ctx, &mcp.ProgressNotification{
    //     ProgressToken: req.Params.Meta.ProgressToken,
    //     Progress:      50,
    //     Total:         100,
    // })
  }

  // Perform work
  result := performWork(ctx, input)
  return nil, Output{Result: result}, nil
}
```

### Logging with slog

The Go SDK integrates with Go's structured logging:

```go
import (
  "log/slog"
  "os"
)

func main() {
  server := mcp.NewServer(&mcp.Implementation{Name: "server"}, nil)

  // When server is connected, get session
  transport := &mcp.StdioTransport{}
  session, err := server.Connect(context.Background(), transport, nil)
  if err != nil {
    log.Fatal(err)
  }

  // Create slog handler that logs to MCP client
  handler := mcp.NewLoggingHandler(session, &mcp.LoggingHandlerOptions{
    LoggerName:  "example-server",
    MinInterval: time.Second, // Rate limit log messages
  })
  logger := slog.New(handler)

  // Use logger in tools
  logger.Info("Server started", "version", "1.0.0")
}
```

### Multiple Transport Options

```go
// Stdio transport (default for CLI tools)
server.Run(ctx, &mcp.StdioTransport{})

// HTTP transport
handler := mcp.NewStreamableHTTPHandler(func(*http.Request) *mcp.Server {
  return server
}, nil)
http.ListenAndServe(":8080", handler)

// SSE transport
sseHandler := mcp.NewSSEHTTPHandler(func(*http.Request) *mcp.Server {
  return server
}, nil)
http.ListenAndServe(":8080", sseHandler)
```

---

## Code Best Practices

### Code Composability and Reusability

Your implementation MUST prioritise composability and code reuse:

1. **Extract Common Functionality**:
   - Create reusable helper functions for operations used across multiple tools
   - Build shared API clients for HTTP requests
   - Centralise error handling logic in utility functions
   - Extract business logic into dedicated functions
   - Extract shared formatting functionality

2. **Avoid Duplication**:
   - NEVER copy-paste similar code between tools
   - If writing similar logic twice, extract it into a function
   - Common operations like pagination, filtering, and formatting should be shared
   - Authentication/authorisation logic should be centralised

### Go-Specific Best Practices

1. **Error Handling**: Use error wrapping with `fmt.Errorf` and `%w`
   ```go
   if err != nil {
       return fmt.Errorf("failed to fetch user: %w", err)
   }
   ```

2. **Early Returns**: Avoid deep nesting with early returns
   ```go
   if err != nil {
       return handleAPIError(err), Output{}, nil
   }
   // Continue with success path
   ```

3. **Package Organisation**: Keep related functionality together
   ```go
   // tools.go - all tool handlers
   // api.go - all API client code
   // types.go - all type definitions
   ```

4. **Constants**: Define package-level constants in UPPER_CASE
   ```go
   const (
       API_BASE_URL    = "https://api.example.com"
       CHARACTER_LIMIT = 25000
   )
   ```

5. **Minimal Copying**: "A little copying is better than a little dependency" - don't over-abstract

## Quality Checklist

Before finalising your Go MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names reflect natural task subdivisions
- [ ] Response formats optimise for agent context efficiency
- [ ] Human-readable identifiers used where appropriate
- [ ] Error messages guide agents towards correct usage

### Implementation Quality
- [ ] FOCUSED IMPLEMENTATION: Most important and valuable tools implemented
- [ ] All tools have descriptive names and documentation
- [ ] Return types are consistent across similar operations
- [ ] Error handling is implemented for all external calls
- [ ] Server name follows format: `{service}-mcp-server`
- [ ] All I/O operations use context.Context
- [ ] Common functionality is extracted into reusable functions
- [ ] Error messages are clear, actionable, and educational

### Tool Configuration
- [ ] All tools registered with `mcp.AddTool` and proper tool metadata
- [ ] Tool names, descriptions, and annotations correctly set
- [ ] Input/output types use appropriate struct tags (`json`, `jsonschema`)
- [ ] JSON Schema constraints defined where appropriate (min/max, patterns)
- [ ] Three-return pattern used correctly (CallToolResult, Output, error)
- [ ] Tool errors use `IsError: true` in CallToolResult, not third return

### Go-Specific Quality
- [ ] Go module properly configured (go.mod, go.sum)
- [ ] Code passes `go fmt` (properly formatted)
- [ ] Code passes `go vet` (no suspicious constructs)
- [ ] No use of `any` or `interface{}` where specific types can be used
- [ ] Context.Context passed to all I/O operations
- [ ] Error wrapping uses `fmt.Errorf` with `%w`
- [ ] Type assertions checked for safety
- [ ] Proper use of generics for type-safe operations

### Code Quality
- [ ] Pagination handled correctly with proper metadata
- [ ] Large responses check CHARACTER_LIMIT and truncate with clear messages
- [ ] Filtering options provided for potentially large result sets
- [ ] HTTP client properly configured with timeouts
- [ ] Middleware used for cross-cutting concerns where appropriate

### Build and Testing
- [ ] `go build` completes successfully
- [ ] Binary runs successfully: `./my-mcp-server`
- [ ] Server responds correctly over stdio transport
- [ ] Compatible with evaluation harness via `python scripts/evaluation.py -t stdio -c ./my-mcp-server`
