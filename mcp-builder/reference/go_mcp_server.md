# Go MCP Server Implementation Guide

## Overview

This document provides Go-specific best practices and examples for implementing MCP servers using the official Go MCP SDK. It covers server setup, tool registration patterns, input validation with JSON schemas, error handling, and complete working examples.

---

## Quick Reference

### Key Imports
```go
import (
	"context"
	"encoding/json"
	"fmt"
	"log"

	"github.com/modelcontextprotocol/go-sdk/mcp"
	"github.com/google/jsonschema-go/jsonschema"
)
```

### Server Initialization
```go
server := mcp.NewServer(&mcp.Implementation{
	Name:    "service-mcp",
	Version: "v1.0.0",
}, nil)
```

### Tool Registration Pattern
```go
type ToolInput struct {
	Name string `json:"name" jsonschema:"description of the name field"`
}

type ToolOutput struct {
	Result string `json:"result" jsonschema:"description of the result field"`
}

func toolHandler(ctx context.Context, req *mcp.CallToolRequest, input ToolInput) (
	*mcp.CallToolResult, ToolOutput, error,
) {
	// Implementation
	output := ToolOutput{Result: "processed " + input.Name}
	return nil, output, nil
}

// Register with automatic schema inference
mcp.AddTool(server, &mcp.Tool{
	Name:        "tool_name",
	Description: "Tool description",
}, toolHandler)
```

---

## Go MCP SDK Architecture

The official Go MCP SDK provides a comprehensive framework for building MCP servers and clients. It provides:
- Automatic JSON schema generation from Go struct types
- Type-safe tool registration with `mcp.AddTool`
- Multiple transport options (stdio, HTTP/SSE, Streamable HTTP)
- Middleware support for request/response interception
- Iterator-based pagination

**For complete SDK documentation, use WebFetch to load:**
`https://raw.githubusercontent.com/modelcontextprotocol/go-sdk/main/README.md`

**For detailed feature documentation, see:**
- `https://raw.githubusercontent.com/modelcontextprotocol/go-sdk/main/docs/server.md`
- `https://raw.githubusercontent.com/modelcontextprotocol/go-sdk/main/docs/client.md`

## Server Naming Convention

Go MCP servers must follow this naming pattern:
- **Format**: `{service}-mcp` (lowercase with hyphens)
- **Examples**: `github-mcp`, `jira-mcp`, `stripe-mcp`

The name should be:
- General (not tied to specific features)
- Descriptive of the service/API being integrated
- Easy to infer from the task description
- Without version numbers or dates

**Implementation Name vs Tool Names:**
- Server `Implementation.Name` uses hyphen-case: `"github-mcp"`
- Tool names use snake_case: `"github_create_issue"`

## Tool Implementation

### Tool Naming

Use snake_case for tool names (e.g., "search_users", "create_project", "get_channel_info") with clear, action-oriented names.

**Avoid Naming Conflicts**: Include the service context to prevent overlaps:
- Use "slack_send_message" instead of just "send_message"
- Use "github_create_issue" instead of just "create_issue"
- Use "asana_list_tasks" instead of just "list_tasks"

### Tool Structure with Type Inference

The Go SDK uses `mcp.AddTool` to bind tools to handler functions with automatic type inference:

```go
package main

import (
	"context"
	"encoding/json"
	"fmt"

	"github.com/modelcontextprotocol/go-sdk/mcp"
	"github.com/google/jsonschema-go/jsonschema"
)

// Define input type with JSON and jsonschema tags
type SearchUsersInput struct {
	Query  string `json:"query" jsonschema:"Search query to match against user names or emails (e.g. 'john', 'eng-team')"`
	Limit  int    `json:"limit" jsonschema:"Maximum number of results to return, between 1 and 100"`
	Offset int    `json:"offset" jsonschema:"Number of results to skip for pagination, default 0"`
}

// Define output type with JSON and jsonschema tags
type SearchUsersOutput struct {
	Total   int          `json:"total" jsonschema:"Total number of users matching the query"`
	Count   int          `json:"count" jsonschema:"Number of users in this response"`
	Offset  int          `json:"offset" jsonschema:"Current pagination offset"`
	Users   []UserResult `json:"users" jsonschema:"List of users matching the search"`
	HasMore bool         `json:"has_more" jsonschema:"Whether more results are available"`
}

type UserResult struct {
	ID    string `json:"id" jsonschema:"User ID (e.g. U123456789)"`
	Name  string `json:"name" jsonschema:"User's full name"`
	Email string `json:"email" jsonschema:"User's email address"`
}

// Handler function - types determine schema inference
func searchUsersHandler(
	ctx context.Context,
	req *mcp.CallToolRequest,
	input SearchUsersInput,
) (*mcp.CallToolResult, SearchUsersOutput, error) {
	// Validate input constraints
	if input.Limit < 1 || input.Limit > 100 {
		return mcp.NewToolResultError("Limit must be between 1 and 100"),
			SearchUsersOutput{}, nil
	}

	// Implementation here - fetch from API
	users := []UserResult{
		{ID: "U123", Name: "John Doe", Email: "john@example.com"},
	}

	output := SearchUsersOutput{
		Total:   1,
		Count:   len(users),
		Offset:  input.Offset,
		Users:   users,
		HasMore: false,
	}

	return nil, output, nil
}

func main() {
	// Create server
	server := mcp.NewServer(&mcp.Implementation{
		Name:    "example-mcp",
		Version: "v1.0.0",
	}, nil)

	// Register tool with automatic schema inference
	mcp.AddTool(server, &mcp.Tool{
		Name:        "example_search_users",
		Description: "Search for users in the Example system by name or email",
	}, searchUsersHandler)

	// Run server over stdio
	if err := server.Run(context.Background(), &mcp.StdioTransport{}); err != nil {
		log.Fatal(err)
	}
}
```

**How `mcp.AddTool` works:**
- Automatically generates `InputSchema` from the input struct type
- Automatically generates `OutputSchema` from the output struct type
- Validates input arguments against the schema
- Unmarshals arguments into the input type
- Marshals output into both `StructuredOutput` and `Content` fields
- Handles error cases automatically

### Custom Schema Constraints

To add custom constraints beyond what struct tags provide, manually define schemas:

```go
import "github.com/google/jsonschema-go/jsonschema"

// Define custom types for better schema control
type Probability float64
type WeatherType string

const (
	Sunny        WeatherType = "sunny"
	PartlyCloudy WeatherType = "partly_cloudy"
	Rainy        WeatherType = "rainy"
)

type WeatherInput struct {
	Location string `json:"location" jsonschema:"User's location for weather forecast"`
	Days     int    `json:"days" jsonschema:"Number of days to forecast"`
}

type WeatherOutput struct {
	Summary    string      `json:"summary" jsonschema:"Summary of the weather forecast"`
	Confidence Probability `json:"confidence" jsonschema:"Confidence level between 0 and 1"`
	DailyForecast []DailyForecast `json:"daily_forecast" jsonschema:"Daily forecast details"`
}

type DailyForecast struct {
	Date    string      `json:"date" jsonschema:"Forecast date"`
	Type    WeatherType `json:"type" jsonschema:"Weather type"`
	High    float64     `json:"high" jsonschema:"High temperature in Fahrenheit"`
	Low     float64     `json:"low" jsonschema:"Low temperature in Fahrenheit"`
}

// Custom schemas for specific types
customSchemas := map[reflect.Type]*jsonschema.Schema{
	reflect.TypeFor[Probability](): {
		Type:    "number",
		Minimum: jsonschema.Ptr(0.0),
		Maximum: jsonschema.Ptr(1.0),
	},
	reflect.TypeFor[WeatherType](): {
		Type: "string",
		Enum: []any{Sunny, PartlyCloudy, Rainy},
	},
}

// Generate schemas with custom types
opts := &jsonschema.ForOptions{TypeSchemas: customSchemas}
inputSchema, err := jsonschema.For[WeatherInput](opts)
if err != nil {
	log.Fatal(err)
}

// Customize generated schema
daysSchema := inputSchema.Properties["days"]
daysSchema.Minimum = jsonschema.Ptr(0.0)
daysSchema.Maximum = jsonschema.Ptr(10.0)

outputSchema, err := jsonschema.For[WeatherOutput](opts)
if err != nil {
	log.Fatal(err)
}

// Register with custom schemas
mcp.AddTool(server, &mcp.Tool{
	Name:         "get_weather",
	Description:  "Get weather forecast for a location",
	InputSchema:  inputSchema,
	OutputSchema: outputSchema,
}, weatherHandler)
```

### Tool Annotations

Add hints to help clients understand tool characteristics:

```go
tool := &mcp.Tool{
	Name:        "github_search_repos",
	Description: "Search GitHub repositories",
	Annotations: map[string]any{
		"title":           "Search GitHub Repositories",
		"readOnlyHint":    true,  // Tool does not modify state
		"destructiveHint": false, // Tool does not perform destructive operations
		"idempotentHint":  true,  // Repeated calls have same effect
		"openWorldHint":   true,  // Tool interacts with external systems
	},
}
mcp.AddTool(server, tool, searchReposHandler)
```

## Response Format Options

Support multiple output formats for flexibility. Use enum types for format selection:

```go
type ResponseFormat string

const (
	FormatMarkdown ResponseFormat = "markdown"
	FormatJSON     ResponseFormat = "json"
)

type SearchInput struct {
	Query  string         `json:"query" jsonschema:"Search query"`
	Format ResponseFormat `json:"format" jsonschema:"Output format: 'markdown' for human-readable or 'json' for machine-readable"`
}

func searchHandler(ctx context.Context, req *mcp.CallToolRequest, input SearchInput) (
	*mcp.CallToolResult, string, error,
) {
	// Fetch data
	results := fetchResults(input.Query)

	// Format based on preference
	if input.Format == FormatMarkdown {
		return nil, formatAsMarkdown(results), nil
	}

	// Return as JSON
	jsonData, err := json.Marshal(results)
	if err != nil {
		return mcp.NewToolResultError(fmt.Sprintf("Failed to marshal JSON: %v", err)), "", nil
	}
	return nil, string(jsonData), nil
}

func formatAsMarkdown(results []Result) string {
	var lines []string
	lines = append(lines, "# Search Results\n")
	for _, r := range results {
		lines = append(lines, fmt.Sprintf("## %s (%s)", r.Name, r.ID))
		lines = append(lines, fmt.Sprintf("- **Description**: %s", r.Description))
		lines = append(lines, "")
	}
	return strings.Join(lines, "\n")
}
```

**Markdown format**:
- Use headers, lists, and formatting for clarity
- Convert timestamps to human-readable format
- Show display names with IDs in parentheses
- Omit verbose metadata
- Group related information logically

**JSON format**:
- Return complete, structured data
- Include all available fields and metadata
- Use consistent field names and types

## Pagination Implementation

For tools that list resources:

```go
type ListInput struct {
	Limit  int `json:"limit" jsonschema:"Maximum results to return (1-100), default 20"`
	Offset int `json:"offset" jsonschema:"Number of results to skip for pagination, default 0"`
}

type ListOutput struct {
	Total      int      `json:"total" jsonschema:"Total number of items available"`
	Count      int      `json:"count" jsonschema:"Number of items in this response"`
	Offset     int      `json:"offset" jsonschema:"Current pagination offset"`
	Items      []Item   `json:"items" jsonschema:"List of items"`
	HasMore    bool     `json:"has_more" jsonschema:"Whether more results are available"`
	NextOffset *int     `json:"next_offset,omitempty" jsonschema:"Offset for next page, null if no more"`
}

func listItemsHandler(ctx context.Context, req *mcp.CallToolRequest, input ListInput) (
	*mcp.CallToolResult, ListOutput, error,
) {
	// Apply defaults
	if input.Limit == 0 {
		input.Limit = 20
	}
	if input.Limit < 1 || input.Limit > 100 {
		return mcp.NewToolResultError("Limit must be between 1 and 100"), ListOutput{}, nil
	}

	// Fetch from API with pagination
	data, total, err := apiList(ctx, input.Limit, input.Offset)
	if err != nil {
		return mcp.NewToolResultError(fmt.Sprintf("API error: %v", err)), ListOutput{}, nil
	}

	hasMore := total > input.Offset+len(data)
	var nextOffset *int
	if hasMore {
		next := input.Offset + len(data)
		nextOffset = &next
	}

	return nil, ListOutput{
		Total:      total,
		Count:      len(data),
		Offset:     input.Offset,
		Items:      data,
		HasMore:    hasMore,
		NextOffset: nextOffset,
	}, nil
}
```

## Character Limits and Truncation

Add a character limit constant to prevent overwhelming responses:

```go
const CharacterLimit = 25000 // Maximum response size in characters

func searchToolHandler(ctx context.Context, req *mcp.CallToolRequest, input SearchInput) (
	*mcp.CallToolResult, string, error,
) {
	// Fetch data
	data, err := fetchData(ctx, input)
	if err != nil {
		return mcp.NewToolResultError(err.Error()), "", nil
	}

	// Generate response
	result := formatResponse(data)

	// Check character limit and truncate if needed
	if len(result) > CharacterLimit {
		// Truncate data intelligently
		truncatedData := data[:max(1, len(data)/2)]

		response := map[string]any{
			"data":      truncatedData,
			"truncated": true,
			"message": fmt.Sprintf(
				"Response truncated from %d to %d items. Use 'offset' parameter or add filters.",
				len(data), len(truncatedData),
			),
		}

		jsonData, _ := json.Marshal(response)
		result = string(jsonData)
	}

	return nil, result, nil
}
```

## Error Handling

Provide clear, actionable error messages using `mcp.NewToolResultError`:

```go
import (
	"fmt"
	"net/http"
)

func handleAPIError(err error) *mcp.CallToolResult {
	// Handle HTTP errors
	if httpErr, ok := err.(*HTTPError); ok {
		switch httpErr.StatusCode {
		case http.StatusNotFound:
			return mcp.NewToolResultError("Error: Resource not found. Please check the ID is correct.")
		case http.StatusForbidden:
			return mcp.NewToolResultError("Error: Permission denied. You don't have access to this resource.")
		case http.StatusTooManyRequests:
			return mcp.NewToolResultError("Error: Rate limit exceeded. Please wait before making more requests.")
		case http.StatusUnauthorized:
			return mcp.NewToolResultError("Error: Authentication failed. Please check your API credentials.")
		default:
			return mcp.NewToolResultError(fmt.Sprintf("Error: API request failed with status %d", httpErr.StatusCode))
		}
	}

	// Handle timeout errors
	if isTimeout(err) {
		return mcp.NewToolResultError("Error: Request timed out. Please try again.")
	}

	// Generic error
	return mcp.NewToolResultError(fmt.Sprintf("Error: Unexpected error occurred: %v", err))
}

func toolHandler(ctx context.Context, req *mcp.CallToolRequest, input ToolInput) (
	*mcp.CallToolResult, ToolOutput, error,
) {
	data, err := callAPI(ctx, input)
	if err != nil {
		return handleAPIError(err), ToolOutput{}, nil
	}

	return nil, ToolOutput{Result: data}, nil
}
```

**Error handling best practices:**
- Return errors via `mcp.NewToolResultError()`, not Go errors
- Go errors (third parameter) should only be used for protocol-level failures
- Tool execution failures should set `IsError: true` in the result
- Provide specific, actionable guidance in error messages

## Shared Utilities

Extract common functionality into reusable functions:

```go
const (
	APIBaseURL     = "https://api.example.com/v1"
	DefaultTimeout = 30 * time.Second
)

// Shared HTTP client
var httpClient = &http.Client{
	Timeout: DefaultTimeout,
}

// Reusable API request function
func makeAPIRequest(ctx context.Context, method, endpoint string, body any) ([]byte, error) {
	var reqBody io.Reader
	if body != nil {
		jsonData, err := json.Marshal(body)
		if err != nil {
			return nil, fmt.Errorf("failed to marshal request: %w", err)
		}
		reqBody = bytes.NewReader(jsonData)
	}

	url := fmt.Sprintf("%s/%s", APIBaseURL, endpoint)
	req, err := http.NewRequestWithContext(ctx, method, url, reqBody)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer "+getAPIKey())

	resp, err := httpClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("request failed: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 400 {
		return nil, &HTTPError{StatusCode: resp.StatusCode}
	}

	return io.ReadAll(resp.Body)
}

// Shared formatting functions
func formatMarkdownList(items []Item) string {
	var lines []string
	for _, item := range items {
		lines = append(lines, fmt.Sprintf("- **%s** (%s): %s", item.Name, item.ID, item.Description))
	}
	return strings.Join(lines, "\n")
}
```

## Context and Cancellation

Always respect context cancellation for long-running operations:

```go
func longRunningHandler(ctx context.Context, req *mcp.CallToolRequest, input LongInput) (
	*mcp.CallToolResult, LongOutput, error,
) {
	// Check if context is already cancelled
	select {
	case <-ctx.Done():
		return mcp.NewToolResultError("Operation cancelled"), LongOutput{}, nil
	default:
	}

	// Perform work with context
	resultChan := make(chan result)
	go func() {
		// Long operation
		data := processData(input)
		resultChan <- data
	}()

	// Wait for result or cancellation
	select {
	case <-ctx.Done():
		return mcp.NewToolResultError("Operation cancelled"), LongOutput{}, nil
	case res := <-resultChan:
		return nil, LongOutput{Data: res}, nil
	}
}
```

## Progress Notifications

Report progress for long-running operations:

```go
func processingHandler(ctx context.Context, req *mcp.CallToolRequest, input ProcessInput) (
	*mcp.CallToolResult, ProcessOutput, error,
) {
	// Get progress token from request metadata
	progressToken := req.Params.Meta.ProgressToken

	// Only send progress if token is provided
	if progressToken != nil {
		// Progress reporting requires ServerSession access
		// This is typically done via middleware or session context
		session := getSessionFromContext(ctx)

		// Report progress at 25%
		session.NotifyProgress(ctx, &mcp.ProgressNotification{
			ProgressToken: *progressToken,
			Progress:      0.25,
			Total:         1.0,
		})

		// Continue processing...

		// Report progress at 75%
		session.NotifyProgress(ctx, &mcp.ProgressNotification{
			ProgressToken: *progressToken,
			Progress:      0.75,
			Total:         1.0,
		})
	}

	// Complete processing
	result := processData(input)
	return nil, ProcessOutput{Result: result}, nil
}
```

## Type Hints and Documentation

Use godoc-style comments for all exported types and functions:

```go
// SearchUsersInput defines the parameters for searching users.
// All fields are validated against constraints defined in jsonschema tags.
type SearchUsersInput struct {
	// Query is the search string to match against user names or emails.
	// Examples: "john", "eng-team", "@example.com"
	Query string `json:"query" jsonschema:"Search query to match against user names or emails"`

	// Limit is the maximum number of results to return.
	// Must be between 1 and 100. Default: 20.
	Limit int `json:"limit" jsonschema:"Maximum results to return (1-100)"`

	// Offset is the number of results to skip for pagination.
	// Default: 0.
	Offset int `json:"offset" jsonschema:"Pagination offset"`
}

// searchUsersHandler searches for users matching the query.
//
// This tool searches across all user profiles, supporting partial matches
// and various search filters. It does NOT create or modify users.
//
// Input constraints:
//   - query: minimum 2 characters, maximum 200 characters
//   - limit: must be between 1 and 100
//   - offset: must be >= 0
//
// Returns a SearchUsersOutput containing:
//   - total: total number of matching users
//   - count: number of users in this response
//   - offset: current pagination offset
//   - users: slice of matching users
//   - has_more: whether more results are available
//
// Error cases:
//   - Returns error result if limit is out of range
//   - Returns error result if API request fails
//   - Returns empty results if no users match query
func searchUsersHandler(
	ctx context.Context,
	req *mcp.CallToolRequest,
	input SearchUsersInput,
) (*mcp.CallToolResult, SearchUsersOutput, error) {
	// Implementation
}
```

## Complete Example

Below is a complete Go MCP server example:

```go
package main

import (
	"context"
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"time"

	"github.com/modelcontextprotocol/go-sdk/mcp"
)

const (
	APIBaseURL      = "https://api.example.com/v1"
	CharacterLimit  = 25000
	DefaultTimeout  = 30 * time.Second
)

// ResponseFormat defines output format options
type ResponseFormat string

const (
	FormatMarkdown ResponseFormat = "markdown"
	FormatJSON     ResponseFormat = "json"
)

// SearchUsersInput defines search parameters
type SearchUsersInput struct {
	Query  string         `json:"query" jsonschema:"Search string to match against user names or emails (e.g. 'john', 'engineering')"`
	Limit  int            `json:"limit" jsonschema:"Maximum results to return (1-100), default 20"`
	Offset int            `json:"offset" jsonschema:"Pagination offset, default 0"`
	Format ResponseFormat `json:"format" jsonschema:"Output format: 'markdown' or 'json'"`
}

// SearchUsersOutput defines search results
type SearchUsersOutput struct {
	Total   int          `json:"total" jsonschema:"Total users matching query"`
	Count   int          `json:"count" jsonschema:"Users in this response"`
	Offset  int          `json:"offset" jsonschema:"Current pagination offset"`
	Users   []UserResult `json:"users" jsonschema:"List of matching users"`
	HasMore bool         `json:"has_more" jsonschema:"More results available"`
}

// UserResult represents a user search result
type UserResult struct {
	ID    string `json:"id" jsonschema:"User ID (e.g. U123456789)"`
	Name  string `json:"name" jsonschema:"User's full name"`
	Email string `json:"email" jsonschema:"User's email address"`
	Team  string `json:"team,omitempty" jsonschema:"User's team name"`
}

// HTTPError represents an HTTP error response
type HTTPError struct {
	StatusCode int
	Message    string
}

func (e *HTTPError) Error() string {
	return fmt.Sprintf("HTTP %d: %s", e.StatusCode, e.Message)
}

// Shared HTTP client
var httpClient = &http.Client{Timeout: DefaultTimeout}

// makeAPIRequest performs an HTTP request to the API
func makeAPIRequest(ctx context.Context, method, endpoint string, params map[string]string) ([]byte, error) {
	url := fmt.Sprintf("%s/%s", APIBaseURL, endpoint)
	req, err := http.NewRequestWithContext(ctx, method, url, nil)
	if err != nil {
		return nil, fmt.Errorf("failed to create request: %w", err)
	}

	// Add query parameters
	q := req.URL.Query()
	for k, v := range params {
		q.Add(k, v)
	}
	req.URL.RawQuery = q.Encode()

	req.Header.Set("Content-Type", "application/json")
	req.Header.Set("Authorization", "Bearer YOUR_API_KEY")

	resp, err := httpClient.Do(req)
	if err != nil {
		return nil, fmt.Errorf("request failed: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode >= 400 {
		return nil, &HTTPError{StatusCode: resp.StatusCode, Message: resp.Status}
	}

	var result struct {
		Users []UserResult `json:"users"`
		Total int          `json:"total"`
	}

	if err := json.NewDecoder(resp.Body).Decode(&result); err != nil {
		return nil, fmt.Errorf("failed to decode response: %w", err)
	}

	return json.Marshal(result)
}

// handleAPIError converts errors to tool error results
func handleAPIError(err error) *mcp.CallToolResult {
	if httpErr, ok := err.(*HTTPError); ok {
		switch httpErr.StatusCode {
		case http.StatusNotFound:
			return mcp.NewToolResultError("Error: Resource not found. Please check the ID is correct.")
		case http.StatusForbidden:
			return mcp.NewToolResultError("Error: Permission denied. You don't have access to this resource.")
		case http.StatusTooManyRequests:
			return mcp.NewToolResultError("Error: Rate limit exceeded. Please wait before making more requests.")
		case http.StatusUnauthorized:
			return mcp.NewToolResultError("Error: Authentication failed. Please check your API credentials.")
		default:
			return mcp.NewToolResultError(fmt.Sprintf("Error: API request failed with status %d", httpErr.StatusCode))
		}
	}
	return mcp.NewToolResultError(fmt.Sprintf("Error: %v", err))
}

// formatMarkdown formats users as markdown
func formatMarkdown(users []UserResult, query string, total int) string {
	lines := []string{
		fmt.Sprintf("# User Search Results: '%s'", query),
		"",
		fmt.Sprintf("Found %d users (showing %d)", total, len(users)),
		"",
	}

	for _, user := range users {
		lines = append(lines, fmt.Sprintf("## %s (%s)", user.Name, user.ID))
		lines = append(lines, fmt.Sprintf("- **Email**: %s", user.Email))
		if user.Team != "" {
			lines = append(lines, fmt.Sprintf("- **Team**: %s", user.Team))
		}
		lines = append(lines, "")
	}

	return join(lines, "\n")
}

// searchUsersHandler implements user search
func searchUsersHandler(
	ctx context.Context,
	req *mcp.CallToolRequest,
	input SearchUsersInput,
) (*mcp.CallToolResult, string, error) {
	// Apply defaults
	if input.Limit == 0 {
		input.Limit = 20
	}
	if input.Format == "" {
		input.Format = FormatMarkdown
	}

	// Validate input
	if input.Limit < 1 || input.Limit > 100 {
		return mcp.NewToolResultError("Limit must be between 1 and 100"), "", nil
	}
	if input.Offset < 0 {
		return mcp.NewToolResultError("Offset must be >= 0"), "", nil
	}
	if len(input.Query) < 2 {
		return mcp.NewToolResultError("Query must be at least 2 characters"), "", nil
	}

	// Make API request
	params := map[string]string{
		"q":      input.Query,
		"limit":  fmt.Sprintf("%d", input.Limit),
		"offset": fmt.Sprintf("%d", input.Offset),
	}

	data, err := makeAPIRequest(ctx, "GET", "users/search", params)
	if err != nil {
		return handleAPIError(err), "", nil
	}

	var apiResp struct {
		Users []UserResult `json:"users"`
		Total int          `json:"total"`
	}
	if err := json.Unmarshal(data, &apiResp); err != nil {
		return mcp.NewToolResultError(fmt.Sprintf("Failed to parse response: %v", err)), "", nil
	}

	if len(apiResp.Users) == 0 {
		return nil, fmt.Sprintf("No users found matching '%s'", input.Query), nil
	}

	// Format response
	if input.Format == FormatMarkdown {
		markdown := formatMarkdown(apiResp.Users, input.Query, apiResp.Total)
		return nil, markdown, nil
	}

	// Return as JSON
	output := SearchUsersOutput{
		Total:   apiResp.Total,
		Count:   len(apiResp.Users),
		Offset:  input.Offset,
		Users:   apiResp.Users,
		HasMore: apiResp.Total > input.Offset+len(apiResp.Users),
	}

	jsonData, _ := json.Marshal(output)
	return nil, string(jsonData), nil
}

func main() {
	// Create server
	server := mcp.NewServer(&mcp.Implementation{
		Name:    "example-mcp",
		Version: "v1.0.0",
	}, nil)

	// Register tool
	mcp.AddTool(server, &mcp.Tool{
		Name:        "example_search_users",
		Description: "Search for users in the Example system by name, email, or team",
		Annotations: map[string]any{
			"title":           "Search Example Users",
			"readOnlyHint":    true,
			"destructiveHint": false,
			"idempotentHint":  true,
			"openWorldHint":   true,
		},
	}, searchUsersHandler)

	// Run server over stdio
	ctx := context.Background()
	if err := server.Run(ctx, &mcp.StdioTransport{}); err != nil {
		log.Fatal(err)
	}
}

func join(strs []string, sep string) string {
	result := ""
	for i, s := range strs {
		if i > 0 {
			result += sep
		}
		result += s
	}
	return result
}
```

---

## Advanced Features

### Multiple Transport Options

The Go SDK supports different transport mechanisms:

```go
// Stdio transport (for CLI tools, subprocess integration)
func main() {
	server := mcp.NewServer(&mcp.Implementation{Name: "example-mcp"}, nil)
	if err := server.Run(context.Background(), &mcp.StdioTransport{}); err != nil {
		log.Fatal(err)
	}
}

// HTTP/SSE transport (for web services)
func main() {
	server := mcp.NewServer(&mcp.Implementation{Name: "example-mcp"}, nil)

	http.Handle("/mcp", server.SSEHandler())
	log.Println("Server listening on :8080")
	log.Fatal(http.ListenAndServe(":8080", nil))
}

// Streamable HTTP transport (with automatic reconnection)
func main() {
	server := mcp.NewServer(&mcp.Implementation{Name: "example-mcp"}, nil)

	http.Handle("/mcp", server.StreamableHTTPHandler())
	log.Println("Server listening on :8080")
	log.Fatal(http.ListenAndServe(":8080", nil))
}
```

**Transport selection:**
- **Stdio**: Command-line tools, subprocess integration, Claude Code
- **HTTP/SSE**: Web services, remote access, 2024-11-05 protocol
- **Streamable HTTP**: Real-time updates, automatic reconnection, 2025-03-26 protocol

### Prompts

MCP servers can provide prompt templates:

```go
promptHandler := func(ctx context.Context, req *mcp.GetPromptRequest) (*mcp.GetPromptResult, error) {
	name := req.Params.Arguments["name"]
	return &mcp.GetPromptResult{
		Description: "Greeting prompt",
		Messages: []*mcp.PromptMessage{
			{
				Role:    "user",
				Content: &mcp.TextContent{Text: "Say hi to " + name},
			},
		},
	}, nil
}

server.AddPrompt(&mcp.Prompt{
	Name:        "greet",
	Description: "Generate a greeting",
	Arguments: []*mcp.PromptArgument{
		{
			Name:        "name",
			Description: "Name of the person to greet",
			Required:    true,
		},
	},
}, promptHandler)
```

### Resources

Expose data as MCP resources:

```go
// Register individual resource
resourceHandler := func(ctx context.Context, req *mcp.ReadResourceRequest) (*mcp.ReadResourceResult, error) {
	uri := req.Params.URI
	content, err := loadContent(uri)
	if err != nil {
		return nil, mcp.ResourceNotFoundError(uri)
	}
	return &mcp.ReadResourceResult{
		Contents: []*mcp.ResourceContents{{URI: uri, Text: content}},
	}, nil
}

server.AddResource(&mcp.Resource{
	URI:         "file:///docs/readme.md",
	Name:        "README",
	Description: "Project README",
}, resourceHandler)

// Register resource template for dynamic resources
server.AddResourceTemplate(&mcp.ResourceTemplate{
	URITemplate: "file:///docs/{name}.md",
	Name:        "Documentation",
	Description: "Project documentation files",
}, resourceHandler)
```

### Middleware

Add middleware for logging, authentication, or rate limiting:

```go
// Receiving middleware (runs before handling requests)
receivingMiddleware := func(next mcp.ReceivingMiddleware) mcp.ReceivingMiddleware {
	return func(ctx context.Context, req *mcp.JSONRPCRequest) (*mcp.JSONRPCResponse, error) {
		log.Printf("Received request: %s", req.Method)
		resp, err := next(ctx, req)
		log.Printf("Request completed: %s", req.Method)
		return resp, err
	}
}

// Sending middleware (runs before sending requests)
sendingMiddleware := func(next mcp.SendingMiddleware) mcp.SendingMiddleware {
	return func(ctx context.Context, req *mcp.JSONRPCRequest) (*mcp.JSONRPCResponse, error) {
		log.Printf("Sending request: %s", req.Method)
		return next(ctx, req)
	}
}

// Create server with middleware
server := mcp.NewServer(&mcp.Implementation{Name: "example-mcp"}, &mcp.ServerOptions{
	ReceivingMiddleware: []mcp.ReceivingMiddleware{receivingMiddleware},
	SendingMiddleware:   []mcp.SendingMiddleware{sendingMiddleware},
})
```

### Logging

Send log messages to clients:

```go
import "log/slog"

// Create logger that sends to MCP client
logger := slog.New(mcp.NewLoggingHandler(serverSession, nil))

// Use logger in tools
func toolHandler(ctx context.Context, req *mcp.CallToolRequest, input ToolInput) (
	*mcp.CallToolResult, ToolOutput, error,
) {
	logger.Info("Processing request", "query", input.Query)

	result, err := processRequest(input)
	if err != nil {
		logger.Error("Request failed", "error", err)
		return handleAPIError(err), ToolOutput{}, nil
	}

	logger.Info("Request completed successfully")
	return nil, result, nil
}
```

---

## Code Best Practices

### Code Composability and Reusability

Your implementation MUST prioritize composability and code reuse:

1. **Extract Common Functionality**:
   - Create reusable helper functions for operations used across multiple tools
   - Build shared HTTP clients for API requests instead of duplicating code
   - Centralize error handling logic in utility functions
   - Extract business logic into dedicated functions that can be composed
   - Extract shared formatting functionality

2. **Avoid Duplication**:
   - NEVER copy-paste similar code between tools
   - If you find yourself writing similar logic twice, extract it into a function
   - Common operations like pagination, filtering, and formatting should be shared
   - Authentication/authorization logic should be centralized

### Go-Specific Best Practices

1. **Use Context**: Always pass and respect `context.Context` for cancellation
2. **Struct Tags**: Use `json` and `jsonschema` tags for schema generation
3. **Error Handling**: Return tool errors via `mcp.NewToolResultError()`, not Go errors
4. **Type Safety**: Leverage Go's type system with strong typing
5. **Package Organization**: Group related functionality into packages
6. **Constants**: Define package-level constants in PascalCase
7. **Exported Names**: Export only what needs to be public (PascalCase)
8. **Comments**: Use godoc-style comments for all exported items

### Go Module Structure

```
example-mcp/
├── go.mod                 # Module definition
├── go.sum                 # Dependency checksums
├── main.go               # Entry point
├── tools/                # Tool implementations
│   ├── search.go
│   └── create.go
├── api/                  # API client
│   ├── client.go
│   └── errors.go
└── internal/             # Internal utilities
    ├── formatting/
    └── validation/
```

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
- [ ] All tools have descriptive names and documentation
- [ ] Return types are consistent across similar operations
- [ ] Error handling is implemented for all external calls
- [ ] Server name follows format: `{service}-mcp`
- [ ] All I/O operations respect context cancellation
- [ ] Common functionality is extracted into reusable functions
- [ ] Error messages are clear, actionable, and educational
- [ ] Outputs are properly validated and formatted

### Tool Configuration
- [ ] All tools implement `Name`, `Description`, and `Annotations`
- [ ] Annotations correctly set (readOnlyHint, destructiveHint, idempotentHint, openWorldHint)
- [ ] All tools use typed structs for input with jsonschema tags
- [ ] All struct fields have appropriate json and jsonschema tags
- [ ] All tools have godoc comments with input/output documentation
- [ ] Comments include complete schema structure for complex returns
- [ ] Schema validation is automatic via `mcp.AddTool`

### Advanced Features (where applicable)
- [ ] Progress notifications used for long-running operations
- [ ] Resources registered for appropriate data endpoints
- [ ] Prompts registered for reusable templates
- [ ] Middleware implemented for cross-cutting concerns
- [ ] Appropriate transport configured (stdio, HTTP, Streamable)

### Code Quality
- [ ] File includes proper imports from go-sdk
- [ ] Pagination is properly implemented where applicable
- [ ] Large responses check CharacterLimit and truncate with clear messages
- [ ] Filtering options are provided for potentially large result sets
- [ ] All functions respect context cancellation
- [ ] HTTP client usage follows best practices with timeouts
- [ ] Go module properly initialized (`go mod init`, `go mod tidy`)
- [ ] Constants are defined at package level

### Testing and Building
- [ ] Server builds successfully: `go build`
- [ ] All imports resolve correctly: `go mod tidy`
- [ ] Code passes `go vet ./...`
- [ ] Code is formatted: `gofmt -w .`
- [ ] Sample tool calls work as expected
- [ ] Error scenarios handled gracefully

### Copyright and Licensing
- [ ] All Go files have proper copyright header (if contributing to official SDK)
- [ ] Module has appropriate LICENSE file
