# Ruby MCP Server Implementation Guide

## Overview

This document provides Ruby-specific best practices and examples for implementing MCP servers using the official MCP Ruby SDK gem (`mcp`). It covers server setup, tool registration with classes and blocks, resource and prompt handlers, transport options, and complete working examples.

---

## Quick Reference

### Key Imports
```ruby
require 'mcp'
```

### Server Initialization
```ruby
server = MCP::Server.new(
  name: 'service_mcp',
  version: '1.0.0',
  tools: [MyTool],
  resources: [my_resource],
  prompts: [MyPrompt]
)
```

### Tool Registration Pattern (Class)
```ruby
class MyTool < MCP::Tool
  tool_name 'service_action'
  description 'What this tool does and returns'
  input_schema(properties: { ... }, required: [...])
  annotations(read_only_hint: true)
  def self.call(**args, server_context:)
    MCP::Tool::Response.new([{ type: 'text', text: result }])
  end
end
```

### Tool Registration Pattern (Block)
```ruby
server.define_tool(name: 'service_action', description: '...', input_schema: { ... }) do |args, server_context|
  MCP::Tool::Response.new([{ type: 'text', text: result }])
end
```

---

## MCP Ruby SDK

The official Ruby SDK gem provides:
- `MCP::Server` for server initialization
- `MCP::Tool` base class for class-based tool definitions
- `define_tool` for block-based tool definitions
- `MCP::Resource` and `MCP::ResourceTemplate` for resources
- `MCP::Prompt` base class for prompt templates
- `StdioTransport` and `StreamableHTTPTransport`

**Two approaches for tools:**
- **Class-based** (recommended for complex tools): Subclass `MCP::Tool`
- **Block-based** (good for simple tools): Use `server.define_tool`

## Server Naming Convention

Ruby MCP servers should follow this naming pattern:
- **Format**: `{service}_mcp` (lowercase with underscores)
- **Examples**: `github_mcp`, `jira_mcp`, `stripe_mcp`

## Project Structure

```
{service}_mcp/
├── Gemfile
├── server.rb            # Entry point
├── lib/
│   ├── tools/
│   │   ├── search.rb
│   │   └── create.rb
│   ├── resources/
│   │   └── config.rb
│   ├── prompts/
│   │   └── analyze.rb
│   └── client.rb        # API client, auth
└── test/
    └── tools_test.rb
```

## Tool Implementation

### Class-Based Tool

```ruby
class SearchTool < MCP::Tool
  tool_name 'service_search'
  description 'Search for items by query. Returns matching records with ID, name, and status.'

  input_schema(
    properties: {
      query: { type: 'string', description: 'Search query string' },
      limit: { type: 'integer', description: 'Max results (1-100)', default: 20 }
    },
    required: ['query']
  )

  output_schema(
    properties: {
      total: { type: 'integer' },
      results: { type: 'array', items: { type: 'object' } }
    },
    required: ['total', 'results']
  )

  annotations(
    read_only_hint: true,
    destructive_hint: false,
    idempotent_hint: true,
    open_world_hint: true
  )

  def self.call(query:, limit: 20, server_context:)
    results = ApiClient.search(query, limit: limit)

    if results.empty?
      return MCP::Tool::Response.new(
        [{ type: 'text', text: "No results found for '#{query}'" }],
        is_error: true
      )
    end

    output = { total: results.length, results: results }

    MCP::Tool::Response.new(
      [{ type: 'text', text: output.to_json }],
      structured_content: output
    )
  end
end
```

### Block-Based Tool

```ruby
server.define_tool(
  name: 'service_ping',
  description: 'Check service connectivity. Returns status and latency.',
  input_schema: { properties: {}, required: [] },
  annotations: { read_only_hint: true, idempotent_hint: true }
) do |_args, server_context|
  start = Time.now
  status = ApiClient.ping
  latency = ((Time.now - start) * 1000).round(2)

  MCP::Tool::Response.new([{
    type: 'text',
    text: { status: status, latency_ms: latency }.to_json
  }])
end
```

## Resource Implementation

```ruby
resource = MCP::Resource.new(
  uri: 'config://app/settings',
  name: 'app-settings',
  description: 'Current application configuration',
  mime_type: 'application/json'
)

server = MCP::Server.new(name: 'service_mcp', resources: [resource])

server.resources_read_handler do |params|
  case params[:uri]
  when 'config://app/settings'
    [{ uri: params[:uri], mimeType: 'application/json', text: load_settings.to_json }]
  else
    raise "Unknown resource: #{params[:uri]}"
  end
end
```

### Resource Templates

```ruby
template = MCP::ResourceTemplate.new(
  uri_template: 'users://{user_id}/profile',
  name: 'user-profile',
  description: 'User profile data',
  mime_type: 'application/json'
)

server = MCP::Server.new(name: 'service_mcp', resource_templates: [template])
```

## Prompt Implementation

```ruby
class AnalyzePrompt < MCP::Prompt
  prompt_name 'analyze'
  description 'Analyze a topic in depth'

  arguments [
    MCP::Prompt::Argument.new(name: 'topic', description: 'Topic to analyze', required: true),
    MCP::Prompt::Argument.new(name: 'depth', description: 'Analysis depth', required: false)
  ]

  def self.template(args, server_context:)
    topic = args['topic'] || 'general'
    depth = args['depth'] || 'basic'

    MCP::Prompt::Result.new(
      description: "Analysis of #{topic}",
      messages: [
        MCP::Prompt::Message.new(role: 'user', content: MCP::Content::Text.new("Analyze: #{topic} at #{depth} depth"))
      ]
    )
  end
end
```

## Server Context

Pass contextual information to tools and prompts:

```ruby
server = MCP::Server.new(
  name: 'service_mcp',
  tools: [AuthenticatedTool],
  server_context: {
    user_id: current_user.id,
    auth_token: session[:token]
  }
)
```

## Transport Configuration

### stdio (local, default)

```ruby
transport = MCP::Server::Transports::StdioTransport.new(server)
transport.open
```

### Streamable HTTP

```ruby
transport = MCP::Server::Transports::StreamableHTTPTransport.new(server)
server.transport = transport
```

### Rails Integration

```ruby
class McpController < ApplicationController
  def index
    server = MCP::Server.new(
      name: 'rails_mcp',
      tools: [SearchTool],
      server_context: { user_id: current_user.id }
    )
    render json: server.handle_json(request.body.read)
  end
end
```

## Configuration

### Exception Reporting
```ruby
MCP.configure do |config|
  config.exception_reporter = ->(exception, server_context) {
    Bugsnag.notify(exception) { |report| report.add_metadata(:mcp, server_context) }
  }
end
```

### Instrumentation
```ruby
MCP.configure do |config|
  config.instrumentation_callback = ->(data) {
    StatsD.timing("mcp.#{data[:method]}.duration", data[:duration])
  }
end
```

## Error Handling

```ruby
class RiskyTool < MCP::Tool
  def self.call(data:, server_context:)
    result = risky_operation(data)
    MCP::Tool::Response.new([{ type: 'text', text: result }])
  rescue ValidationError => e
    MCP::Tool::Response.new(
      [{ type: 'text', text: "Invalid input: #{e.message}" }],
      is_error: true
    )
  end
end
```

## Complete Example

```ruby
#!/usr/bin/env ruby
require 'mcp'
require 'json'
require 'net/http'

class ListReposTool < MCP::Tool
  tool_name 'list_repos'
  description 'List repositories for an owner. Returns name, description, and star count.'

  input_schema(
    properties: {
      owner: { type: 'string', description: 'GitHub org or username' },
      per_page: { type: 'integer', description: 'Results per page (1-100)', default: 30 }
    },
    required: ['owner']
  )

  annotations(read_only_hint: true, idempotent_hint: true, open_world_hint: true)

  def self.call(owner:, per_page: 30, server_context:)
    token = ENV.fetch('API_TOKEN') { raise 'API_TOKEN required' }
    # ... fetch repos ...
    output = { repos: [{ name: 'example', stars: 42 }], total: 1 }
    MCP::Tool::Response.new(
      [{ type: 'text', text: output.to_json }],
      structured_content: output
    )
  end
end

server = MCP::Server.new(name: 'example_mcp', version: '1.0.0', tools: [ListReposTool])
transport = MCP::Server::Transports::StdioTransport.new(server)
transport.open
```

---

## Quality Checklist

Before finalizing your Ruby MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names are `snake_case` with consistent service prefix
- [ ] Error messages guide agents toward correct usage

### Implementation Quality
- [ ] All tools define `tool_name`, `description`, `input_schema`, and `annotations`
- [ ] Input schemas include property types, descriptions, and required arrays
- [ ] `output_schema` defined where applicable for structured content
- [ ] Error responses use `is_error: true` with actionable messages
- [ ] `structured_content` returned alongside text content where useful

### Ruby Quality
- [ ] Uses class-based tools for complex logic, blocks for simple tools
- [ ] Proper `rescue` error handling in all tool `call` methods
- [ ] No hardcoded credentials — all secrets via `ENV`
- [ ] Server context used for auth and request-scoped data
- [ ] Exception reporting configured for production

### Project Configuration
- [ ] Gemfile includes `gem 'mcp'`
- [ ] `bundle install` succeeds
- [ ] Server name follows format: `{service}_mcp`

### Testing
- [ ] `ruby server.rb` starts without errors
- [ ] Unit tests pass for all tool `call` methods
- [ ] Manual test with MCP Inspector: `npx @modelcontextprotocol/inspector ruby server.rb`
