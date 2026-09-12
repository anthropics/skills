# PHP MCP Server Implementation Guide

## Overview

This document provides PHP-specific best practices and examples for implementing MCP servers using the official PHP SDK (`mcp/sdk`), maintained in collaboration with The PHP Foundation. It covers attribute-based tool discovery, resource and prompt handlers, transport options, and complete working examples.

---

## Quick Reference

### Installation
```bash
composer require mcp/sdk
```

### Server Initialization (Attribute Discovery)
```php
$server = Server::builder()
    ->setServerInfo('service-mcp-server', '1.0.0')
    ->setDiscovery(__DIR__, ['src'])
    ->build();
```

### Tool Registration Pattern (Attribute)
```php
#[McpTool(name: 'service_action')]
public function myAction(string $param): string {
    return "Result: $param";
}
```

---

## MCP PHP SDK

The official PHP SDK provides:
- `Server::builder()` for fluent server construction
- `#[McpTool]` attribute for automatic tool discovery
- `#[McpResource]` and `#[McpResourceTemplate]` for resources
- `#[McpPrompt]` for prompt templates
- `#[Schema]` attribute for input validation constraints
- `#[CompletionProvider]` for parameter autocompletion
- `StdioTransport` and `StreamableHttpTransport`

**Two approaches:**
- **Attribute discovery** (recommended): Annotate methods with `#[McpTool]` and let the SDK auto-discover them
- **Manual registration**: Use `addTool()` on the builder for programmatic control

## Server Naming Convention

PHP MCP servers should follow this naming pattern:
- **Format**: `{service}-mcp-server` (lowercase with hyphens)
- **Examples**: `github-mcp-server`, `jira-mcp-server`, `stripe-mcp-server`

## Project Structure

```
{service}-mcp-server/
├── composer.json
├── server.php           # Entry point
├── src/
│   ├── Tools/
│   │   ├── Search.php
│   │   └── Manage.php
│   ├── Resources/
│   │   └── Config.php
│   ├── Prompts/
│   │   └── Analyze.php
│   └── Client.php       # API client, auth
└── tests/
    └── ToolsTest.php
```

## Tool Implementation

### Simple Tool with Attribute

```php
<?php
namespace App\Tools;

use Mcp\Capability\Attribute\McpTool;

class Search
{
    /**
     * Search for items by query. Returns matching records with ID, name, and status.
     *
     * @param string $query Search query string
     * @param int $limit Maximum results to return (1-100)
     * @return array Search results
     */
    #[McpTool(name: 'service_search')]
    public function search(string $query, int $limit = 20): array
    {
        $results = $this->apiClient->search($query, $limit);

        if (empty($results)) {
            throw new \InvalidArgumentException("No results found for '{$query}'");
        }

        return [
            'total' => count($results),
            'results' => $results,
        ];
    }
}
```

### Tool with Schema Validation

```php
use Mcp\Capability\Attribute\{McpTool, Schema};

class UserManager
{
    #[McpTool(name: 'service_create_user')]
    public function createUser(
        #[Schema(format: 'email')]
        string $email,

        #[Schema(minimum: 18, maximum: 120)]
        int $age,

        #[Schema(pattern: '^[A-Z][a-z]+$', description: 'Capitalized first name')]
        string $firstName
    ): array {
        return ['id' => uniqid(), 'email' => $email, 'age' => $age, 'firstName' => $firstName];
    }
}
```

### Tool with Rich Content

```php
use Mcp\Schema\Content\{TextContent, ImageContent};

class Reports
{
    #[McpTool(name: 'service_generate_report')]
    public function generateReport(string $type): array
    {
        return [
            new TextContent('Report generated:'),
            TextContent::code($this->buildReport($type), 'json'),
            new TextContent('Summary: All checks passed.'),
        ];
    }
}
```

## Resource Implementation

### Static Resource

```php
use Mcp\Capability\Attribute\McpResource;

class ConfigProvider
{
    #[McpResource(uri: 'config://app/settings', name: 'app_settings', mimeType: 'application/json')]
    public function getSettings(): array
    {
        return ['version' => '1.0.0', 'debug' => false, 'features' => ['auth', 'logging']];
    }
}
```

### Resource Template

```php
use Mcp\Capability\Attribute\McpResourceTemplate;

class UserProvider
{
    #[McpResourceTemplate(
        uriTemplate: 'user://{userId}/profile/{section}',
        name: 'user_profile',
        description: 'User profile data by section',
        mimeType: 'application/json'
    )]
    public function getUserProfile(string $userId, string $section): array
    {
        return $this->users[$userId][$section]
            ?? throw new \InvalidArgumentException("Profile section not found");
    }
}
```

## Prompt Implementation

```php
use Mcp\Capability\Attribute\McpPrompt;

class PromptGenerator
{
    #[McpPrompt(name: 'code_review')]
    public function reviewCode(string $language, string $code, string $focus = 'general'): array
    {
        return [
            ['role' => 'assistant', 'content' => 'You are an expert code reviewer.'],
            ['role' => 'user', 'content' => "Review this {$language} code focusing on {$focus}:\n\n```{$language}\n{$code}\n```"],
        ];
    }
}
```

## Completion Providers

```php
use Mcp\Capability\Attribute\{McpPrompt, CompletionProvider};

#[McpPrompt]
public function generateContent(
    #[CompletionProvider(values: ['blog', 'article', 'tutorial', 'guide'])]
    string $contentType,

    #[CompletionProvider(values: ['beginner', 'intermediate', 'advanced'])]
    string $difficulty
): array {
    return [['role' => 'user', 'content' => "Create a {$difficulty} level {$contentType}"]];
}
```

## Transport Configuration

### stdio (local, default)

```php
use Mcp\Server\Transport\StdioTransport;

$transport = new StdioTransport();
$server->run($transport);
```

### Streamable HTTP

```php
use Mcp\Server\Transport\StreamableHttpTransport;
use Nyholm\Psr7\Factory\Psr17Factory;

$psr17Factory = new Psr17Factory();
$request = $psr17Factory->createServerRequestFromGlobals();
$transport = new StreamableHttpTransport($request, $psr17Factory, $psr17Factory);
$response = $server->run($transport);
```

### Session Management

```php
$server = Server::builder()
    ->setServerInfo('service-mcp-server', '1.0.0')
    ->setSession(ttl: 7200)  // 2 hours
    ->build();
```

## Error Handling

The SDK automatically converts exceptions into JSON-RPC error responses:

```php
#[McpTool(name: 'service_divide')]
public function divide(float $a, float $b): float
{
    if ($b === 0.0) {
        throw new \InvalidArgumentException('Division by zero is not allowed');
    }
    return $a / $b;
}
```

## Caching for Performance

```php
use Symfony\Component\Cache\Adapter\FilesystemAdapter;
use Symfony\Component\Cache\Psr16Cache;

$cache = new Psr16Cache(new FilesystemAdapter('mcp-discovery'));

$server = Server::builder()
    ->setServerInfo('service-mcp-server', '1.0.0')
    ->setDiscovery(basePath: __DIR__, scanDirs: ['src'], excludeDirs: ['vendor', 'tests'], cache: $cache)
    ->build();
```

## Complete Example

```php
#!/usr/bin/env php
<?php
declare(strict_types=1);
require_once __DIR__ . '/vendor/autoload.php';

use Mcp\Server;
use Mcp\Server\Transport\StdioTransport;
use Mcp\Capability\Attribute\McpTool;

class RepoTools
{
    /**
     * List repositories for an owner. Returns name, description, and star count.
     */
    #[McpTool(name: 'list_repos')]
    public function listRepos(string $owner, int $perPage = 30): array
    {
        $token = getenv('API_TOKEN') ?: throw new \RuntimeException('API_TOKEN required');
        // ... fetch repos ...
        return ['repos' => [['name' => 'example', 'stars' => 42]], 'total' => 1];
    }
}

$server = Server::builder()
    ->setServerInfo('example-mcp-server', '1.0.0')
    ->setDiscovery(__DIR__, ['.'])
    ->build();

$transport = new StdioTransport();
$server->run($transport);
```

### Claude Desktop Configuration

```json
{
  "mcpServers": {
    "php-server": {
      "command": "php",
      "args": ["/absolute/path/to/server.php"]
    }
  }
}
```

---

## Quality Checklist

Before finalizing your PHP MCP server implementation, ensure:

### Strategic Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names are `snake_case` with consistent service prefix
- [ ] Error messages guide agents toward correct usage

### Implementation Quality
- [ ] All tools use `#[McpTool]` attribute with explicit `name`
- [ ] PHPDoc comments serve as tool descriptions (auto-extracted)
- [ ] `#[Schema]` attributes used for input validation constraints
- [ ] Exceptions thrown for invalid inputs (SDK converts to error responses)
- [ ] Return types are arrays or content objects

### PHP Quality
- [ ] PHP 8.2+ with `declare(strict_types=1)`
- [ ] PSR-4 autoloading configured in `composer.json`
- [ ] No hardcoded credentials — all secrets via `getenv()`
- [ ] Discovery caching enabled for production
- [ ] Proper exception handling in all tool methods

### Project Configuration
- [ ] `composer.json` includes `mcp/sdk`
- [ ] `composer install` succeeds
- [ ] Server name follows format: `{service}-mcp-server`

### Testing
- [ ] `php server.php` starts without errors
- [ ] PHPUnit tests pass for all tool methods
- [ ] Manual test with MCP Inspector: `npx @modelcontextprotocol/inspector php server.php`
