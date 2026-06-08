# MCP Python SDK Guide

## Installation

```bash
pip install "mcp[cli]"
# or with uv (recommended)
uv add "mcp[cli]"
```

Requirements: Python >= 3.10
Latest: `mcp` v1.27.2 (May 2026). Author: Anthropic, PBC. License: MIT.

## FastMCP: High-Level API

FastMCP is the primary way to build MCP servers in Python. It uses decorators and type hints
to auto-generate schemas, eliminating manual JSON schema specification.

### Minimal Server

```python
from mcp.server.fastmcp import FastMCP

mcp = FastMCP("my-service-mcp")  # Naming convention: {service}_mcp

@mcp.tool()
def add(a: int, b: int) -> int:
    """Add two numbers. Returns their sum."""
    return a + b

if __name__ == "__main__":
    mcp.run()  # defaults to stdio
```

### Running Modes

```bash
# Development (with MCP Inspector)
uv run mcp dev server.py

# Install to Claude Desktop
uv run mcp install server.py

# Direct execution (stdio)
python server.py

# Streamable HTTP
python server.py --transport streamable-http --port 8000
```

## Full Tool Implementation with FastMCP

```python
from mcp.server.fastmcp import FastMCP
from pydantic import BaseModel, Field, field_validator, ConfigDict
from typing import Optional
from enum import Enum
import httpx
import json

mcp = FastMCP("github_mcp")

class ResponseFormat(str, Enum):
    MARKDOWN = "markdown"
    JSON = "json"

class CreateIssueInput(BaseModel):
    model_config = ConfigDict(
        str_strip_whitespace=True,
        validate_assignment=True,
        extra='forbid'
    )

    repo: str = Field(...,
        description="Repository in owner/repo format (e.g., 'octocat/hello-world')",
        pattern=r'^[\w.-]+/[\w.-]+$')
    title: str = Field(...,
        description="Issue title",
        min_length=1, max_length=256)
    body: Optional[str] = Field(None,
        description="Issue body in Markdown")
    response_format: ResponseFormat = Field(
        default=ResponseFormat.MARKDOWN,
        description="Output format: 'markdown' or 'json'")

    @field_validator('repo')
    @classmethod
    def validate_repo(cls, v: str) -> str:
        if '/' not in v:
            raise ValueError("repo must be in owner/repo format")
        return v

@mcp.tool(
    name="github_create_issue",
    annotations={
        "title": "Create GitHub Issue",
        "readOnlyHint": False,
        "destructiveHint": False,
        "idempotentHint": False,
        "openWorldHint": True
    }
)
async def github_create_issue(params: CreateIssueInput) -> str:
    """Create a new issue in a GitHub repository.

    Args:
        params: Validated input with repo, title, optional body and format.

    Returns:
        str: Created issue details (Markdown or JSON).

    Raises/Returns errors:
        "Error: 404" if repository not found
        "Error: 401" if GITHUB_TOKEN is invalid
        "Error: 422" if validation fails (e.g., empty title)
    """
    try:
        async with httpx.AsyncClient() as client:
            response = await client.post(
                f"https://api.github.com/repos/{params.repo}/issues",
                json={"title": params.title, "body": params.body},
                headers={
                    "Authorization": f"Bearer {get_token()}",
                    "Accept": "application/vnd.github+json"
                },
                timeout=30.0
            )
            response.raise_for_status()
            issue = response.json()

        if params.response_format == ResponseFormat.MARKDOWN:
            return f"## Issue #{issue['number']} Created\n\n**{issue['title']}**\n\n{issue['html_url']}"
        else:
            return json.dumps({
                "number": issue["number"],
                "url": issue["html_url"],
                "state": issue["state"]
            }, indent=2)

    except httpx.HTTPStatusError as e:
        return f"Error: {e.response.status_code} - {e.response.text}"
    except httpx.TimeoutException:
        return "Error: Request timed out. Please try again."
```

## Resource Registration

```python
@mcp.resource("github://repos/{owner}/{repo}/readme")
async def get_readme(owner: str, repo: str) -> str:
    """Fetch repository README as Markdown."""
    async with httpx.AsyncClient() as client:
        response = await client.get(
            f"https://api.github.com/repos/{owner}/{repo}/readme",
            headers={"Accept": "application/vnd.github.raw"},
            timeout=30.0
        )
        response.raise_for_status()
        return response.text

@mcp.resource("config://settings")
def get_settings() -> str:
    """Return current server configuration."""
    return json.dumps({"version": "1.0", "environment": "production"})
```

## Prompt Registration

```python
@mcp.prompt()
def code_review(language: str, focus: str = "quality") -> str:
    """Generate a code review prompt.

    Args:
        language: Programming language (e.g., 'python', 'typescript')
        focus: Review focus ('security', 'performance', 'quality')
    """
    return (
        f"Review the following {language} code for {focus} issues. "
        f"Be specific, cite line numbers, and suggest concrete improvements."
    )

# Multi-message prompt
from mcp.types import UserMessage, AssistantMessage

@mcp.prompt()
def debug_session(error_message: str) -> list[UserMessage]:
    """Multi-turn debugging prompt."""
    return [
        UserMessage(f"I'm getting this error: {error_message}"),
        UserMessage("Please help me debug this step by step.")
    ]
```

## Context Injection (Advanced)

FastMCP automatically injects `Context` when type-annotated:

```python
from mcp.server.fastmcp import FastMCP, Context

@mcp.tool()
async def process_large_dataset(path: str, ctx: Context) -> str:
    """Process a large file with progress reporting."""

    # Logging
    await ctx.info("Starting processing", {"path": path})
    await ctx.debug("Debug info here")

    # Progress reporting
    await ctx.report_progress(0.0, "Loading file...")
    data = await load_file(path)

    await ctx.report_progress(0.5, "Processing...")
    result = await process(data)

    await ctx.report_progress(1.0, "Complete")

    # Read another MCP resource
    config = await ctx.read_resource("config://settings")

    # Request user input (elicitation)
    api_key = await ctx.elicit(
        prompt="Enter API key for external service:",
        input_type="password"
    )

    return result

# Context capabilities:
# ctx.info(msg, data?)       - info log
# ctx.debug(msg, data?)      - debug log
# ctx.warning(msg, data?)    - warning log
# ctx.error(msg, data?)      - error log
# ctx.report_progress(p, msg) - 0.0-1.0 progress
# ctx.read_resource(uri)     - read MCP resource
# ctx.elicit(prompt, type)   - request user input
# ctx.fastmcp.name           - server name
```

## Lifespan Management

For persistent connections (DB, HTTP client pool):

```python
from contextlib import asynccontextmanager
import asyncpg

@asynccontextmanager
async def app_lifespan(app: FastMCP):
    # Startup
    db = await asyncpg.connect(dsn=os.environ["DATABASE_URL"])
    yield {"db": db}
    # Shutdown
    await db.close()

mcp = FastMCP("db_mcp", lifespan=app_lifespan)

@mcp.tool()
async def query_db(sql: str, ctx: Context) -> str:
    """Execute a read-only SQL query."""
    db = ctx.request_context.lifespan_state["db"]
    rows = await db.fetch(sql)
    return json.dumps([dict(r) for r in rows], indent=2)
```

## Transport Options

```python
# stdio (default, for local/Claude Desktop)
mcp.run()
# or
mcp.run(transport="stdio")

# Streamable HTTP (remote, scalable)
mcp.run(transport="streamable-http", host="0.0.0.0", port=8000)

# SSE (legacy, avoid for new work)
mcp.run(transport="sse", port=8000)

# WebSocket
mcp.run(transport="websocket", port=8000)
```

## ASGI Integration (Multi-Server Deployment)

Mount multiple MCP servers on a single Starlette app:

```python
from starlette.applications import Starlette
from starlette.routing import Mount

mcp1 = FastMCP("github_mcp")
mcp2 = FastMCP("slack_mcp")

app = Starlette(routes=[
    Mount("/github", app=mcp1.streamable_http_app()),
    Mount("/slack", app=mcp2.streamable_http_app()),
])

# Run with: uvicorn main:app
```

## Low-Level SDK (Without FastMCP)

For cases requiring more control:

```python
from mcp.server import Server
from mcp.server.stdio import stdio_server
from mcp.types import Tool, TextContent, CallToolResult
import mcp.types as types

server = Server("my-server")

@server.list_tools()
async def list_tools() -> list[Tool]:
    return [
        Tool(
            name="ping",
            description="Check server is alive",
            inputSchema={"type": "object", "properties": {}}
        )
    ]

@server.call_tool()
async def call_tool(name: str, arguments: dict) -> list[TextContent]:
    if name == "ping":
        return [TextContent(type="text", text="pong")]
    raise ValueError(f"Unknown tool: {name}")

async def main():
    async with stdio_server() as (read_stream, write_stream):
        await server.run(read_stream, write_stream, server.create_initialization_options())

import asyncio
asyncio.run(main())
```

## Type Annotations and Auto-Schema

FastMCP infers input schemas entirely from type annotations:

```python
# Simple types → JSON Schema primitives
@mcp.tool()
def greet(name: str, age: int = 0, active: bool = True) -> str:
    """Greet someone."""
    return f"Hello {name}, age {age}"
# Generates: { name: string, age?: integer, active?: boolean }

# Pydantic models → full JSON Schema with validation
class UserFilter(BaseModel):
    department: str
    min_age: int = Field(ge=0, le=150)
    roles: list[str] = Field(default_factory=list)

@mcp.tool()
async def find_users(filters: UserFilter) -> list[dict]:
    """Find users matching filters."""
    return await db_query(filters.model_dump())
```

## Structured Output

```python
from typing import TypedDict
from dataclasses import dataclass

# TypedDict return
class IssueResult(TypedDict):
    number: int
    url: str
    state: str

@mcp.tool()
async def get_issue(repo: str, number: int) -> IssueResult:
    """Returns structured issue data."""
    issue = await fetch_issue(repo, number)
    return {"number": issue.number, "url": issue.url, "state": issue.state}

# Pydantic model return (auto-serialized)
class DetailedReport(BaseModel):
    title: str
    sections: list[str]
    word_count: int

@mcp.tool()
async def generate_report(topic: str) -> DetailedReport:
    """Generate a report."""
    return DetailedReport(title=topic, sections=[], word_count=0)
```

## Testing

```python
# In-memory testing without subprocess
from mcp.server.fastmcp.testing import create_test_client

async def test_tools():
    async with create_test_client(mcp) as client:
        tools = await client.list_tools()
        assert any(t.name == "github_create_issue" for t in tools.tools)

        result = await client.call_tool("add", {"a": 2, "b": 3})
        assert result.content[0].text == "5"
```
