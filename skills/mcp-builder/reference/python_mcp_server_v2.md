# Python MCP Server Implementation Guide (SDK v2)

This guide covers building MCP servers with **v2 of the MCP Python SDK** (`mcp` 2.x), where the high-level server class is `MCPServer`. v1 called it `FastMCP`; if the project pins `mcp<2` or imports `mcp.server.fastmcp`, use the [v1 guide](./python_mcp_server.md) or migrate first (see [Migrating a v1 Server](#migrating-a-v1-server)).

The full v2 documentation index is `https://py.sdk.modelcontextprotocol.io/llms.txt`; every page is also served as markdown at its `index.md` URL. The examples here were checked against `mcp` 2.3.0.

---

## Quick Reference

### Install

```bash
uv init my-mcp-server && cd my-mcp-server
uv add "mcp[cli]>=2" httpx
uv add --dev pytest anyio
```

`mcp` 2.x no longer depends on `httpx` (it moved to `httpx2`), so add `httpx` yourself if your tools call an HTTP API with it.

### A Server in One Screen

```python
from typing import Annotated

from pydantic import Field

from mcp.server import MCPServer
from mcp.types import ToolAnnotations

mcp = MCPServer("example_mcp", instructions="Example service: users and teams. Use for user lookups.")


@mcp.tool(
    title="Greet",
    annotations=ToolAnnotations(read_only_hint=True, open_world_hint=False),
    structured_output=False,
)
def example_greet(name: Annotated[str, Field(description="Who to greet")]) -> str:
    """Greet someone by name."""
    return f"Hello, {name}!"


if __name__ == "__main__":
    mcp.run()  # stdio by default
```

### v1 → v2 at a Glance

| v1 (`mcp` 1.x) | v2 (`mcp` 2.x) |
|---|---|
| `from mcp.server.fastmcp import FastMCP` | `from mcp.server import MCPServer` |
| `from mcp.server.fastmcp import Context` | `from mcp.server.mcpserver import Context` |
| `from mcp.server.fastmcp.exceptions import ToolError` | `from mcp.server.mcpserver.exceptions import ToolError` |
| `from mcp import McpError` | `from mcp import MCPError` |
| `FastMCP("x", port=8000, stateless_http=True)` | `MCPServer("x")` + `mcp.run(transport="streamable-http", port=8000, stateless_http=True)` |
| `ToolAnnotations(readOnlyHint=True)` | `ToolAnnotations(read_only_hint=True)` (camelCase is still on the wire) |
| `result.isError`, `tool.inputSchema` | `result.is_error`, `tool.input_schema` |
| `ctx.fastmcp` | `ctx.mcp_server` |
| `MCP_*` environment variables configure the server | Not read any more: pass values to the constructor |
| `httpx` arrives with `mcp` | Add `httpx` yourself if you use it |

---

## Project Setup

```toml
# pyproject.toml
[project]
name = "example-mcp"
version = "0.1.0"
requires-python = ">=3.10"
dependencies = ["mcp[cli]>=2,<3", "httpx>=0.27"]

[project.scripts]
example-mcp = "example_mcp.server:main"

[build-system]
requires = ["hatchling"]
build-backend = "hatchling.build"

[dependency-groups]
dev = ["pytest>=8", "anyio>=4.9"]
```

- Keep the server in a package (`src/example_mcp/server.py`) with a `main()` that calls `mcp.run()`, so it installs as a command and runs with `uvx example-mcp`
- Put the run call under `if __name__ == "__main__":`: `mcp dev`, `mcp run` and your tests import the module, and the guard keeps an import from starting a server
- Name the server `{service}_mcp`, without version numbers

---

## Calling the Upstream API

Create the HTTP client once, in a **lifespan**, and reach it from tools through the injected `Context`:

```python
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from dataclasses import dataclass

import httpx

from mcp.server import MCPServer
from mcp.server.mcpserver import Context


@dataclass
class AppContext:
    http: httpx.AsyncClient


@asynccontextmanager
async def lifespan(server: MCPServer) -> AsyncIterator[AppContext]:
    async with httpx.AsyncClient(base_url="https://api.example.com/v1", timeout=30) as http:
        yield AppContext(http=http)


mcp = MCPServer("example_mcp", lifespan=lifespan)


@mcp.tool()
async def example_ping(ctx: Context[AppContext]) -> str:
    """Check that the Example API is reachable."""
    response = await ctx.request_context.lifespan_context.http.get("/ping")
    return f"Example API answered {response.status_code}"
```

- The lifespan runs once: entered before the first request, exited when the server stops
- `ctx: Context[AppContext]` is injected by its annotation and never appears in the tool's input schema; the type parameter makes `lifespan_context` typed
- Send what the API needs (API key, `User-Agent`, version header) in one place: the client's `headers`
- Map HTTP statuses and timeouts to messages that say how to recover, and raise them as `ToolError` (see [Errors](#errors)): in v2 an unexpected exception reaches the model only as `Error executing tool <name>`, without its text
- Use `async def` for tools that do I/O. A plain `def` tool also works: v2 runs it on a worker thread, so it never blocks the server, but `asyncio.get_running_loop()` inside it raises

---

## Designing Tools

### Names and Descriptions

- Use snake_case, action-oriented names with a service prefix: `slack_send_message`, `github_create_issue`
- The tool name is the function name; the description is the docstring (or `description=`). Say what the tool does, what it returns, and when to use a sibling tool instead
- Set `title=` for the display name clients show
- Set `instructions=` on `MCPServer`: with tool search, Claude Code loads only tool names and server instructions up front (see [Claude Code's tool search](https://code.claude.com/docs/en/mcp#scale-with-mcp-tool-search))

### Annotations

Annotations are hints for clients, for example to auto-approve read-only tools or confirm destructive ones. They never change how the SDK runs the tool. In v2 they are snake_case keyword arguments on `ToolAnnotations`:

```python
from mcp.types import ToolAnnotations

READ_ONLY = ToolAnnotations(read_only_hint=True, open_world_hint=True)
EDITS = ToolAnnotations(destructive_hint=True, idempotent_hint=True, open_world_hint=True)
```

| Annotation | Set to `True` when the tool... |
|---|---|
| `read_only_hint` | does not modify anything |
| `destructive_hint` | may delete or overwrite data |
| `idempotent_hint` | can be repeated with the same arguments with no extra effect |
| `open_world_hint` | talks to an external system (most API tools) |

### Input Schemas

Type hints are the input schema. Describe and constrain arguments with `Annotated` and a Pydantic `Field`:

```python
from enum import Enum
from typing import Annotated

from pydantic import Field


class ResponseFormat(str, Enum):
    MARKDOWN = "markdown"
    JSON = "json"


@mcp.tool(structured_output=False)
async def example_search_users(
    query: Annotated[str, Field(min_length=2, max_length=200, description="Text to match against names and emails")],
    limit: Annotated[int, Field(ge=1, le=100, description="Maximum number of users to return")] = 20,
    offset: Annotated[int, Field(ge=0, description="Number of matches to skip, for pagination")] = 0,
    response_format: ResponseFormat = ResponseFormat.MARKDOWN,
) -> str:
    """Search users by name or email."""
    ...
```

- `Field(description=...)` becomes the argument's JSON Schema `description`, the only documentation the model gets for it
- Parameters with defaults are optional; `Literal[...]` and `Enum` become JSON Schema enums
- Arguments that fail validation never reach your function: the model gets an `is_error=True` result naming the field, for example `Input should be less than or equal to 100`, and can retry
- For many related arguments, take one Pydantic model parameter instead; the model fills it in as a JSON object and you receive a validated instance

### Output: Markdown, JSON, and Structured Content

In v2 the **return type annotation is the output schema**. A tool annotated `-> str`, `-> int` or `-> SomeModel` gets an `output_schema`, and every result carries the value twice: as text in `content` (what the model reads) and as `structured_content` (typed data for the client application). For a `str` the structured copy is `{"result": "..."}`.

- Tools that return text for the model (Markdown, or a JSON string chosen by a `response_format` argument): pass `structured_output=False` to `@mcp.tool()`, so the result is text only and the tool has no `output_schema`
- Tools whose output is always the same JSON shape: return a Pydantic model (or `TypedDict`). The SDK publishes its schema, validates the return value against it, and sends it as both `structured_content` and JSON text
- Markdown for the model: headers and lists, human-readable dates, display names with IDs in parentheses, no bookkeeping fields

### Pagination

List and search tools take `limit` and `offset` and say where the next page starts:

```python
next_offset = offset + len(users)
has_more = total > next_offset
page = {"total": total, "count": len(users), "offset": offset, "users": users, "has_more": has_more}
if has_more:
    page["next_offset"] = next_offset
```

In Markdown mode, end the text with how to get more, e.g. `More results: call again with offset=20.`

### Character Limit

Cap responses with a `CHARACTER_LIMIT` (25,000 characters is a good default; Claude Code warns above 10,000 tokens and saves text over 50,000 characters to a file; see [MCP output limits](https://code.claude.com/docs/en/mcp#mcp-output-limits-and-warnings)). Stay under it by returning **fewer items**, never by cutting text, so `next_offset` still points at the first item left out. Measure the text the tool sends, including page fields:

```python
text = render(users)
while len(users) > 1 and len(text) > CHARACTER_LIMIT:
    users = users[: (len(users) + 1) // 2]
    text = render(users)
```

### Errors

A tool can fail three ways, and v2 treats each differently:

- **`ToolError`** (`from mcp.server.mcpserver.exceptions import ToolError`): the call returns `is_error=True` and the model reads `Error executing tool <name>: <your message>`. Use it for anything a better call could fix: a not-found ID, a rate limit, a malformed query. Say how to recover
- **Any other exception**: still `is_error=True`, but the model sees only `Error executing tool <name>`; the message and traceback go to the server log. Catch upstream errors and re-raise them as `ToolError` with a useful message
- **`MCPError`** (`from mcp import MCPError`): the whole request fails with a JSON-RPC error that the host handles and the model never sees. Use it only when no retry by the model can help (a missing client capability, a server not ready)

Never *return* an error message as a normal result: it arrives with `is_error=False` and looks like a successful answer.

---

## Complete Example

One module, two tools. `example_search_users` shows pagination, the character limit and the two output formats; `example_get_user` shows structured output from a Pydantic model. The HTTP client comes from `build_client()`, which tests replace with a mock transport (see [Verify Your Server](#verify-your-server)).

```python
#!/usr/bin/env python3
"""MCP server for the Example API. Serves stdio by default, Streamable HTTP when TRANSPORT=http."""

import json
import os
from collections.abc import AsyncIterator
from contextlib import asynccontextmanager
from dataclasses import dataclass
from enum import Enum
from typing import Annotated, Any

import httpx
from pydantic import BaseModel, Field

from mcp.server import MCPServer
from mcp.server.mcpserver import Context
from mcp.server.mcpserver.exceptions import ToolError
from mcp.types import ToolAnnotations

API_BASE_URL = "https://api.example.com/v1"
CHARACTER_LIMIT = 25_000
READ_ONLY = ToolAnnotations(read_only_hint=True, open_world_hint=True)


class ResponseFormat(str, Enum):
    MARKDOWN = "markdown"
    JSON = "json"


class User(BaseModel):
    id: str
    name: str
    email: str
    team: str | None = None


# ---- Upstream API client: created once in the lifespan ----


def build_client() -> httpx.AsyncClient:
    api_key = os.environ.get("EXAMPLE_API_KEY", "")
    return httpx.AsyncClient(
        base_url=API_BASE_URL,
        headers={"Authorization": f"Bearer {api_key}", "Accept": "application/json"},
        timeout=30,
    )


@dataclass
class AppContext:
    http: httpx.AsyncClient


@asynccontextmanager
async def lifespan(server: MCPServer) -> AsyncIterator[AppContext]:
    async with build_client() as http:
        yield AppContext(http=http)


def http_error_message(status: int) -> str:
    """Messages the model can act on."""
    return {
        401: "The Example API rejected the API key. Check EXAMPLE_API_KEY.",
        403: "The API key has no access to this resource.",
        404: "Not found. Check the ID, or search for it with example_search_users.",
        429: "Rate limit exceeded. Wait a minute before making more requests.",
    }.get(status, f"The Example API returned HTTP {status}. Try again later.")


async def api_get(ctx: Context[AppContext], path: str, params: dict[str, Any] | None = None) -> Any:
    try:
        response = await ctx.request_context.lifespan_context.http.get(path, params=params)
    except httpx.TimeoutException:
        raise ToolError("The Example API did not respond within 30 seconds. Try again, or narrow the query.") from None
    if response.is_error:
        raise ToolError(http_error_message(response.status_code))
    return response.json()


mcp = MCPServer(
    "example_mcp",
    instructions="Example API (users and teams). Use to find users by name or email and to read a user's details.",
    lifespan=lifespan,
)


# ---- Tools ----


def render_page(users: list[dict[str, Any]], total: int, offset: int, response_format: ResponseFormat) -> str:
    next_offset = offset + len(users)
    has_more = total > next_offset
    if response_format is ResponseFormat.JSON:
        page: dict[str, Any] = {"total": total, "count": len(users), "offset": offset, "users": users, "has_more": has_more}
        if has_more:
            page["next_offset"] = next_offset
        return json.dumps(page)
    lines = [f"Found {total} users (showing {len(users)} from offset {offset})", ""]
    lines += [f"- **{u['name']}** ({u['id']}): {u['email']}" for u in users]
    if has_more:
        lines += ["", f"More results: call again with offset={next_offset}."]
    return "\n".join(lines)


@mcp.tool(title="Search users", annotations=READ_ONLY, structured_output=False)
async def example_search_users(
    query: Annotated[str, Field(min_length=2, max_length=200, description="Text to match against names and emails")],
    ctx: Context[AppContext],
    limit: Annotated[int, Field(ge=1, le=100, description="Maximum number of users to return")] = 20,
    offset: Annotated[int, Field(ge=0, description="Number of matches to skip, for pagination")] = 0,
    response_format: ResponseFormat = ResponseFormat.MARKDOWN,
) -> str:
    """Search users by name or email. Returns matching users with their IDs; pass an ID to example_get_user
    for details. Example: query="john", limit=5."""
    data = await api_get(ctx, "/users", {"q": query, "limit": limit, "offset": offset})
    users, total = data["users"], data["total"]
    if not users:
        return f"No users match {query!r}."
    text = render_page(users, total, offset, response_format)
    while len(users) > 1 and len(text) > CHARACTER_LIMIT:
        users = users[: (len(users) + 1) // 2]
        text = render_page(users, total, offset, response_format)
    return text


@mcp.tool(title="Get user", annotations=READ_ONLY)
async def example_get_user(
    user_id: Annotated[str, Field(min_length=1, description="User ID from example_search_users, e.g. 'u_123'")],
    ctx: Context[AppContext],
) -> User:
    """Get one user's details by ID."""
    return User.model_validate(await api_get(ctx, f"/users/{user_id}"))


def main() -> None:
    if os.environ.get("TRANSPORT") == "http":
        mcp.run(transport="streamable-http", port=int(os.environ.get("PORT", "3000")))
    else:
        mcp.run()


if __name__ == "__main__":
    main()
```

---

## Serving

### stdio (Local Servers)

`mcp.run()` serves stdio: the host starts your module as a subprocess and speaks over stdin and stdout. stdout is the protocol channel, so log to stderr (Python's `logging` does by default) and never `print()` to stdout.

### Streamable HTTP (Remote Servers)

```python
mcp.run(transport="streamable-http", port=3000)  # serves http://127.0.0.1:3000/mcp
```

- Transport options go to `run()`, not to `MCPServer(...)`: `host`, `port`, `streamable_http_path`, `json_response`, `stateless_http`, `transport_security`
- `host` defaults to `127.0.0.1`; on loopback DNS-rebinding protection turns on automatically. To serve a real hostname, pass `transport_security=TransportSecuritySettings(allowed_hosts=[...], allowed_origins=[...])` from `mcp.server.transport_security`
- To mount the server in an existing ASGI app, build it with `mcp.streamable_http_app()`
- Authentication: `https://py.sdk.modelcontextprotocol.io/run/authorization/index.md`

---

## Resources and Prompts

```python
from mcp.server.mcpserver.exceptions import ResourceNotFoundError

TEAMS = {"core": "Core platform team"}


@mcp.resource("example://teams/{team_id}")
def team(team_id: str) -> str:
    """One team's description."""
    if team_id not in TEAMS:
        raise ResourceNotFoundError(f"No team {team_id!r}.")
    return TEAMS[team_id]


@mcp.prompt()
def review_user(user_id: str) -> str:
    """Review a user's account."""
    return f"Look up user {user_id} with example_get_user and summarise anything unusual."
```

- Resources are application-controlled data; a URI with `{param}` is a template
- Resource handlers have no `is_error` channel: raise `ResourceNotFoundError` (or `ResourceError`) and the client gets a protocol error
- Prompts are user-invoked templates; the returned string becomes a user message

---

## Verify Your Server

`Client` from the SDK connects **in memory** when you pass it the server object: no subprocess, no port. Test the real tools, with the upstream API replaced by `httpx.MockTransport`:

```python
# tests/test_server.py
import httpx
import pytest

from mcp import Client

import example_mcp.server as server


def fake_api(request: httpx.Request) -> httpx.Response:
    if request.url.path == "/v1/users":
        users = [{"id": "u_1", "name": "John Smith", "email": "john@example.com"}]
        return httpx.Response(200, json={"users": users, "total": 3})
    if request.url.path == "/v1/users/u_1":
        return httpx.Response(200, json={"id": "u_1", "name": "John Smith", "email": "john@example.com"})
    return httpx.Response(404)


@pytest.fixture
def anyio_backend():
    return "asyncio"


@pytest.fixture
async def client(monkeypatch):
    monkeypatch.setattr(
        server, "build_client",
        lambda: httpx.AsyncClient(base_url=server.API_BASE_URL, transport=httpx.MockTransport(fake_api)),
    )
    async with Client(server.mcp) as c:
        yield c


@pytest.mark.anyio
async def test_tools(client):
    tools = {t.name for t in (await client.list_tools()).tools}
    assert tools == {"example_search_users", "example_get_user"}

    page = await client.call_tool("example_search_users", {"query": "john", "limit": 1})
    assert not page.is_error and "More results: call again with offset=1." in page.content[0].text

    user = await client.call_tool("example_get_user", {"user_id": "u_1"})
    assert user.structured_content["email"] == "john@example.com"

    missing = await client.call_tool("example_get_user", {"user_id": "nope"})
    assert missing.is_error and "Check the ID" in missing.content[0].text

    invalid = await client.call_tool("example_search_users", {"query": "j"})
    assert invalid.is_error  # rejected by min_length before the tool runs
```

- Run with `uv run pytest`; the lifespan runs inside `Client(...)`, so the patched `build_client` is what the tools use
- Assert on results, not exceptions: tool failures come back as `is_error=True` results
- For manual exploration, `uv run mcp dev src/example_mcp/server.py` opens the MCP Inspector
- To test the installed command over stdio, connect `Client` to it as a subprocess; see `https://py.sdk.modelcontextprotocol.io/client/index.md`

---

## More Features

| To... | See |
|---|---|
| Report progress from a long-running tool | `https://py.sdk.modelcontextprotocol.io/handlers/progress/index.md` |
| Handle cancellation | `https://py.sdk.modelcontextprotocol.io/handlers/cancellation/index.md` |
| Ask the user for input mid-call (elicitation) | `https://py.sdk.modelcontextprotocol.io/handlers/elicitation/index.md` |
| Return images and audio | `https://py.sdk.modelcontextprotocol.io/servers/media/index.md` |
| Add OAuth to an HTTP server | `https://py.sdk.modelcontextprotocol.io/run/authorization/index.md` |
| Deploy and scale over HTTP | `https://py.sdk.modelcontextprotocol.io/run/deploy/index.md` |

---

## Migrating a v1 Server

There is no codemod for Python. Work through the [v1 → v2 table](#v1--v2-at-a-glance), then the official guide at `https://py.sdk.modelcontextprotocol.io/migration/index.md`. The changes most servers hit:

1. Change the dependency to `mcp>=2,<3` and add `httpx` if you use it
2. Replace `mcp.server.fastmcp` imports with `mcp.server` / `mcp.server.mcpserver` (same submodule layout)
3. Move `host`, `port`, `stateless_http`, `json_response` and the other transport options from the constructor to `run()`
4. Rename camelCase attributes you read on SDK types to snake_case (`is_error`, `input_schema`, `structured_content`) and use `ToolAnnotations(read_only_hint=...)`
5. Replace `McpError` with `MCPError`, and check every `raise MCPError` inside a tool: in v2 it fails the whole request instead of returning `is_error=True`. Use `ToolError` for errors the model should see
6. Replace configuration through `MCP_*` environment variables with constructor arguments
7. Run your tests: sync tools now run on a worker thread, and unexpected exceptions no longer show their text to the model

---

## Quality Checklist

### Tool Design
- [ ] Tools enable complete workflows, not just API endpoint wrappers
- [ ] Tool names are snake_case with a service prefix
- [ ] Every tool has a `title`, a docstring that says when to use it, and correct `annotations`
- [ ] The server sets `instructions` that say what it is for, key words first
- [ ] Arguments use `Annotated[..., Field(...)]` with constraints and descriptions
- [ ] List and search tools paginate with `limit` / `offset` and say how to get the next page
- [ ] Responses stay under `CHARACTER_LIMIT` by returning fewer items
- [ ] Text-for-the-model tools use `structured_output=False`; always-JSON tools return a Pydantic model
- [ ] Upstream failures are raised as `ToolError` with a message that says how to recover

### Implementation
- [ ] `mcp>=2,<3` in dependencies, plus `httpx` if used
- [ ] Shared clients are created once in the lifespan, not per call
- [ ] I/O-bound tools are `async def`; HTTP calls have a timeout
- [ ] Nothing prints to stdout on the stdio transport
- [ ] Transport options are passed to `run()`

### Verification
- [ ] Tests call every tool through `Client(mcp)` with the upstream API mocked
- [ ] One invalid input is rejected and one upstream error comes back as a readable tool error
- [ ] The server starts with `uv run mcp dev` and lists its tools in the Inspector
