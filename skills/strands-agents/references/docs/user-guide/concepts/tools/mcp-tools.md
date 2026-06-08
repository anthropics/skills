# Model Context Protocol (MCP) Tools

The [Model Context Protocol (MCP)](https://modelcontextprotocol.io) is an open protocol that standardizes how applications provide context to Large Language Models. Strands Agents integrates with MCP to extend agent capabilities through external tools and services.

MCP enables communication between agents and MCP servers that provide additional tools. Strands includes built-in support for connecting to MCP servers and using their tools in both Python and TypeScript.

## Quick Start

=== "Python"

    ```python
    from mcp import stdio_client, StdioServerParameters
    from strands import Agent
    from strands.tools.mcp import MCPClient

    # Create MCP client with stdio transport
    mcp_client = MCPClient(lambda: stdio_client(
        StdioServerParameters(
            command="uvx",
            args=["awslabs.aws-documentation-mcp-server@latest"]
        )
    ))

    # Pass MCP client directly to agent - lifecycle managed automatically
    agent = Agent(tools=[mcp_client])
    agent("What is AWS Lambda?")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:quick_start"
    ```

## Integration Approaches

=== "Python"

    **Managed Integration (Recommended)**

    The `MCPClient` implements the `ToolProvider` interface, enabling direct usage in the Agent constructor with automatic lifecycle management:

    ```python
    from mcp import stdio_client, StdioServerParameters
    from strands import Agent
    from strands.tools.mcp import MCPClient

    mcp_client = MCPClient(lambda: stdio_client(
        StdioServerParameters(
            command="uvx",
            args=["awslabs.aws-documentation-mcp-server@latest"]
        )
    ))

    # Direct usage - connection lifecycle managed automatically
    agent = Agent(tools=[mcp_client])
    response = agent("What is AWS Lambda?")
    ```

    **Manual Context Management**

    For cases requiring explicit control over the MCP session lifecycle, use context managers:

    ```python
    with mcp_client:
        tools = mcp_client.list_tools_sync()
        agent = Agent(tools=tools)
        agent("What is AWS Lambda?")  # Must be within context
    ```

=== "TypeScript"

    **Direct Integration**

    `McpClient` instances are passed directly to the agent. The client connects lazily on first use:

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:direct_integration"
    ```

    Tools can also be listed explicitly if needed:

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:explicit_tools"
    ```

## Transport Options

Both Python and TypeScript support multiple transport mechanisms for connecting to MCP servers.

### Standard I/O (stdio)

For command-line tools and local processes that implement the MCP protocol:

=== "Python"

    ```python
    from mcp import stdio_client, StdioServerParameters
    from strands import Agent
    from strands.tools.mcp import MCPClient

    # For macOS/Linux:
    stdio_mcp_client = MCPClient(lambda: stdio_client(
        StdioServerParameters(
            command="uvx",
            args=["awslabs.aws-documentation-mcp-server@latest"]
        )
    ))

    # For Windows:
    stdio_mcp_client = MCPClient(lambda: stdio_client(
        StdioServerParameters(
            command="uvx",
            args=[
                "--from",
                "awslabs.aws-documentation-mcp-server@latest",
                "awslabs.aws-documentation-mcp-server.exe"
            ]
        )
    ))

    with stdio_mcp_client:
        tools = stdio_mcp_client.list_tools_sync()
        agent = Agent(tools=tools)
        response = agent("What is AWS Lambda?")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:stdio_transport"
    ```

### Streamable HTTP

For HTTP-based MCP servers that use Streamable HTTP transport:

=== "Python"

    ```python
    from mcp.client.streamable_http import streamablehttp_client
    from strands import Agent
    from strands.tools.mcp import MCPClient

    streamable_http_mcp_client = MCPClient(
        lambda: streamablehttp_client("http://localhost:8000/mcp")
    )

    with streamable_http_mcp_client:
        tools = streamable_http_mcp_client.list_tools_sync()
        agent = Agent(tools=tools)
    ```

    Additional properties like authentication can be configured:

    ```python
    import os
    from mcp.client.streamable_http import streamablehttp_client
    from strands.tools.mcp import MCPClient

    github_mcp_client = MCPClient(
        lambda: streamablehttp_client(
            url="https://api.githubcopilot.com/mcp/",
            headers={"Authorization": f"Bearer {os.getenv('MCP_PAT')}"}
        )
    )
    ```

    #### AWS IAM 

    For MCP servers on AWS that use SigV4 authentication with IAM credentials, you can conveniently use the [`mcp-proxy-for-aws`](https://pypi.org/project/mcp-proxy-for-aws/) package to handle AWS credential management and request signing automatically. See the [detailed guide](https://dev.to/aws/no-oauth-required-an-mcp-client-for-aws-iam-k1o) for more information.

    First, install the package:

    ```bash
    pip install mcp-proxy-for-aws
    ```

    Then you use it like any other transport:

    ```python
    from mcp_proxy_for_aws.client import aws_iam_streamablehttp_client
    from strands.tools.mcp import MCPClient

    mcp_client = MCPClient(lambda: aws_iam_streamablehttp_client(
        endpoint="https://your-service.us-east-1.amazonaws.com/mcp",
        aws_region="us-east-1",
        aws_service="bedrock-agentcore"
    ))
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:streamable_http"
    ```

### Server-Sent Events (SSE)

=== "Python"

    For HTTP-based MCP servers that use Server-Sent Events transport:

    ```python
    from mcp.client.sse import sse_client
    from strands import Agent
    from strands.tools.mcp import MCPClient

    sse_mcp_client = MCPClient(lambda: sse_client("http://localhost:8000/sse"))

    with sse_mcp_client:
        tools = sse_mcp_client.list_tools_sync()
        agent = Agent(tools=tools)
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:sse_transport"
    ```

## Using Multiple MCP Servers

Combine tools from multiple MCP servers in a single agent:

=== "Python"

    ```python
    from mcp import stdio_client, StdioServerParameters
    from mcp.client.sse import sse_client
    from strands import Agent
    from strands.tools.mcp import MCPClient

    # Create multiple clients
    sse_mcp_client = MCPClient(lambda: sse_client("http://localhost:8000/sse"))
    stdio_mcp_client = MCPClient(lambda: stdio_client(
        StdioServerParameters(command="python", args=["path/to/mcp_server.py"])
    ))

    # Manual approach - explicit context management
    with sse_mcp_client, stdio_mcp_client:
        tools = sse_mcp_client.list_tools_sync() + stdio_mcp_client.list_tools_sync()
        agent = Agent(tools=tools)

    # Managed approach
    agent = Agent(tools=[sse_mcp_client, stdio_mcp_client])
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:multiple_servers"
    ```

## Client Configuration

=== "Python"

    Python's `MCPClient` supports tool filtering and name prefixing to manage tools from multiple servers.

    **Tool Filtering**

    Control which tools are loaded using the `tool_filters` parameter:

    ```python
    from mcp import stdio_client, StdioServerParameters
    from strands.tools.mcp import MCPClient
    import re

    # String matching - loads only specified tools
    filtered_client = MCPClient(
        lambda: stdio_client(StdioServerParameters(
            command="uvx",
            args=["awslabs.aws-documentation-mcp-server@latest"]
        )),
        tool_filters={"allowed": ["search_documentation", "read_documentation"]}
    )

    # Regex patterns
    regex_client = MCPClient(
        lambda: stdio_client(StdioServerParameters(
            command="uvx",
            args=["awslabs.aws-documentation-mcp-server@latest"]
        )),
        tool_filters={"allowed": [re.compile(r"^search_.*")]}
    )

    # Combined filters - applies allowed first, then rejected
    combined_client = MCPClient(
        lambda: stdio_client(StdioServerParameters(
            command="uvx",
            args=["awslabs.aws-documentation-mcp-server@latest"]
        )),
        tool_filters={
            "allowed": [re.compile(r".*documentation$")],
            "rejected": ["read_documentation"]
        }
    )
    ```

    **Tool Name Prefixing**

    Prevent name conflicts when using multiple MCP servers:

    ```python
    aws_docs_client = MCPClient(
        lambda: stdio_client(StdioServerParameters(
            command="uvx",
            args=["awslabs.aws-documentation-mcp-server@latest"]
        )),
        prefix="aws_docs"
    )

    other_client = MCPClient(
        lambda: stdio_client(StdioServerParameters(
            command="uvx",
            args=["other-mcp-server@latest"]
        )),
        prefix="other"
    )

    # Tools will be named: aws_docs_search_documentation, other_search, etc.
    agent = Agent(tools=[aws_docs_client, other_client])
    ```

=== "TypeScript"

    TypeScript's `McpClient` accepts optional application metadata:

    ```typescript
    const mcpClient = new McpClient({
      applicationName: 'My Agent App',
      applicationVersion: '1.0.0',
      transport: new StdioClientTransport({
        command: 'npx',
        args: ['-y', 'some-mcp-server'],
      }),
    })
    ```

    Tool filtering and prefixing are not currently supported in TypeScript.

## Direct Tool Invocation

While tools are typically invoked by the agent based on user requests, MCP tools can also be called directly:

=== "Python"

    ```python
    result = mcp_client.call_tool_sync(
        tool_use_id="tool-123",
        name="calculator",
        arguments={"x": 10, "y": 20}
    )
    print(f"Result: {result['content'][0]['text']}")
    ```

=== "TypeScript"

    ```typescript
    // Get tools and find the target tool
    const tools = await mcpClient.listTools()
    const calcTool = tools.find(t => t.name === 'calculator')

    // Call directly through the client
    const result = await mcpClient.callTool(calcTool, { x: 10, y: 20 })
    ```

## Implementing an MCP Server

Custom MCP servers can be created to extend agent capabilities:

=== "Python"

    ```python
    from mcp.server import FastMCP

    # Create an MCP server
    mcp = FastMCP("Calculator Server")

    # Define a tool
    @mcp.tool(description="Calculator tool which performs calculations")
    def calculator(x: int, y: int) -> int:
        return x + y

    # Run the server with SSE transport
    mcp.run(transport="sse")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:mcp_server"
    ```

For more information on implementing MCP servers, see the [MCP documentation](https://modelcontextprotocol.io).

## Advanced Usage

=== "Python"

    ### Elicitation

    An MCP server can request additional information from the user by sending an elicitation request. Set up an elicitation callback to handle these requests:

    ```python
    # server.py
    from mcp.server import FastMCP
    from pydantic import BaseModel, Field

    class ApprovalSchema(BaseModel):
        username: str = Field(description="Who is approving?")

    server = FastMCP("mytools")

    @server.tool()
    async def delete_files(paths: list[str]) -> str:
        result = await server.get_context().elicit(
            message=f"Do you want to delete {paths}",
            schema=ApprovalSchema,
        )
        if result.action != "accept":
            return f"User {result.data.username} rejected deletion"

        # Perform deletion...
        return f"User {result.data.username} approved deletion"

    server.run()
    ```

    ```python
    # client.py
    from mcp import stdio_client, StdioServerParameters
    from mcp.types import ElicitResult
    from strands import Agent
    from strands.tools.mcp import MCPClient

    async def elicitation_callback(context, params):
        print(f"ELICITATION: {params.message}")
        # Get user confirmation...
        return ElicitResult(
            action="accept",
            content={"username": "myname"}
        )

    client = MCPClient(
        lambda: stdio_client(
            StdioServerParameters(command="python", args=["/path/to/server.py"])
        ),
        elicitation_callback=elicitation_callback,
    )

    with client:
        agent = Agent(tools=client.list_tools_sync())
        result = agent("Delete 'a/b/c.txt' and share the name of the approver")
    ```

    For more information on elicitation, see the [MCP specification](https://modelcontextprotocol.io/specification/draft/client/elicitation).

{{ ts_not_supported_code() }}

## Best Practices

- **Tool Descriptions**: Provide clear descriptions for tools to help the agent understand when and how to use them
- **Error Handling**: Return informative error messages when tools fail to execute properly
- **Security**: Consider security implications when exposing tools via MCP, especially for network-accessible servers
- **Connection Management**: In Python, always use context managers (`with` statements) to ensure proper cleanup of MCP connections
- **Timeouts**: Set appropriate timeouts for tool calls to prevent hanging on long-running operations

## Troubleshooting

### MCPClientInitializationError (Python)

Tools relying on an MCP connection must be used within a context manager. Operations will fail when the agent is used outside the `with` statement block.

```python
# Correct
with mcp_client:
    agent = Agent(tools=mcp_client.list_tools_sync())
    response = agent("Your prompt")  # Works

# Incorrect
with mcp_client:
    agent = Agent(tools=mcp_client.list_tools_sync())
response = agent("Your prompt")  # Fails - outside context
```

### Connection Failures

Connection failures occur when there are problems establishing a connection with the MCP server. Verify that:

- The MCP server is running and accessible
- Network connectivity is available and firewalls allow the connection
- The URL or command is correct and properly formatted

### Tool Discovery Issues

If tools aren't being discovered:

- Confirm the MCP server implements the `list_tools` method correctly
- Verify all tools are registered with the server

### Tool Execution Errors

When tool execution fails:

- Verify tool arguments match the expected schema
- Check server logs for detailed error information
