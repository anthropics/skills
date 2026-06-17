# MCP Calculator - Model Context Protocol Integration Example

This [example](https://github.com/strands-agents/docs/blob/main/docs/examples/python/mcp_calculator.py) demonstrates how to integrate Strands agents with external tools using the Model Context Protocol (MCP). It shows how to create a simple MCP server that provides calculator functionality and connect a Strands agent to use these tools.

## Overview

| Feature            | Description                            |
| ------------------ | -------------------------------------- |
| **Tool Used**      | MCPAgentTool                           |
| **Protocol**       | Model Context Protocol (MCP)           |
| **Complexity**     | Intermediate                           |
| **Agent Type**     | Single Agent                           |
| **Interaction**    | Command Line Interface                 |

## Tool Overview

The Model Context Protocol (MCP) enables Strands agents to use tools provided by external servers, connecting conversational AI with specialized functionality. The SDK provides the `MCPAgentTool` class which adapts MCP tools to the agent framework's tool interface. 
The `MCPAgentTool` is loaded via an MCPClient, which represents a connection from Strands to an external server that provides tools for the agent to use.

## Code Walkthrough

### First, create a simple MCP Server

The following code demonstrates how to create a simple MCP server that provides limited calculator functionality.

```python
from mcp.server import FastMCP

mcp = FastMCP("Calculator Server")

@mcp.tool(description="Add two numbers together")
def add(x: int, y: int) -> int:
    """Add two numbers and return the result."""
    return x + y

mcp.run(transport="streamable-http")
```

### Now, connect the server to the Strands agent

Now let's walk through how to connect a Strands agent to our MCP server:

```python
from mcp.client.streamable_http import streamablehttp_client
from strands import Agent
from strands.tools.mcp.mcp_client import MCPClient

def create_streamable_http_transport():
   return streamablehttp_client("http://localhost:8000/mcp/")

streamable_http_mcp_client = MCPClient(create_streamable_http_transport)

# Use the MCP server in a context manager
with streamable_http_mcp_client:
    # Get the tools from the MCP server
    tools = streamable_http_mcp_client.list_tools_sync()
    
    # Create an agent with the MCP tools
    agent = Agent(tools=tools)
```
At this point, the agent has successfully connected to the MCP server and retrieved the calculator tools. These MCP tools have been converted into standard AgentTools that the agent can use just like any other tools provided to it. The agent now has full access to the calculator functionality without needing to know the implementation details of the MCP server.


### Using the Tool

Users can interact with the calculator tools through conversational queries:

```python
# Let the agent handle the tool selection and parameter extraction
response = agent("What is 125 plus 375?")
response = agent("If I have 1000 and spend 246, how much do I have left?")
response = agent("What is 24 multiplied by 7 divided by 3?")
```

### Direct Method Access

For developers who need programmatic control, Strands also supports direct tool invocation:

```python
with streamable_http_mcp_client:
    result = streamable_http_mcp_client.call_tool_sync(
        tool_use_id="tool-123",
        name="add",
        arguments={"x": 125, "y": 375}
    )
    
    # Process the result
    print(f"Calculation result: {result['content'][0]['text']}")
```

### Explicit Tool Call through Agent
```python
with streamable_http_mcp_client:
   tools = streamable_http_mcp_client.list_tools_sync()

   # Create an agent with the MCP tools
   agent = Agent(tools=tools)
   result = agent.tool.add(x=125, y=375)

   # Process the result
   print(f"Calculation result: {result['content'][0]['text']}")
```

### Sample Queries and Responses

**Query 1**: What is 125 plus 375?

**Response**:
```
I'll calculate 125 + 375 for you.

Using the add tool:
- First number (x): 125
- Second number (y): 375

The result of 125 + 375 = 500
```

**Query 2**: If I have 1000 and spend 246, how much do I have left?

**Response**:
```
I'll help you calculate how much you have left after spending $246 from $1000.

This requires subtraction:
- Starting amount (x): 1000
- Amount spent (y): 246

Using the subtract tool:
1000 - 246 = 754

You have $754 left after spending $246 from your $1000.
```

## Extending the Example

The MCP calculator example can be extended in several ways. You could implement additional calculator functions like square root or trigonometric functions. A web UI could be built that connects to the same MCP server. The system could be expanded to connect to multiple MCP servers that provide different tool sets. You might also implement a custom transport mechanism instead of Streamable HTTP or add authentication to the MCP server to control access to tools.

## Conclusion

The Strands Agents SDK provides first-class support for the Model Context Protocol, making it easy to extend your agents with external tools. As demonstrated in this walkthrough, you can connect your agent to MCP servers with just a few lines of code. The SDK handles all the complexities of tool discovery, parameter extraction, and result formatting, allowing you to focus on building your application.


By leveraging the Strands Agents SDK's MCP support, you can rapidly extend your agent's capabilities with specialized tools while maintaining a clean separation between your agent logic and tool implementations.
