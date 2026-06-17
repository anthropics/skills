# Tools Overview

Tools are the primary mechanism for extending agent capabilities, enabling them to perform actions beyond simple text generation. Tools allow agents to interact with external systems, access data, and manipulate their environment.

Strands Agents Tools is a community-driven project that provides a powerful set of tools for your agents to use. For more information, see [Strands Agents Tools](community-tools-package.md).

## Adding Tools to Agents

Tools are passed to agents during initialization or at runtime, making them available for use throughout the agent's lifecycle. Once loaded, the agent can use these tools in response to user requests:

=== "Python"

    ```python
    from strands import Agent
    from strands_tools import calculator, file_read, shell

    # Add tools to our agent
    agent = Agent(
        tools=[calculator, file_read, shell]
    )

    # Agent will automatically determine when to use the calculator tool
    agent("What is 42 ^ 9")

    print("\n\n")  # Print new lines

    # Agent will use the shell and file reader tool when appropriate
    agent("Show me the contents of a single file in this directory")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:adding_tools"
    ```

We can see which tools are loaded in our agent:

=== "Python"

    In Python, you can access `agent.tool_names` for a list of tool names, and `agent.tool_registry.get_all_tools_config()` for a JSON representation including descriptions and input parameters:

    ```python
    print(agent.tool_names)

    print(agent.tool_registry.get_all_tools_config())
    ```

=== "TypeScript"

    In TypeScript, you can access the tools array directly:

    ```typescript
    // Access all tools
    console.log(agent.tools)
    ```


## Loading Tools from Files

=== "Python"

    Tools can also be loaded by passing a file path to our agents during initialization:

    ```python
    agent = Agent(tools=["/path/to/my_tool.py"])
    ```

{{ ts_not_supported_code() }}


### Auto-loading and reloading tools

=== "Python"


    Tools placed in your current working directory `./tools/` can be automatically loaded at agent initialization, and automatically reloaded when modified. This can be really useful when developing and debugging tools: simply modify the tool code and any agents using that tool will reload it to use the latest modifications!

    Automatic loading and reloading of tools in the `./tools/` directory is disabled by default. To enable this behavior, set `load_tools_from_directory=True` during `Agent` initialization:

    ```python
    from strands import Agent

    agent = Agent(load_tools_from_directory=True)
    ```
{{ ts_not_supported_code() }}



!!! note "Tool Loading Implications"
    When enabling automatic tool loading, any Python file placed in the `./tools/` directory will be executed by the agent. Under the shared responsibility model, it is your responsibility to ensure that only safe, trusted code is written to the tool loading directory, as the agent will automatically pick up and execute any tools found there.

## Using Tools

Tools can be invoked in two primary ways.

Agents have context about tool calls and their results as part of conversation history. See [Using State in Tools](../agents/state.md#using-state-in-tools) for more information.

### Natural Language Invocation

The most common way agents use tools is through natural language requests. The agent determines when and how to invoke tools based on the user's input:

=== "Python"

    ```python
    # Agent decides when to use tools based on the request
    agent("Please read the file at /path/to/file.txt")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:natural_language_invocation"
    ```

### Direct Method Calls

Tools can be invoked programmatically in addition to natural language invocation.

=== "Python"

    Every tool added to an agent becomes a method accessible directly on the agent object:

    ```python
    # Directly invoke a tool as a method
    result = agent.tool.file_read(path="/path/to/file.txt", mode="view")
    ```

    When calling tools directly as methods, always use keyword arguments - positional arguments are *not* supported:

    ```python
    # This will NOT work - positional arguments are not supported
    result = agent.tool.file_read("/path/to/file.txt", "view")  # ❌ Don't do this
    ```

    If a tool name contains hyphens, you can invoke the tool using underscores instead:

    ```python
    # Directly invoke a tool named "read-all"
    result = agent.tool.read_all(path="/path/to/file.txt")
    ```

=== "TypeScript"

    Find the tool in the `agent.tools` array and call its `invoke()` method. You need to provide both the input and a context object (when required) with the tool use details.

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:direct_invocation"
    ```


## Tool Executors

When models return multiple tool requests, you can control whether they execute concurrently or sequentially.

=== "Python"

    Agents use concurrent execution by default, but you can specify sequential execution for cases where order matters:

    ```python
    from strands import Agent
    from strands.tools.executors import SequentialToolExecutor

    # Concurrent execution (default)
    agent = Agent(tools=[weather_tool, time_tool])
    agent("What is the weather and time in New York?")

    # Sequential execution
    agent = Agent(
        tool_executor=SequentialToolExecutor(),
        tools=[screenshot_tool, email_tool]
    )
    agent("Take a screenshot and email it to my friend")
    ```

    For more details, see [Tool Executors](executors.md).

{{ ts_not_supported_code() }}

## Building & Loading Tools

### 1. Custom Tools

Build your own tools using the Strands SDK's tool interfaces. Both Python and TypeScript support creating custom tools, though with different approaches.



#### Function-Based Tools

=== "Python"

    Define any Python function as a tool by using the [`@tool`](../../../api-reference/python/tools/decorator.md#strands.tools.decorator.tool) decorator. Function decorated tools can be placed anywhere in your codebase and imported in to your agent's list of tools. 

    ```python
    import asyncio
    from strands import Agent, tool


    @tool
    def get_user_location() -> str:
        """Get the user's location."""

        # Implement user location lookup logic here
        return "Seattle, USA"


    @tool
    def weather(location: str) -> str:
        """Get weather information for a location.

        Args:
            location: City or location name
        """

        # Implement weather lookup logic here
        return f"Weather for {location}: Sunny, 72°F"


    @tool
    async def call_api() -> str:
        """Call API asynchronously.

        Strands will invoke all async tools concurrently.
        """

        await asyncio.sleep(5)  # simulated api call
        return "API result"


    def basic_example():
        agent = Agent(tools=[get_user_location, weather])
        agent("What is the weather like in my location?")


    async def async_example():
        agent = Agent(tools=[call_api])
        await agent.invoke_async("Can you call my API?")


    def main():
        basic_example()
        asyncio.run(async_example())
    ```

=== "TypeScript"


    Use the `tool()` function to create tools with [Zod](https://zod.dev/) schema validation. These tools can then be passed directly to your agents.

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:basic_tool"
    ```

    For more details on building custom tools, see [Creating Custom Tools](custom-tools.md).


#### Module-Based Tools

=== "Python"

    Tool modules can also provide single tools that don't use the decorator pattern, instead they define the `TOOL_SPEC` variable and a function matching the tool's name. In this example `weather.py`:

    ```python
    # weather.py

    from typing import Any
    from strands.types.tools import ToolResult, ToolUse

    TOOL_SPEC = {
        "name": "weather",
        "description": "Get weather information for a location",
        "inputSchema": {
            "json": {
                "type": "object",
                "properties": {
                    "location": {
                        "type": "string",
                        "description": "City or location name"
                    }
                },
                "required": ["location"]
            }
        }
    }

    # Function name must match tool name
    # May also be defined async similar to decorated tools
    def weather(tool: ToolUse, **kwargs: Any) -> ToolResult:
        tool_use_id = tool["toolUseId"]
        location = tool["input"]["location"]

        # Implement weather lookup logic here
        weather_info = f"Weather for {location}: Sunny, 72°F"

        return {
            "toolUseId": tool_use_id,
            "status": "success",
            "content": [{"text": weather_info}]
        }
    ```

    And finally our `agent.py` file that demonstrates loading the decorated `get_user_location` tool from a Python module, and the single non-decorated `weather` tool module:

    ```python
    # agent.py

    from strands import Agent
    import get_user_location
    import weather

    # Tools can be added to agents through Python module imports
    agent = Agent(tools=[get_user_location, weather])

    # Use the agent with the custom tools
    agent("What is the weather like in my location?")
    ```

    Tool modules can also be loaded by providing their module file paths:

    ```python
    from strands import Agent

    # Tools can be added to agents through file path strings
    agent = Agent(tools=["./get_user_location.py", "./weather.py"])

    agent("What is the weather like in my location?")
    ```

    For more details on building custom Python tools, see [Creating Custom Tools](custom-tools.md).


{{ ts_not_supported_code() }}



### 2. Vended Tools

Pre-built tools are available in both Python and TypeScript to help you get started quickly.

=== "Python"

    **Community Tools Package**

    For Python, Strands offers a [community-supported tools package]({{ tools_repo }}) with pre-built tools for development:

    ```python
    from strands import Agent
    from strands_tools import calculator, file_read, shell

    agent = Agent(tools=[calculator, file_read, shell])
    ```

    For a complete list of available tools, see [Community Tools Package](community-tools-package.md).

=== "TypeScript"

    **Vended Tools**

    TypeScript vended tools are included in the SDK at [`vended-tools/`]({{ ts_sdk_repo_home }}/src/vended-tools).
    The Community Tools Package (`strands-agents-tools`) is Python-only.

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:vended_tools"
    ```

    

### 3. Model Context Protocol (MCP) Tools

The [Model Context Protocol (MCP)](https://modelcontextprotocol.io) provides a standardized way to expose and consume tools across different systems. This approach is ideal for creating reusable tool collections that can be shared across multiple agents or applications.

=== "Python"

    ```python
    from mcp.client.sse import sse_client
    from strands import Agent
    from strands.tools.mcp import MCPClient

    # Connect to an MCP server using SSE transport
    sse_mcp_client = MCPClient(lambda: sse_client("http://localhost:8000/sse"))

    # Create an agent with MCP tools
    with sse_mcp_client:
        # Get the tools from the MCP server
        tools = sse_mcp_client.list_tools_sync()

        # Create an agent with the MCP server's tools
        agent = Agent(tools=tools)

        # Use the agent with MCP tools
        agent("Calculate the square root of 144")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/mcp-tools.ts:tools_overview_example"
    ```

For more information on using MCP tools, see [MCP Tools](mcp-tools.md).

## Tool Design Best Practices

### Effective Tool Descriptions

Language models rely heavily on tool descriptions to determine when and how to use them. Well-crafted descriptions significantly improve tool usage accuracy.

A good tool description should:

- Clearly explain the tool's purpose and functionality
- Specify when the tool should be used
- Detail the parameters it accepts and their formats
- Describe the expected output format
- Note any limitations or constraints

Example of a well-described tool:

=== "Python"

    ```python
    @tool
    def search_database(query: str, max_results: int = 10) -> list:
        """
        Search the product database for items matching the query string.

        Use this tool when you need to find detailed product information based on keywords,
        product names, or categories. The search is case-insensitive and supports fuzzy
        matching to handle typos and variations in search terms.

        This tool connects to the enterprise product catalog database and performs a semantic
        search across all product fields, providing comprehensive results with all available
        product metadata.

        Example response:
            [
                {
                    "id": "P12345",
                    "name": "Ultra Comfort Running Shoes",
                    "description": "Lightweight running shoes with...",
                    "price": 89.99,
                    "category": ["Footwear", "Athletic", "Running"]
                },
                ...
            ]

        Notes:
            - This tool only searches the product catalog and does not provide
              inventory or availability information
            - Results are cached for 15 minutes to improve performance
            - The search index updates every 6 hours, so very recent products may not appear
            - For real-time inventory status, use a separate inventory check tool

        Args:
            query: The search string (product name, category, or keywords)
                   Example: "red running shoes" or "smartphone charger"
            max_results: Maximum number of results to return (default: 10, range: 1-100)
                         Use lower values for faster response when exact matches are expected

        Returns:
            A list of matching product records, each containing:
            - id: Unique product identifier (string)
            - name: Product name (string)
            - description: Detailed product description (string)
            - price: Current price in USD (float)
            - category: Product category hierarchy (list)
        """

        # Implementation
        pass
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:search_database"
    ```
