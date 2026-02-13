# Creating Custom Tools

There are multiple approaches to defining custom tools in Strands, with differences between Python and TypeScript implementations.

=== "Python"

    Python supports three approaches to defining tools:

    * **Python functions with the [`@tool`](../../../api-reference/python/tools/decorator.md#strands.tools.decorator.tool) decorator**: Transform regular Python functions into tools by adding a simple decorator. This approach leverages Python's docstrings and type hints to automatically generate tool specifications.

    * **Class-based tools with the [`@tool`](../../../api-reference/python/tools/decorator.md#strands.tools.decorator.tool) decorator**: Create tools within classes to maintain state and leverage object-oriented programming patterns.

    * **Python modules following a specific format**: Define tools by creating Python modules that contain a tool specification and a matching function. This approach gives you more control over the tool's definition and is useful for dependency-free implementations of tools.


=== "TypeScript"

    TypeScript supports two main approaches:

    * **tool() function with [Zod](https://zod.dev/) schemas**: Create tools using the `tool()` function with Zod schema validation for type-safe input handling.

    * **Class-based tools extending FunctionTool**: Create tools within classes to maintain shared state and resources.


## Tool Creation Examples

### Basic Example


=== "Python"


    Here's a simple example of a function decorated as a tool:

    ```python
    from strands import tool

    @tool
    def weather_forecast(city: str, days: int = 3) -> str:
        """Get weather forecast for a city.

        Args:
            city: The name of the city
            days: Number of days for the forecast
        """
        return f"Weather forecast for {city} for the next {days} days..."
    ```

    The decorator extracts information from your function's docstring to create the tool specification. The first paragraph becomes the tool's description, and the "Args" section provides parameter descriptions. These are combined with the function's type hints to create a complete tool specification.



=== "TypeScript"


    Here's a simple example of a function based tool with Zod:

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:basic_tool"
    ```

    TypeScript uses Zod schemas for input validation and type generation. The schema's descriptions are used by the model to understand when and how to use the tool.



### Overriding Tool Name, Description, and Schema


=== "Python"


    You can override the tool name, description, and input schema by providing them as arguments to the decorator:


    ```python
    @tool(name="get_weather", description="Retrieves weather forecast for a specified location")
    def weather_forecast(city: str, days: int = 3) -> str:
        """Implementation function for weather forecasting.

        Args:
            city: The name of the city
            days: Number of days for the forecast
        """
        return f"Weather forecast for {city} for the next {days} days..."
    ```


{{ ts_not_supported_code() }}


### Overriding Input Schema

=== "Python"


    You can provide a custom JSON schema to override the automatically generated one:

    ```python
    @tool(
        inputSchema={
            "json": {
                "type": "object",
                "properties": {
                    "shape": {
                        "type": "string",
                        "enum": ["circle", "rectangle"],
                        "description": "The shape type"
                    },
                    "radius": {"type": "number", "description": "Radius for circle"},
                    "width": {"type": "number", "description": "Width for rectangle"},
                    "height": {"type": "number", "description": "Height for rectangle"}
                },
                "required": ["shape"]
            }
        }
    )
    def calculate_area(shape: str, radius: float = None, width: float = None, height: float = None) -> float:
        """Calculate area of a shape."""
        if shape == "circle":
            return 3.14159 * radius ** 2
        elif shape == "rectangle":
            return width * height
        return 0.0
    ```


{{ ts_not_supported_code() }}



## Using and Customizing Tools:

### Loading Function-Based Tools

To use function-based tools, simply pass them to the agent:

=== "Python"

    ```python
    agent = Agent(
        tools=[weather_forecast]
    )
    ```

=== "TypeScript"

    ```typescript
    const agent = new Agent({
        tools: [weatherTool]
    })
    ```

### Custom Return Type


=== "Python"

    By default, your function's return value is automatically formatted as a text response. However, if you need more control over the response format, you can return a dictionary with a specific structure:


    ```python
    @tool
    def fetch_data(source_id: str) -> dict:
        """Fetch data from a specified source.

        Args:
            source_id: Identifier for the data source
        """
        try:
            data = some_other_function(source_id)
            return {
                "status": "success",
                "content": [ {
                    "json": data,
                }]
            }
        except Exception as e:
            return {
                "status": "error",
                 "content": [
                    {"text": f"Error:{e}"}
                ]
            }
    ```

=== "TypeScript"

    In Typescript, your tool's return value is automatically converted into a `ToolResultBlock`. You can return **any** JSON serializable object:

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:tool_response_success"
    ```

For more details, see the [Tool Response Format](#tool-response-format) section below.


### Async Invocation

Function tools may also be defined async. Strands will invoke all async tools concurrently.

=== "Python"

    ```python
    import asyncio
    from strands import Agent, tool


    @tool
    async def call_api() -> str:
        """Call API asynchronously."""

        await asyncio.sleep(5)  # simulated api call
        return "API result"


    async def async_example():
        agent = Agent(tools=[call_api])
        await agent.invoke_async("Can you call my API?")


    asyncio.run(async_example())
    ```

=== "TypeScript"

    **Async callback:**

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:async_tool"
    ```

    **AsyncGenerator callback:**

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:async_generator_callback"
    ```

### ToolContext

Tools can access their execution context to interact with the invoking agent, current tool use data, and invocation state. The [`ToolContext`](../../../api-reference/python/types/tools.md#strands.types.tools.ToolContext) provides this access:

=== "Python"

    In Python, set `context=True` in the decorator and include a `tool_context` parameter:

    ```python
    from strands import tool, Agent, ToolContext

    @tool(context=True)
    def get_self_name(tool_context: ToolContext) -> str:
        return f"The agent name is {tool_context.agent.name}"

    @tool(context=True)
    def get_tool_use_id(tool_context: ToolContext) -> str:
        return f"Tool use is {tool_context.tool_use["toolUseId"]}"

    @tool(context=True)
    def get_invocation_state(tool_context: ToolContext) -> str:
        return f"Invocation state: {tool_context.invocation_state["custom_data"]}"

    agent = Agent(tools=[get_self_name, get_tool_use_id, get_invocation_state], name="Best agent")

    agent("What is your name?")
    agent("What is the tool use id?")
    agent("What is the invocation state?", custom_data="You're the best agent ;)")
    ```


=== "TypeScript"

    In TypeScript, the context is passed as an optional second parameter to the callback function:

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:tool_context"
    ```


### Custom ToolContext Parameter Name

=== "Python"


    To use a different parameter name for ToolContext, specify the desired name as the value of the `@tool.context` argument:

    ```python
    from strands import tool, Agent, ToolContext

    @tool(context="context")
    def get_self_name(context: ToolContext) -> str:
        return f"The agent name is {context.agent.name}"

    agent = Agent(tools=[get_self_name], name="Best agent")

    agent("What is your name?")
    ```

{{ ts_not_supported_code() }}


#### Accessing State in Tools

=== "Python"

    The `invocation_state` attribute in `ToolContext` provides access to data passed through the agent invocation. This is particularly useful for:

    1. **Request Context**: Access session IDs, user information, or request-specific data
    2. **Multi-Agent Shared State**: In [Graph](../multi-agent/graph.md) and [Swarm](../multi-agent/swarm.md) patterns, access state shared across all agents
    3. **Per-Invocation Overrides**: Override behavior or settings for specific requests
    
    ```python
    from strands import tool, Agent, ToolContext
    import requests
    
    @tool(context=True)
    def api_call(query: str, tool_context: ToolContext) -> dict:
        """Make an API call with user context.
        
        Args:
            query: The search query to send to the API
            tool_context: Context containing user information
        """
        user_id = tool_context.invocation_state.get("user_id")
        
        response = requests.get(
            "https://api.example.com/search",
            headers={"X-User-ID": user_id},
            params={"q": query}
        )
        
        return response.json()
    
    agent = Agent(tools=[api_call])
    result = agent("Get my profile data", user_id="user123")
    ```

    **Invocation State Compared To Other Approaches**

    It's important to understand how invocation state compares to other approaches that impact tool execution:

    - **Tool Parameters**: Use for data that the LLM should reason about and provide based on the user's request. Examples include search queries, file paths, calculation inputs, or any data the agent needs to determine from context.

    - **Invocation State**: Use for context and configuration that should not appear in prompts but affects tool behavior. Best suited for parameters that can change between agent invocations. Examples include user IDs for personalization, session IDs, or user flags.

    - **[Class-based tools](#class-based-tools)**: Use for configuration that doesn't change between requests and requires initialization. Examples include API keys, database connection strings, service endpoints, or shared resources that need setup.


=== "TypeScript"

    In TypeScript, tools access **agent state** through `context.agent.state`. The state provides key-value storage that persists across tool invocations but is not passed to the model:

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:tool_context_invocation_state"
    ```

    Agent state is useful for:

    1. **Request Context**: Access session IDs, user information, or request-specific data
    2. **Multi-Agent Shared State**: In multi-agent patterns, access state shared across all agents
    3. **Tool State Persistence**: Maintain state between tool invocations within the same agent session


### Tool Streaming

=== "Python"

    Async tools can yield intermediate results to provide real-time progress updates. Each yielded value becomes a [streaming event](../streaming/index.md), with the final value serving as the tool's return result:

    ```python
    from datetime import datetime
    import asyncio
    from strands import tool
    
    @tool
    async def process_dataset(records: int) -> str:
        """Process records with progress updates."""
        start = datetime.now()
        
        for i in range(records):
            await asyncio.sleep(0.1)
            if i % 10 == 0:
                elapsed = datetime.now() - start
                yield f"Processed {i}/{records} records in {elapsed.total_seconds():.1f}s"
        
        yield f"Completed {records} records in {(datetime.now() - start).total_seconds():.1f}s"
    ```

    Stream events contain a `tool_stream_event` dictionary with `tool_use` (invocation info) and `data` (yielded value) fields:
    ```python
    async def tool_stream_example():
        agent = Agent(tools=[process_dataset])
    
        async for event in agent.stream_async("Process 50 records"):
            if tool_stream := event.get("tool_stream_event"):
                if update := tool_stream.get("data"):
                    print(f"Progress: {update}")
    
    asyncio.run(tool_stream_example())
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:tool_streaming"
    ```
## Class-Based Tools

Class-based tools allow you to create tools that maintain state and leverage object-oriented programming patterns. This approach is useful when your tools need to share resources, maintain context between invocations, follow object-oriented design principles, customize tools before passing them to an agent, or create different tool configurations for different agents.

### Example with Multiple Tools in a Class

You can define multiple tools within the same class to create a cohesive set of related functionality:

=== "Python"

    ```python
    from strands import Agent, tool
    
    class DatabaseTools:
        def __init__(self, connection_string):
            self.connection = self._establish_connection(connection_string)
            
        def _establish_connection(self, connection_string):
            # Set up database connection
            return {"connected": True, "db": "example_db"}
        
        @tool
        def query_database(self, sql: str) -> dict:
            """Run a SQL query against the database.
            
            Args:
                sql: The SQL query to execute
            """
            # Uses the shared connection
            return {"results": f"Query results for: {sql}", "connection": self.connection}
        
        @tool
        def insert_record(self, table: str, data: dict) -> str:
            """Insert a new record into the database.
            
            Args:
                table: The table name
                data: The data to insert as a dictionary
            """
            # Also uses the shared connection
            return f"Inserted data into {table}: {data}"
    
    # Usage
    db_tools = DatabaseTools("example_connection_string")
    agent = Agent(
        tools=[db_tools.query_database, db_tools.insert_record]
    )
    ```

    When you use the [`@tool`](../../../api-reference/python/tools/decorator.md#strands.tools.decorator.tool) decorator on a class method, the method becomes bound to the class instance when instantiated. This means the tool function has access to the instance's attributes and can maintain state between invocations.



=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/tools/tools.ts:class_multiple_tools"
    ```

    In TypeScript, you can create tools within a class and store them as properties. The tools can access the class's private state through closures.






## Tool Response Format

Tools can return responses in various formats using the [`ToolResult`](../../../api-reference/python/types/tools.md#strands.types.tools.ToolResult) structure. This structure provides flexibility for returning different types of content while maintaining a consistent interface.

#### ToolResult Structure

=== "Python"

    The [`ToolResult`](../../../api-reference/python/types/tools.md#strands.types.tools.ToolResult) dictionary has the following structure:

    ```python
    {
        "toolUseId": str,       # The ID of the tool use request (should match the incoming request).  Optional
        "status": str,          # Either "success" or "error"
        "content": List[dict]   # A list of content items with different possible formats
    }
    ```

=== "TypeScript"

    The ToolResult schema:

    ```typescript
    {
      type: 'toolResultBlock'  
      toolUseId: string
      status: 'success' | 'error'
      content: Array<ToolResultContent>
      error?: Error
    }
    ```

#### Content Types

The `content` field is a list of content blocks, where each block can contain:

- `text`: A string containing text output
- `json`: Any JSON-serializable data structure

#### Response Examples

=== "Python"

    **Success Response:**

    ```python
    {
        "toolUseId": "tool-123",
        "status": "success",
        "content": [
            {"text": "Operation completed successfully"},
            {"json": {"results": [1, 2, 3], "total": 3}}
        ]
    }
    ```

    **Error Response:**

    ```python
    {
        "toolUseId": "tool-123",
        "status": "error",
        "content": [
            {"text": "Error: Unable to process request due to invalid parameters"}
        ]
    }
    ```

=== "TypeScript"

    **Success Response:**

    The output structure of a successful tool response:

    ```typescript
    {
        "type": "toolResultBlock",
        "toolUseId": "tooluse_xq6vYsQ-QcGZOPcIx0yM3A",
        "status": "success",
        "content": [
            {
                "type": "jsonBlock",
                "json": {
                    "result": "The letter 'r' appears 3 time(s) in 'strawberry'"
                }
            }
        ]
    }
    ```

    **Error Response:**

    The output structure of a unsuccessful tool response:

    ```typescript
    {
        "type": "toolResultBlock",
        "toolUseId": "tooluse_rFoPosVKQ7WfYRfw_min8Q",
        "status": "error",
        "content": [
            {
                "type": "textBlock",
                "text": "Error: Test error"
            }
        ],
        "error": Error // https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Error
    }
    ```


#### Tool Result Handling

=== "Python"

    When using the [`@tool`](../../../api-reference/python/tools/decorator.md#strands.tools.decorator.tool) decorator, your function's return value is automatically converted to a proper [`ToolResult`](../../../api-reference/python/types/tools.md#strands.types.tools.ToolResult):

    1. If you return a string or other simple value, it's wrapped as `{"text": str(result)}`
    2. If you return a dictionary with the proper [`ToolResult`](../../../api-reference/python/types/tools.md#strands.types.tools.ToolResult) structure, it's used directly
    3. If an exception occurs, it's converted to an error response

=== "TypeScript"

    The `tool()` function automatically handles return value conversion:

    1. Any of the following types are converted to a ToolResult schema: `string | number | boolean | null | { [key: string]: JSONValue } | JSONValue[]`
    2. Exceptions are caught and converted to error responses

## Module Based Tools (python only)

=== "Python"

    An alternative approach is to define a tool as a Python module with a specific structure. This enables creating tools that don't depend on the SDK directly.

    A Python module tool requires two key components:

    1. A `TOOL_SPEC` variable that defines the tool's name, description, and input schema
    2. A function with the same name as specified in the tool spec that implements the tool's functionality


### Basic Example

=== "Python"

    Here's how you would implement the same weather forecast tool as a module:

    ```python
    # weather_forecast.py
    from typing import Any


    # 1. Tool Specification
    TOOL_SPEC = {
        "name": "weather_forecast",
        "description": "Get weather forecast for a city.",
        "inputSchema": {
            "json": {
                "type": "object",
                "properties": {
                    "city": {
                        "type": "string",
                        "description": "The name of the city"
                    },
                    "days": {
                        "type": "integer",
                        "description": "Number of days for the forecast",
                        "default": 3
                    }
                },
                "required": ["city"]
            }
        }
    }

    # 2. Tool Function
    def weather_forecast(tool, **kwargs: Any):
        # Extract tool parameters
        tool_use_id = tool["toolUseId"]
        tool_input = tool["input"]

        # Get parameter values
        city = tool_input.get("city", "")
        days = tool_input.get("days", 3)

        # Tool implementation
        result = f"Weather forecast for {city} for the next {days} days..."

        # Return structured response
        return {
            "toolUseId": tool_use_id,
            "status": "success",
            "content": [{"text": result}]
        }
    ```



### Loading Module Tools

=== "Python"

    To use a module-based tool, import the module and pass it to the agent:

    ```python
    from strands import Agent
    import weather_forecast

    agent = Agent(
        tools=[weather_forecast]
    )
    ```

    Alternatively, you can load a tool by passing in a path:

    ```python
    from strands import Agent

    agent = Agent(
        tools=["./weather_forecast.py"]
    )
    ```


### Async Invocation

=== "Python"

    Similar to decorated tools, users may define their module tools async.

    ```python
    TOOL_SPEC = {
        "name": "call_api",
        "description": "Call my API asynchronously.",
        "inputSchema": {
            "json": {
                "type": "object",
                "properties": {},
                "required": []
            }
        }
    }

    async def call_api(tool, **kwargs):
        await asyncio.sleep(5)  # simulated api call
        result = "API result"

        return {
            "toolUseId": tool["toolUseId"],
            "status": "success",
            "content": [{"text": result}],
        }
    ```
