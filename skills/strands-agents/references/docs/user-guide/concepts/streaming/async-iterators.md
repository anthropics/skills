# Async Iterators for Streaming

Async iterators provide asynchronous streaming of agent events, allowing you to process events as they occur in real-time. This approach is ideal for asynchronous frameworks where you need fine-grained control over async execution flow.

For a complete list of available events including text generation, tool usage, lifecycle, and reasoning events, see the [streaming overview](./index.md#event-types).

## Basic Usage

=== "Python"

    Python uses the [`stream_async`](../../../api-reference/python/agent/agent.md#strands.agent.agent.Agent.stream_async), which is a streaming counterpart to the [`invoke_async`](../../../api-reference/python/agent/agent.md#strands.agent.agent.Agent.invoke_async) method, for asynchronous streaming. This is ideal for frameworks like FastAPI, aiohttp, or Django Channels.

    > **Note**: Python also supports synchronous event handling via [callback handlers](./callback-handlers.md).

    ```python
    import asyncio
    from strands import Agent
    from strands_tools import calculator

    # Initialize our agent without a callback handler
    agent = Agent(
        tools=[calculator],
        callback_handler=None
    )

    # Async function that iterators over streamed agent events
    async def process_streaming_response():
        agent_stream = agent.stream_async("Calculate 2+2")
        async for event in agent_stream:
            print(event)

    # Run the agent
    asyncio.run(process_streaming_response())
    ```

=== "TypeScript"

    TypeScript uses the [`stream`](../../../api-reference/python/agent/agent.md) method for streaming, which is async by default. This is ideal for frameworks like Express.js or NestJS.

    ```typescript
    --8<-- "user-guide/concepts/streaming/async-iterators.ts:basic_usage"
    ```

## Server examples

Here's how to integrate streaming with web frameworks to create a streaming endpoint:

=== "Python - FastAPI"

    ```python
    from fastapi import FastAPI, HTTPException
    from fastapi.responses import StreamingResponse
    from pydantic import BaseModel
    from strands import Agent
    from strands_tools import calculator, http_request

    app = FastAPI()

    class PromptRequest(BaseModel):
        prompt: str

    @app.post("/stream")
    async def stream_response(request: PromptRequest):
        async def generate():
            agent = Agent(
                tools=[calculator, http_request],
                callback_handler=None
            )

            try:
                async for event in agent.stream_async(request.prompt):
                    if "data" in event:
                        # Only stream text chunks to the client
                        yield event["data"]
            except Exception as e:
                yield f"Error: {str(e)}"

        return StreamingResponse(
            generate(),
            media_type="text/plain"
        )
    ```

=== "TypeScript - Express.js"

    > **Note**: This is a conceptual example. Install Express.js with `npm install express @types/express` to use it in your project.

    ```typescript
    --8<-- "user-guide/concepts/streaming/async-iterators.ts:express_example"
    ```

    You can then curl your local server with:
    ```bash
    curl localhost:3000/stream -d '{"prompt": "Hello"}' -H "Content-Type: application/json"
    ```

### Agentic Loop

This async stream processor illustrates the event loop lifecycle events and how they relate to each other. It's useful for understanding the flow of execution in the Strands agent:

=== "Python"

    ```python
    from strands import Agent
    from strands_tools import calculator

    # Create agent with event loop tracker
    agent = Agent(
        tools=[calculator],
        callback_handler=None
    )

    # This will show the full event lifecycle in the console
    async for event in agent.stream_async("What is the capital of France and what is 42+7?"):
        # Track event loop lifecycle
        if event.get("init_event_loop", False):
            print("🔄 Event loop initialized")
        elif event.get("start_event_loop", False):
            print("▶️ Event loop cycle starting")
        elif "message" in event:
            print(f"📬 New message created: {event['message']['role']}")
        elif "result" in event:
            print("✅ Agent completed with result")
        elif event.get("force_stop", False):
            print(f"🛑 Event loop force-stopped: {event.get('force_stop_reason', 'unknown reason')}")

        # Track tool usage
        if "current_tool_use" in event and event["current_tool_use"].get("name"):
            tool_name = event["current_tool_use"]["name"]
            print(f"🔧 Using tool: {tool_name}")

        # Show only a snippet of text to keep output clean
        if "data" in event:
            # Only show first 20 chars of each chunk for demo purposes
            data_snippet = event["data"][:20] + ("..." if len(event["data"]) > 20 else "")
            print(f"📟 Text: {data_snippet}")
    ```

    The output will show the sequence of events:

    1. First the event loop initializes (`init_event_loop`)
    2. Then the cycle begins (`start_event_loop`)
    3. New cycles may start multiple times during execution (`start_event_loop`)
    4. Text generation and tool usage events occur during the cycle
    5. Finally, the agent completes with a `result` event or may be force-stopped (`force_stop`)

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/streaming/overview.ts:agent_loop_lifecycle"
    ```

    The output will show the sequence of events:

    1. First the invocation starts (`beforeInvocationEvent`)
    2. Then the model is called (`beforeModelEvent`)
    3. The model generates content with delta events (`modelContentBlockDeltaEvent`)
    4. Tools may be executed (`beforeToolsEvent`, `afterToolsEvent`)
    5. The model may be called again in subsequent cycles
    6. Finally, the invocation completes (`afterInvocationEvent`)
