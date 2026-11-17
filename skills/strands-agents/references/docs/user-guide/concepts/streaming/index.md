# Streaming Events

Strands Agents SDK provides real-time streaming capabilities that allow you to monitor and process events as they occur during agent execution. This enables responsive user interfaces, real-time monitoring, and custom output formatting.

Strands has multiple approaches for handling streaming events:

- **[Async Iterators](async-iterators.md)**: Ideal for asynchronous server frameworks
- **[Callback Handlers (Python only)](callback-handlers.md)**: Perfect for synchronous applications and custom event processing

Both methods receive the same event types but differ in their execution model and use cases.

## Event Types

All streaming methods yield the same set of events:

### Lifecycle Events

=== "Python"

    - **`init_event_loop`**: True at the start of agent invocation initializing
    - **`start_event_loop`**: True when the event loop is starting
    - **`message`**: Present when a new message is created
    - **`event`**: Raw event from the model stream
    - **`force_stop`**: True if the event loop was forced to stop
        - **`force_stop_reason`**: Reason for forced stop
    - **`result`**: The final [`AgentResult`](../../../api-reference/python/agent/agent_result.md#strands.agent.agent_result.AgentResult)

=== "TypeScript"

    Each event emitted from the typescript agent is a class with a `type` attribute that has a unique value. When determining an event, you can use `instanceof` on the class, or an equality check on the `event.type` value.

    - **`BeforeInvocationEvent`**: Start of agent loop (before any iterations)
    - **`AfterInvocationEvent`**: End of agent loop (after all iterations complete)
        - **`error?`**: Optional error if loop terminated due to exception
    - **`BeforeModelEvent`**: Before model invocation
        - **`messages`**: Array of messages being sent to model
    - **`AfterModelEvent`**: After model invocation
        - **`message`**: Assistant message returned by model
        - **`stopReason`**: Why generation stopped
    - **`BeforeToolsEvent`**: Before tools execution
        - **`message`**: Assistant message containing tool use blocks
    - **`AfterToolsEvent`**: After tools execution
        - **`message`**: User message containing tool results
    

### Model Stream Events

=== "Python"

    - **`data`**: Text chunk from the model's output
    - **`delta`**: Raw delta content from the model
    - **`reasoning`**: True for reasoning events
        - **`reasoningText`**: Text from reasoning process
        - **`reasoning_signature`**: Signature from reasoning process
        - **`redactedContent`**: Reasoning content redacted by the model

=== "TypeScript"

    - **`ModelMessageStartEvent`**: Start of a message from the model
    - **`ModelContentBlockStartEvent`**: Start of a content block from a model for text, toolUse, reasoning, etc.
    - **`ModelContentBlockDeltaEvent`**: Content deltas for text, tool input, or reasoning
    - **`ModelContentBlockStopEvent`**: End of a content block
    - **`ModelMessageStopEvent`**: End of a message
    - **`ModelMetadataEvent`**: Usage and metrics metadata

### Tool Events

=== "Python"
    - **`current_tool_use`**: Information about the current tool being used, including:
        - **`toolUseId`**: Unique ID for this tool use
        - **`name`**: Name of the tool
        - **`input`**: Tool input parameters (accumulated as streaming occurs)
    - **`tool_stream_event`**: Information about [an event streamed from a tool](../tools/custom-tools.md#tool-streaming), including:
        - **`tool_use`**: The [`ToolUse`](../../../api-reference/python/types/tools.md#strands.types.tools.ToolUse) for the tool that streamed the event
        - **`data`**: The data streamed from the tool
=== "TypeScript"
    - **`BeforeToolsEvent`**: Information about the current tool being used, including:
        - **`message`**: The assistant message containing tool use blocks
    - **`ToolStreamEvent`**: Information about an event streamed from a tool, including:
        - **`data`**: The data streamed from the tool

### Multi-Agent Events

=== "Python"

    Multi-agent systems ([Graph](../multi-agent/graph.md) and [Swarm](../multi-agent/swarm.md)) emit additional coordination events:

    - **`multiagent_node_start`**: When a node begins execution
        - **`type`**: `"multiagent_node_start"`
        - **`node_id`**: Unique identifier for the node
        - **`node_type`**: Type of node (`"agent"`, `"swarm"`, `"graph"`)
    - **`multiagent_node_stream`**: Forwarded events from agents/multi-agents with node context
        - **`type`**: `"multiagent_node_stream"`
        - **`node_id`**: Identifier of the node generating the event
        - **`event`**: The original agent event (nested)
    - **`multiagent_node_stop`**: When a node completes execution
        - **`type`**: `"multiagent_node_stop"`
        - **`node_id`**: Unique identifier for the node
        - **`node_result`**: Complete NodeResult with execution details, metrics, and status
    - **`multiagent_handoff`**: When control is handed off between agents (Swarm) or batch transitions (Graph)
        - **`type`**: `"multiagent_handoff"`
        - **`from_node_ids`**: List of node IDs completing execution
        - **`to_node_ids`**: List of node IDs beginning execution
        - **`message`**: Optional handoff message (typically used in Swarm)
    - **`multiagent_result`**: Final multi-agent result
        - **`type`**: `"multiagent_result"`
        - **`result`**: The final GraphResult or SwarmResult

    See [Graph streaming](../multi-agent/graph.md#streaming-events) and [Swarm streaming](../multi-agent/swarm.md#streaming-events) for usage examples.

=== "TypeScript"

    ```typescript
    Coming soon to Typescript!
    ```

## Quick Examples
=== "Python"
    **Async Iterator Pattern**
    ```python
    async for event in agent.stream_async("Calculate 2+2"):
        if "data" in event:
            print(event["data"], end="")
    ```

    **Callback Handler Pattern**
    ```python
    def handle_events(**kwargs):
        if "data" in kwargs:
            print(kwargs["data"], end="")

    agent = Agent(callback_handler=handle_events)
    agent("Calculate 2+2")
    ```

=== "TypeScript"

    **Async Iterator Pattern**
    ```typescript
    --8<-- "user-guide/concepts/streaming/overview.ts:quick_example_async_iterator"
    ```

## Identifying Events Emitted from Agent

This example demonstrates how to identify event emitted from an agent:

=== "Python"

    ```python
    from strands import Agent
    from strands_tools import calculator

    def process_event(event):
        """Shared event processor for both async iterators and callback handlers"""
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

        # Show text snippets
        if "data" in event:
            data_snippet = event["data"][:20] + ("..." if len(event["data"]) > 20 else "")
            print(f"📟 Text: {data_snippet}")

    agent = Agent(tools=[calculator], callback_handler=None)
    async for event in agent.stream_async("What is the capital of France and what is 42+7?"):
        process_event(event)

    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/streaming/overview.ts:agent_loop_lifecycle"
    ```

## Sub-Agent Streaming Example

Utilizing both [agents as a tool](../multi-agent/agents-as-tools.md) and [tool streaming](../tools/custom-tools.md#tool-streaming), this example shows how to stream events from sub-agents:

=== "Python"

    ```python
    from typing import AsyncIterator
    from dataclasses import dataclass
    from strands import Agent, tool
    from strands_tools import calculator

    @dataclass
    class SubAgentResult:
        agent: Agent
        event: dict

    @tool
    async def math_agent(query: str) -> AsyncIterator:
        """Solve math problems using the calculator tool."""
        agent = Agent(
            name="Math Expert",
            system_prompt="You are a math expert. Use the calculator tool for calculations.",
            callback_handler=None,
            tools=[calculator]
        )
        
        result = None
        async for event in agent.stream_async(query):
            yield SubAgentResult(agent=agent, event=event)
            if "result" in event:
                result = event["result"]
        
        yield str(result)

    def process_sub_agent_events(event):
        """Shared processor for sub-agent streaming events"""
        tool_stream = event.get("tool_stream_event", {}).get("data")
        
        if isinstance(tool_stream, SubAgentResult):
            current_tool = tool_stream.event.get("current_tool_use", {})
            tool_name = current_tool.get("name")
            
            if tool_name:
                print(f"Agent '{tool_stream.agent.name}' using tool '{tool_name}'")
        
        # Also show regular text output
        if "data" in event:
            print(event["data"], end="")

    # Using with async iterators
    orchestrator_async_iterator = Agent(
        system_prompt="Route math questions to the math_agent tool.",
        callback_handler=None,
        tools=[math_agent]
    )


    # With async-iterator
    async for event in orchestrator_async_iterator.stream_async("What is 3+3?"):
        process_sub_agent_events(event)
    

    # With callback handler
    def handle_events(**kwargs):
        process_sub_agent_events(kwargs)

    orchestrator_callback = Agent(
        system_prompt="Route math questions to the math_agent tool.",
        callback_handler=handle_events,
        tools=[math_agent]
    )

    orchestrator_callback("What is 3+3?")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/streaming/overview.ts:sub_agent_basic"
    ```

## Next Steps

- Learn about [Async Iterators](async-iterators.md) for asynchronous streaming
- Explore [Callback Handlers](callback-handlers.md) for synchronous event processing
- See the [Agent API Reference](../../../api-reference/python/agent/agent.md) for complete method documentation