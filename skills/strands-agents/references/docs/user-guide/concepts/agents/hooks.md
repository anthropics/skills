# Hooks

Hooks are a composable extensibility mechanism for extending agent functionality by subscribing to events throughout the agent lifecycle. The hook system enables both built-in components and user code to react to or modify agent behavior through strongly-typed event callbacks.

## Overview

The hooks system is a composable, type-safe system that supports multiple subscribers per event type. 

A **Hook Event** is a specific event in the lifecycle that callbacks can be associated with. A **Hook Callback** is a callback function that is invoked when the hook event is emitted.

Hooks enable use cases such as:

- Monitoring agent execution and tool usage
- Modifying tool execution behavior
- Adding validation and error handling
- Monitoring multi-agent execution flow and node transitions
- Debugging complex orchestration patterns
- Implementing custom logging and metrics collection

## Basic Usage

Hook callbacks are registered against specific event types and receive strongly-typed event objects when those events occur during agent execution. Each event carries relevant data for that stage of the agent lifecycle - for example, `BeforeInvocationEvent` includes agent and request details, while `BeforeToolCallEvent` provides tool information and parameters.

### Registering Individual Hook Callbacks

You can register callbacks for specific events using `agent.hooks` after the fact:

=== "Python"

    ```python
    agent = Agent()

    # Register individual callbacks
    def my_callback(event: BeforeInvocationEvent) -> None:
        print("Custom callback triggered")

    agent.hooks.add_callback(BeforeInvocationEvent, my_callback)
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/hooks.ts:individual_callback"
    ```

For multi-agent orchestrators, you can register callbacks for orchestration events:

=== "Python"

    ```python
    # Create your orchestrator (Graph or Swarm)
    orchestrator = Graph(...)
    
    # Register individual callbacks
    def my_callback(event: BeforeNodeCallEvent) -> None:
        print(f"Custom callback triggered")
    
    orchestrator.hooks.add_callback(BeforeNodeCallEvent, my_callback)
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

### Creating a Hook Provider

The `HookProvider` protocol allows a single object to register callbacks for multiple events. This pattern works for both single-agent and multi-agent orchestrators:

=== "Python"

    ```python
    class LoggingHook(HookProvider):
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeInvocationEvent, self.log_start)
            registry.add_callback(AfterInvocationEvent, self.log_end)

        def log_start(self, event: BeforeInvocationEvent) -> None:
            print(f"Request started for agent: {event.agent.name}")

        def log_end(self, event: AfterInvocationEvent) -> None:
            print(f"Request completed for agent: {event.agent.name}")

    # Passed in via the hooks parameter
    agent = Agent(hooks=[LoggingHook()])

    # Or added after the fact
    agent.hooks.add_hook(LoggingHook())
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/hooks.ts:hook_provider_class"
    ```

## Hook Event Lifecycle

### Single-Agent Lifecycle

The following diagram shows when hook events are emitted during a typical agent invocation where tools are invoked:

```mermaid
flowchart LR
 subgraph Start["Request Start Events"]
    direction TB
        BeforeInvocationEvent["BeforeInvocationEvent"]
        StartMessage["MessageAddedEvent"]
        BeforeInvocationEvent --> StartMessage
  end
 subgraph Model["Model Events"]
    direction TB
        AfterModelCallEvent["AfterModelCallEvent"]
        BeforeModelCallEvent["BeforeModelCallEvent"]
        ModelMessage["MessageAddedEvent"]
        BeforeModelCallEvent --> AfterModelCallEvent
        AfterModelCallEvent --> ModelMessage
  end
  subgraph Tool["Tool Events"]
    direction TB
        AfterToolCallEvent["AfterToolCallEvent"]
        BeforeToolCallEvent["BeforeToolCallEvent"]
        ToolMessage["MessageAddedEvent"]
        BeforeToolCallEvent --> AfterToolCallEvent
        AfterToolCallEvent --> ToolMessage
  end
  subgraph End["Request End Events"]
    direction TB
        AfterInvocationEvent["AfterInvocationEvent"]
  end
Start --> Model
Model <--> Tool
Tool --> End
```

### Multi-Agent Lifecycle

The following diagram shows when multi-agent hook events are emitted during orchestrator execution:

```mermaid
flowchart LR
subgraph Init["Initialization"]
    direction TB
    MultiAgentInitializedEvent["MultiAgentInitializedEvent"]
end
subgraph Invocation["Invocation Lifecycle"]
    direction TB
    BeforeMultiAgentInvocationEvent["BeforeMultiAgentInvocationEvent"]
    AfterMultiAgentInvocationEvent["AfterMultiAgentInvocationEvent"]
    BeforeMultiAgentInvocationEvent --> NodeExecution
    NodeExecution --> AfterMultiAgentInvocationEvent
end
subgraph NodeExecution["Node Execution (Repeated)"]
    direction TB
    BeforeNodeCallEvent["BeforeNodeCallEvent"]
    AfterNodeCallEvent["AfterNodeCallEvent"]
    BeforeNodeCallEvent --> AfterNodeCallEvent
end
Init --> Invocation
```

### Available Events

The hooks system provides events for different stages of execution. Events marked **(Python only)** are specific to multi-agent orchestrators and are not available in TypeScript.

| Event                                                       | Description                                                                                                   |
|-------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------|
| `AgentInitializedEvent`                                     | Triggered when an agent has been constructed and finished initialization at the end of the agent constructor. |
| `BeforeInvocationEvent`                                     | Triggered at the beginning of a new agent invocation request                                                  |
| `AfterInvocationEvent`                                      | Triggered at the end of an agent request, regardless of success or failure. Uses reverse callback ordering    |
| `MessageAddedEvent`                                         | Triggered when a message is added to the agent's conversation history                                         |
| `BeforeModelCallEvent`                                      | Triggered before the model is invoked for inference                                                           |
| `AfterModelCallEvent`                                       | Triggered after model invocation completes. Uses reverse callback ordering                                    |
| `BeforeToolCallEvent`                                       | Triggered before a tool is invoked.                                                                           |
| `AfterToolCallEvent`                                        | Triggered after tool invocation completes. Uses reverse callback ordering                                     |
| `BeforeToolsEvent` <br /> **(TypeScript only)**             | Triggered before tools are executed in a batch.                                                               |
| `AfterToolsEvent` <br /> **(TypeScript only)**              | Triggered after tools are executed in a batch. Uses reverse callback ordering                                 |
| `MultiAgentInitializedEvent` <br /> **(Python only)**       | Triggered when multi-agent orchestrator is initialized                                                        |
| `BeforeMultiAgentInvocationEvent`  <br /> **(Python only)** | Triggered before orchestrator execution starts                                                                |
| `AfterMultiAgentInvocationEvent`  <br /> **(Python only)**  | Triggered after orchestrator execution completes. Uses reverse callback ordering                              |
| `BeforeNodeCallEvent`  <br /> **(Python only)**             | Triggered before individual node execution starts                                                             |
| `AfterNodeCallEvent`  <br /> **(Python only)**              | Triggered after individual node execution completes. Uses reverse callback ordering                           |

## Hook Behaviors

### Event Properties

Most event properties are read-only to prevent unintended modifications. However, certain properties can be modified to influence agent behavior:

=== "Python"

    - [`AfterModelCallEvent`](../../../api-reference/python/hooks/events.md#strands.hooks.events.AfterModelCallEvent)
        - `retry` - Request a retry of the model invocation. See [Model Call Retry](#model-call-retry).

    - [`BeforeToolCallEvent`](../../../api-reference/python/hooks/events.md#strands.hooks.events.BeforeToolCallEvent)
        - `cancel_tool` - Cancel tool execution with a message. See [Limit Tool Counts](#limit-tool-counts).
        - `selected_tool` - Replace the tool to be executed. See [Tool Interception](#tool-interception).
        - `tool_use` - Modify tool parameters before execution. See [Fixed Tool Arguments](#fixed-tool-arguments).

    - [`AfterToolCallEvent`](../../../api-reference/python/hooks/events.md#strands.hooks.events.AfterToolCallEvent)
        - `result` - Modify the tool result. See [Result Modification](#result-modification).
        - `retry` - Request a retry of the tool invocation. See [Tool Call Retry](#tool-call-retry).

=== "TypeScript"

    - `AfterModelCallEvent`
        - `retryModelCall` - Request a retry of the model invocation (typically after reducing context size).

### Callback Ordering

Some events come in pairs, such as Before/After events. The After event callbacks are always called in reverse order from the Before event callbacks to ensure proper cleanup semantics.

## Advanced Usage

### Accessing Invocation State in Hooks

Invocation state provides configuration and context data passed through the agent or orchestrator invocation. This is particularly useful for:

1. **Custom Objects**: Access database client objects, connection pools, or other Python objects
2. **Request Context**: Access session IDs, user information, settings, or request-specific data  
3. **Multi-Agent Shared State**: In multi-agent patterns, access state shared across all agents - see [Shared State Across Multi-Agent Patterns](../multi-agent/multi-agent-patterns.md#shared-state-across-multi-agent-patterns)
4. **Custom Parameters**: Pass any additional data that hooks might need

=== "Python"

    ```python
    from strands.hooks import BeforeToolCallEvent
    import logging

    def log_with_context(event: BeforeToolCallEvent) -> None:
        """Log tool invocations with context from invocation state."""
        # Access invocation state from the event
        user_id = event.invocation_state.get("user_id", "unknown")
        session_id = event.invocation_state.get("session_id")
        
        # Access non-JSON serializable objects like database connections
        db_connection = event.invocation_state.get("database_connection")
        logger_instance = event.invocation_state.get("custom_logger")
        
        # Use custom logger if provided, otherwise use default
        logger = logger_instance if logger_instance else logging.getLogger(__name__)
        
        logger.info(
            f"User {user_id} in session {session_id} "
            f"invoking tool: {event.tool_use['name']} "
            f"with DB connection: {db_connection is not None}"
        )

    # Register the hook
    agent = Agent(tools=[my_tool])
    agent.hooks.add_callback(BeforeToolCallEvent, log_with_context)

    # Execute with context including non-serializable objects
    import sqlite3
    custom_logger = logging.getLogger("custom")
    db_conn = sqlite3.connect(":memory:")

    result = agent(
        "Process the data",
        user_id="user123",
        session_id="sess456",
        database_connection=db_conn,  # Non-JSON serializable object
        custom_logger=custom_logger   # Non-JSON serializable object
    )
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

Multi-agent hook events provide access to:

- **source**: The multi-agent orchestrator instance (for example: Graph/Swarm)
- **node_id**: Identifier of the node being executed (for node-level events)
- **invocation_state**: Configuration and context data passed through the orchestrator invocation

Multi-agent hooks provide configuration and context data passed through the orchestrator's lifecycle.

### Tool Interception

Modify or replace tools before execution:

=== "Python"

    ```python
    class ToolInterceptor(HookProvider):
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeToolCallEvent, self.intercept_tool)

        def intercept_tool(self, event: BeforeToolCallEvent) -> None:
            if event.tool_use.name == "sensitive_tool":
                # Replace with a safer alternative
                event.selected_tool = self.safe_alternative_tool
                event.tool_use["name"] = "safe_tool"
    ```

{{ ts_not_supported_code("Changing of tools is not yet available in TypeScript SDK") }}

### Result Modification

Modify tool results after execution:

=== "Python"

    ```python
    class ResultProcessor(HookProvider):
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(AfterToolCallEvent, self.process_result)

        def process_result(self, event: AfterToolCallEvent) -> None:
            if event.tool_use.name == "calculator":
                # Add formatting to calculator results
                original_content = event.result["content"][0]["text"]
                event.result["content"][0]["text"] = f"Result: {original_content}"
    ```

{{ ts_not_supported_code("Changing of tool results is not yet available in TypeScript SDK") }}

### Conditional Node Execution

Implement custom logic to modify orchestration behavior in multi-agent systems:

=== "Python"

    ```python
    class ConditionalExecutionHook(HookProvider):
        def __init__(self, skip_conditions: dict[str, callable]):
            self.skip_conditions = skip_conditions
    
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeNodeCallEvent, self.check_execution_conditions)
    
        def check_execution_conditions(self, event: BeforeNodeCallEvent) -> None:
            node_id = event.node_id
            if node_id in self.skip_conditions:
                condition_func = self.skip_conditions[node_id]
                if condition_func(event.invocation_state):
                    print(f"Skipping node {node_id} due to condition")
                    # Note: Actual node skipping would require orchestrator-specific implementation
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

## Best Practices

### Composability

Design hooks to be composable and reusable:

=== "Python"

    ```python
    class RequestLoggingHook(HookProvider):
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeInvocationEvent, self.log_request)
            registry.add_callback(AfterInvocationEvent, self.log_response)
            registry.add_callback(BeforeToolCallEvent, self.log_tool_use)

        ...
    ```

{{ ts_not_supported_code("Changing of tools is not yet available in TypeScript SDK") }}

### Event Property Modifications

When modifying event properties, log the changes for debugging and audit purposes:

=== "Python"

    ```python
    class ResultProcessor(HookProvider):
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(AfterToolCallEvent, self.process_result)

        def process_result(self, event: AfterToolCallEvent) -> None:
            if event.tool_use.name == "calculator":
                original_content = event.result["content"][0]["text"]
                logger.info(f"Modifying calculator result: {original_content}")
                event.result["content"][0]["text"] = f"Result: {original_content}"
    ```

{{ ts_not_supported_code("Changing of tools is not yet available in TypeScript SDK") }}

### Orchestrator-Agnostic Design

Design multi-agent hooks to work with different orchestrator types:

=== "Python"

    ```python
    class UniversalMultiAgentHook(HookProvider):
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeNodeCallEvent, self.handle_node_execution)
    
        def handle_node_execution(self, event: BeforeNodeCallEvent) -> None:
            orchestrator_type = type(event.source).__name__
            print(f"Executing node {event.node_id} in {orchestrator_type} orchestrator")
            
            # Handle orchestrator-specific logic if needed
            if orchestrator_type == "Graph":
                self.handle_graph_node(event)
            elif orchestrator_type == "Swarm":
                self.handle_swarm_node(event)
    
        def handle_graph_node(self, event: BeforeNodeCallEvent) -> None:
            # Graph-specific handling
            pass
    
        def handle_swarm_node(self, event: BeforeNodeCallEvent) -> None:
            # Swarm-specific handling
            pass
    ```
{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

## Integration with Multi-Agent Systems

Multi-agent hooks complement single-agent hooks. Individual agents within the orchestrator can still have their own hooks, creating a layered monitoring and customization system:

=== "Python"

    ```python
    # Single-agent hook for individual agents
    class AgentLevelHook(HookProvider):
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeToolCallEvent, self.log_tool_use)
    
        def log_tool_use(self, event: BeforeToolCallEvent) -> None:
            print(f"Agent tool call: {event.tool_use['name']}")
    
    # Multi-agent hook for orchestrator
    class OrchestratorLevelHook(HookProvider):
        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeNodeCallEvent, self.log_node_execution)
    
        def log_node_execution(self, event: BeforeNodeCallEvent) -> None:
            print(f"Orchestrator node execution: {event.node_id}")
    
    # Create agents with individual hooks
    agent1 = Agent(tools=[tool1], hooks=[AgentLevelHook()])
    agent2 = Agent(tools=[tool2], hooks=[AgentLevelHook()])
    
    # Create orchestrator with multi-agent hooks
    orchestrator = Graph(
        agents={"agent1": agent1, "agent2": agent2},
        hooks=[OrchestratorLevelHook()]
    )
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

This layered approach provides comprehensive observability and control across both individual agent execution and orchestrator-level coordination.

## Cookbook

This section contains practical hook implementations for common use cases.

### Fixed Tool Arguments

Useful for enforcing security policies, maintaining consistency, or overriding agent decisions with system-level requirements. This hook ensures specific tools always use predetermined parameter values regardless of what the agent specifies.

=== "Python"

    ```python
    from typing import Any
    from strands.hooks import HookProvider, HookRegistry, BeforeToolCallEvent

    class ConstantToolArguments(HookProvider):
        """Use constant argument values for specific parameters of a tool."""

        def __init__(self, fixed_tool_arguments: dict[str, dict[str, Any]]):
            """
            Initialize fixed parameter values for tools.
        
            Args:
                fixed_tool_arguments: A dictionary mapping tool names to dictionaries of 
                    parameter names and their fixed values. These values will override any 
                    values provided by the agent when the tool is invoked.
            """
            self._tools_to_fix = fixed_tool_arguments

        def register_hooks(self, registry: HookRegistry, **kwargs: Any) -> None:
            registry.add_callback(BeforeToolCallEvent, self._fix_tool_arguments)

        def _fix_tool_arguments(self, event: BeforeToolCallEvent):
            # If the tool is in our list of parameters, then use those parameters
            if parameters_to_fix := self._tools_to_fix.get(event.tool_use["name"]):
                tool_input: dict[str, Any] = event.tool_use["input"]
                tool_input.update(parameters_to_fix)
    ```

{{ ts_not_supported_code("Changing of tools is not yet available in TypeScript SDK") }}

For example, to always force the `calculator` tool to use precision of 1 digit:

=== "Python"

    ```python
    fix_parameters = ConstantToolArguments({
        "calculator": {
            "precision": 1,
        }
    })

    agent = Agent(tools=[calculator], hooks=[fix_parameters])
    result = agent("What is 2 / 3?")
    ```

{{ ts_not_supported_code("Changing of tools is not yet available in TypeScript SDK") }}

### Limit Tool Counts

Useful for preventing runaway tool usage, implementing rate limiting, or enforcing usage quotas. This hook tracks tool invocations per request and replaces tools with error messages when limits are exceeded.

=== "Python"

    ```python
    from strands import tool
    from strands.hooks import HookRegistry, HookProvider, BeforeToolCallEvent, BeforeInvocationEvent
    from threading import Lock

    class LimitToolCounts(HookProvider):
        """Limits the number of times tools can be called per agent invocation"""
        
        def __init__(self, max_tool_counts: dict[str, int]):
            """
            Initializer.

            Args:
                max_tool_counts: A dictionary mapping tool names to max call counts for 
                    tools. If a tool is not specified in it, the tool can be called as many
                    times as desired
            """
            self.max_tool_counts = max_tool_counts
            self.tool_counts = {}
            self._lock = Lock()

        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeInvocationEvent, self.reset_counts)
            registry.add_callback(BeforeToolCallEvent, self.intercept_tool)

        def reset_counts(self, event: BeforeInvocationEvent) -> None:
            with self._lock:
                self.tool_counts = {}

        def intercept_tool(self, event: BeforeToolCallEvent) -> None:
            tool_name = event.tool_use["name"]
            with self._lock:
                max_tool_count = self.max_tool_counts.get(tool_name)
                tool_count = self.tool_counts.get(tool_name, 0) + 1
                self.tool_counts[tool_name] = tool_count

            if max_tool_count and tool_count > max_tool_count:
                event.cancel_tool = (
                    f"Tool '{tool_name}' has been invoked too many and is now being throttled. "
                    f"DO NOT CALL THIS TOOL ANYMORE "
                )
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

For example, to limit the `sleep` tool to 3 invocations per invocation:

=== "Python"

    ```python
    limit_hook = LimitToolCounts(max_tool_counts={"sleep": 3})

    agent = Agent(tools=[sleep], hooks=[limit_hook])

    # This call will only have 3 successful sleeps
    agent("Sleep 5 times for 10ms each or until you can't anymore")
    # This will sleep successfully again because the count resets every invocation
    agent("Sleep once")
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

### Model Call Retry

Useful for implementing custom retry logic for model invocations. The `AfterModelCallEvent.retry` field allows hooks to request retries based on any criteria—exceptions, response validation, content quality checks, or any custom logic. This example demonstrates retrying on exceptions with exponential backoff:

=== "Python"

    ```python
    import asyncio
    import logging
    from strands.hooks import HookProvider, HookRegistry, BeforeInvocationEvent, AfterModelCallEvent

    logger = logging.getLogger(__name__)

    class RetryOnServiceUnavailable(HookProvider):
        """Retry model calls when ServiceUnavailable errors occur."""

        def __init__(self, max_retries: int = 3):
            self.max_retries = max_retries
            self.retry_count = 0

        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(BeforeInvocationEvent, self.reset_counts)
            registry.add_callback(AfterModelCallEvent, self.handle_retry)

        def reset_counts(self, event: BeforeInvocationEvent = None) -> None:
            self.retry_count = 0

        async def handle_retry(self, event: AfterModelCallEvent) -> None:
            if event.exception:
                if "ServiceUnavailable" in str(event.exception):
                    logger.info("ServiceUnavailable encountered")
                    if self.retry_count < self.max_retries:
                        logger.info("Retrying model call")
                        self.retry_count += 1
                        event.retry = True
                        await asyncio.sleep(2 ** self.retry_count)  # Exponential backoff
            else:
                # Reset counts on successful call
                self.reset_counts()
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

For example, to retry up to 3 times on service unavailable errors:

=== "Python"

    ```python
    from strands import Agent

    retry_hook = RetryOnServiceUnavailable(max_retries=3)
    agent = Agent(hooks=[retry_hook])

    result = agent("What is the capital of France?")
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

### Tool Call Retry

Useful for implementing custom retry logic for tool invocations. The `AfterToolCallEvent.retry` field allows hooks to request that a tool be re-executed—for example, to handle transient errors, timeouts, or flaky external services. When `retry` is set to `True`, the tool executor discards the current result and invokes the tool again with the same `tool_use_id`.

!!! note "Streaming behavior"
    When a tool call is retried, intermediate streaming events (`ToolStreamEvent`) from discarded attempts will have already been emitted to callers. Only the final attempt's `ToolResultEvent` is emitted and added to conversation history. Callers consuming streamed events should be prepared to handle events from discarded attempts.

=== "Python"

    ```python
    import logging
    from strands.hooks import HookProvider, HookRegistry, AfterToolCallEvent

    logger = logging.getLogger(__name__)

    class RetryOnToolError(HookProvider):
        """Retry tool calls that fail with errors."""

        def __init__(self, max_retries: int = 1):
            self.max_retries = max_retries
            self._attempt_counts: dict[str, int] = {}

        def register_hooks(self, registry: HookRegistry) -> None:
            registry.add_callback(AfterToolCallEvent, self.handle_retry)

        def handle_retry(self, event: AfterToolCallEvent) -> None:
            tool_use_id = str(event.tool_use.get("toolUseId", ""))
            tool_name = event.tool_use.get("name", "unknown")

            # Track attempts per tool_use_id
            attempt = self._attempt_counts.get(tool_use_id, 0) + 1
            self._attempt_counts[tool_use_id] = attempt

            if event.result.get("status") == "error" and attempt <= self.max_retries:
                logger.info(f"Retrying tool '{tool_name}' (attempt {attempt}/{self.max_retries})")
                event.retry = True
            elif event.result.get("status") != "error":
                # Clean up tracking on success
                self._attempt_counts.pop(tool_use_id, None)
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}

For example, to retry failed tool calls once:

=== "Python"

    ```python
    from strands import Agent, tool

    @tool
    def flaky_api_call(query: str) -> str:
        """Call an external API that sometimes fails.

        Args:
            query: The query to send.
        """
        import random
        if random.random() < 0.5:
            raise RuntimeError("Service temporarily unavailable")
        return f"Result for: {query}"

    retry_hook = RetryOnToolError(max_retries=1)
    agent = Agent(tools=[flaky_api_call], hooks=[retry_hook])

    result = agent("Look up the weather")
    ```

{{ ts_not_supported_code("This feature is not yet available in TypeScript SDK") }}
