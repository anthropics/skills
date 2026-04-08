# Callback Handlers

{{ ts_not_supported("TypeScript does not support callback handlers. For real-time event handling in TypeScript, use the [async iterator pattern](./async-iterators.md) with `agent.stream()` or see [Hooks](../agents/hooks.md) for lifecycle event handling.") }}

Callback handlers allow you to intercept and process events as they happen during agent execution in Python. This enables real-time monitoring, custom output formatting, and integration with external systems through function-based event handling.

For a complete list of available events including text generation, tool usage, lifecycle, and reasoning events, see the [streaming overview](./index.md#event-types).

> **Note:** For asynchronous applications, consider [async iterators](./async-iterators.md) instead.

## Basic Usage

The simplest way to use a callback handler is to pass a callback function to your agent:

```python
from strands import Agent
from strands_tools import calculator

def custom_callback_handler(**kwargs):
    # Process stream data
    if "data" in kwargs:
        print(f"MODEL OUTPUT: {kwargs['data']}")
    elif "current_tool_use" in kwargs and kwargs["current_tool_use"].get("name"):
        print(f"\nUSING TOOL: {kwargs['current_tool_use']['name']}")

# Create an agent with custom callback handler
agent = Agent(
    tools=[calculator],
    callback_handler=custom_callback_handler
)

agent("Calculate 2+2")
```

## Default Callback Handler

Strands Agents provides a default callback handler that formats output to the console:

```python
from strands import Agent
from strands.handlers.callback_handler import PrintingCallbackHandler

# The default callback handler prints text and shows tool usage
agent = Agent(callback_handler=PrintingCallbackHandler())
```

If you want to disable all output, specify `None` for the callback handler:

```python
from strands import Agent

# No output will be displayed
agent = Agent(callback_handler=None)
```

## Custom Callback Handlers

Custom callback handlers enable you to have fine-grained control over what is streamed from your agents.

### Example - Print all events in the stream sequence

Custom callback handlers can be useful to debug sequences of events in the agent loop:

```python
from strands import Agent
from strands_tools import calculator

def debugger_callback_handler(**kwargs):
    # Print the values in kwargs so that we can see everything
    print(kwargs)

agent = Agent(
    tools=[calculator],
    callback_handler=debugger_callback_handler
)

agent("What is 922 + 5321")
```

This handler prints all calls to the callback handler including full event details.

### Example - Buffering Output Per Message

This handler demonstrates how to buffer text and only show it when a complete message is generated. This pattern is useful for chat interfaces where you want to show polished, complete responses:

```python
import json
from strands import Agent
from strands_tools import calculator

def message_buffer_handler(**kwargs):
    # When a new message is created from the assistant, print its content
    if "message" in kwargs and kwargs["message"].get("role") == "assistant":
        print(json.dumps(kwargs["message"], indent=2))

# Usage with an agent
agent = Agent(
    tools=[calculator],
    callback_handler=message_buffer_handler
)

agent("What is 2+2 and tell me about AWS Lambda")
```

This handler leverages the `message` event which is triggered when a complete message is created. By using this approach, we can buffer the incrementally streamed text and only display complete, coherent messages rather than partial fragments. This is particularly useful in conversational interfaces or when responses benefit from being processed as complete units.

### Example - Event Loop Lifecycle Tracking

This callback handler illustrates the event loop lifecycle events and how they relate to each other. It's useful for understanding the flow of execution in the Strands agent:

```python
from strands import Agent
from strands_tools import calculator

def event_loop_tracker(**kwargs):
    # Track event loop lifecycle
    if kwargs.get("init_event_loop", False):
        print("🔄 Event loop initialized")
    elif kwargs.get("start_event_loop", False):
        print("▶️ Event loop cycle starting")
    elif "message" in kwargs:
        print(f"📬 New message created: {kwargs['message']['role']}")
    elif "result" in kwargs:
        print("✅ Agent completed with result")
    elif kwargs.get("force_stop", False):
        print(f"🛑 Event loop force-stopped: {kwargs.get('force_stop_reason', 'unknown reason')}")
        
    # Track tool usage
    if "current_tool_use" in kwargs and kwargs["current_tool_use"].get("name"):
        tool_name = kwargs["current_tool_use"]["name"]
        print(f"🔧 Using tool: {tool_name}")
    
    # Show only a snippet of text to keep output clean
    if "data" in kwargs:
        # Only show first 20 chars of each chunk for demo purposes
        data_snippet = kwargs["data"][:20] + ("..." if len(kwargs["data"]) > 20 else "")
        print(f"📟 Text: {data_snippet}")

# Create agent with event loop tracker
agent = Agent(
    tools=[calculator],
    callback_handler=event_loop_tracker
)

# This will show the full event lifecycle in the console
agent("What is the capital of France and what is 42+7?")
```

The output will show the sequence of events:

1. First the event loop initializes (`init_event_loop`)
2. Then the cycle begins (`start_event_loop`)
3. New cycles may start multiple times during execution (`start`)
4. Text generation and tool usage events occur during the cycle
5. Finally, the agent completes with a `result` event or may be force-stopped

## Best Practices

When implementing callback handlers:

1. **Keep Them Fast**: Callback handlers run in the critical path of agent execution
2. **Handle All Event Types**: Be prepared for different event types
3. **Graceful Errors**: Handle exceptions within your handler
4. **State Management**: Store accumulated state in the `request_state`