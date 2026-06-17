# State Management

Strands Agents state is maintained in several forms:

1. **Conversation History:** The sequence of messages between the user and the agent.
2. **Agent State**: Stateful information outside of conversation context, maintained across multiple requests.
3. **Request State**: Contextual information maintained within a single request.

Understanding how state works in Strands is essential for building agents that can maintain context across multi-turn interactions and workflows.

## Conversation History

Conversation history is the primary form of context in a Strands agent, directly accessible through the agent:

=== "Python"

    ```python
    from strands import Agent

    # Create an agent
    agent = Agent()

    # Send a message and get a response
    agent("Hello!")

    # Access the conversation history
    print(agent.messages)  # Shows all messages exchanged so far
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/state.ts:conversation_history"
    ```

The agent messages contains all user and assistant messages, including tool calls and tool results. This is the primary way to inspect what's happening in your agent's conversation.

You can initialize an agent with existing messages to continue a conversation or pre-fill your Agent's context with information:

=== "Python"

    ```python
    from strands import Agent

    # Create an agent with initial messages
    agent = Agent(messages=[
        {"role": "user", "content": [{"text": "Hello, my name is Strands!"}]},
        {"role": "assistant", "content": [{"text": "Hi there! How can I help you today?"}]}
    ])

    # Continue the conversation
    agent("What's my name?")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/state.ts:message_initialization"
    ```

Conversation history is automatically:

- Maintained between calls to the agent
- Passed to the model during each inference
- Used for tool execution context
- Managed to prevent context window overflow

### Direct Tool Calling

Direct tool calls are (by default) recorded in the conversation history:

=== "Python"

    ```python
    from strands import Agent
    from strands_tools import calculator

    agent = Agent(tools=[calculator])

    # Direct tool call with recording (default behavior)
    agent.tool.calculator(expression="123 * 456")

    # Direct tool call without recording
    agent.tool.calculator(expression="765 / 987", record_direct_tool_call=False)

    print(agent.messages)
    ```
    In this example we can see that the first `agent.tool.calculator()` call is recorded in the agent's conversation history.

    The second `agent.tool.calculator()` call is **not** recorded in the history because we specified the `record_direct_tool_call=False` argument.

{{ ts_not_supported_code() }}

### Conversation Manager

Strands uses a conversation manager to handle conversation history effectively. The default is the [`SlidingWindowConversationManager`](../../../api-reference/python/agent/conversation_manager/sliding_window_conversation_manager.md#strands.agent.conversation_manager.sliding_window_conversation_manager.SlidingWindowConversationManager), which keeps recent messages and removes older ones when needed:

=== "Python"

    ```python
    from strands import Agent
    from strands.agent.conversation_manager import SlidingWindowConversationManager

    # Create a conversation manager with custom window size
    # By default, SlidingWindowConversationManager is used even if not specified
    conversation_manager = SlidingWindowConversationManager(
        window_size=10,  # Maximum number of message pairs to keep
    )

    # Use the conversation manager with your agent
    agent = Agent(conversation_manager=conversation_manager)
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/state.ts:conversation_manager_import"
    --8<-- "user-guide/concepts/agents/state.ts:conversation_manager"
    ```


The sliding window conversation manager:

- Keeps the most recent N message pairs
- Removes the oldest messages when the window size is exceeded
- Handles context window overflow exceptions by reducing context
- Ensures conversations don't exceed model context limits

See [Conversation Management](conversation-management.md) for more information about conversation managers.


## Agent State

Agent state provides key-value storage for stateful information that exists outside of the conversation context. Unlike conversation history, agent state is not passed to the model during inference but can be accessed and modified by tools and application logic.

### Basic Usage

=== "Python"

    ```python
    from strands import Agent

    # Create an agent with initial state
    agent = Agent(state={"user_preferences": {"theme": "dark"}, "session_count": 0})


    # Access state values
    theme = agent.state.get("user_preferences")
    print(theme)  # {"theme": "dark"}

    # Set new state values
    agent.state.set("last_action", "login")
    agent.state.set("session_count", 1)

    # Get entire state
    all_state = agent.state.get()
    print(all_state)  # All state data as a dictionary

    # Delete state values
    agent.state.delete("last_action")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/state.ts:agent_state_basic"
    ```

### State Validation and Safety

Agent state enforces JSON serialization validation to ensure data can be persisted and restored:

=== "Python"

    ```python
    from strands import Agent

    agent = Agent()

    # Valid JSON-serializable values
    agent.state.set("string_value", "hello")
    agent.state.set("number_value", 42)
    agent.state.set("boolean_value", True)
    agent.state.set("list_value", [1, 2, 3])
    agent.state.set("dict_value", {"nested": "data"})
    agent.state.set("null_value", None)

    # Invalid values will raise ValueError
    try:
        agent.state.set("function", lambda x: x)  # Not JSON serializable
    except ValueError as e:
        print(f"Error: {e}")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/state.ts:state_validation"
    ```

### Using State in Tools

!!! note

    To use `ToolContext` in your tool function, the parameter must be named `tool_context`. See [ToolContext documentation](../tools/custom-tools.md#toolcontext) for more information.


Agent state is particularly useful for maintaining information across tool executions:

=== "Python"

    ```python
    from strands import Agent, tool, ToolContext

    @tool(context=True)
    def track_user_action(action: str, tool_context: ToolContext):
        """Track user actions in agent state.
        
        Args:
            action: The action to track
        """
        # Get current action count
        action_count = tool_context.agent.state.get("action_count") or 0
        
        # Update state
        tool_context.agent.state.set("action_count", action_count + 1)
        tool_context.agent.state.set("last_action", action)
        
        return f"Action '{action}' recorded. Total actions: {action_count + 1}"

    @tool(context=True)
    def get_user_stats(tool_context: ToolContext):
        """Get user statistics from agent state."""
        action_count = tool_context.agent.state.get("action_count") or 0
        last_action = tool_context.agent.state.get("last_action") or "none"
        
        return f"Actions performed: {action_count}, Last action: {last_action}"

    # Create agent with tools
    agent = Agent(tools=[track_user_action, get_user_stats])

    # Use tools that modify and read state
    agent("Track that I logged in")
    agent("Track that I viewed my profile")
    print(f"Actions taken: {agent.state.get('action_count')}")
    print(f"Last action: {agent.state.get('last_action')}")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/state.ts:state_in_tools"
    ```

## Request State

Each agent interaction maintains a request state dictionary that persists throughout the event loop cycles and is **not** included in the agent's context:

=== "Python"

    ```python
    from strands import Agent

    def custom_callback_handler(**kwargs):
        # Access request state
        if "request_state" in kwargs:
            state = kwargs["request_state"]
            # Use or modify state as needed
            if "counter" not in state:
                state["counter"] = 0
            state["counter"] += 1
            print(f"Callback handler event count: {state['counter']}")

    agent = Agent(callback_handler=custom_callback_handler)

    result = agent("Hi there!")

    print(result.state)
    ```

{{ ts_not_supported_code() }}

The request state:

- Is initialized at the beginning of each agent call
- Persists through recursive event loop cycles
- Can be modified by callback handlers
- Is returned in the AgentResult object

## Persisting State Across Sessions

For information on how to persist agent state and conversation history across multiple interactions or application restarts, see the [Session Management](session-management.md) documentation.
