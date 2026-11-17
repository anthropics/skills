# Conversation Management

In the Strands Agents SDK, context refers to the information provided to the agent for understanding and reasoning. This includes:

- User messages
- Agent responses
- Tool usage and results
- System prompts

As conversations grow, managing this context becomes increasingly important for several reasons:

1. **Token Limits**: Language models have fixed context windows (maximum tokens they can process)
2. **Performance**: Larger contexts require more processing time and resources
3. **Relevance**: Older messages may become less relevant to the current conversation
4. **Coherence**: Maintaining logical flow and preserving important information

## Built-in Conversation Managers

The SDK provides a flexible system for context management through the ConversationManager interface. This allows you to implement different strategies for managing conversation history. You can either leverage one of Strands's provided managers:

- [**NullConversationManager**](#nullconversationmanager): A simple implementation that does not modify conversation history
- [**SlidingWindowConversationManager**](#slidingwindowconversationmanager): Maintains a fixed number of recent messages (default manager)
- [**SummarizingConversationManager**](#summarizingconversationmanager): Intelligently summarizes older messages to preserve context

or [build your own manager](#creating-a-conversationmanager) that matches your requirements.


### NullConversationManager

The [`NullConversationManager`](../../../api-reference/python/agent/conversation_manager/null_conversation_manager.md#strands.agent.conversation_manager.null_conversation_manager.NullConversationManager) is a simple implementation that does not modify the conversation history. It's useful for:

- Short conversations that won't exceed context limits
- Debugging purposes
- Cases where you want to manage context manually

=== "Python"

    ```python
    from strands import Agent
    from strands.agent.conversation_manager import NullConversationManager

    agent = Agent(
        conversation_manager=NullConversationManager()
    )
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/conversation-management_imports.ts:null_conversation_manager_imports"

    --8<-- "user-guide/concepts/agents/conversation-management.ts:null_conversation_manager"
    ```

### SlidingWindowConversationManager

The [`SlidingWindowConversationManager`](../../../api-reference/python/agent/conversation_manager/sliding_window_conversation_manager.md#strands.agent.conversation_manager.sliding_window_conversation_manager.SlidingWindowConversationManager) implements a sliding window strategy that maintains a fixed number of recent messages. This is the default conversation manager used by the Agent class.

=== "Python"

    ```python
    from strands import Agent
    from strands.agent.conversation_manager import SlidingWindowConversationManager

    # Create a conversation manager with custom window size
    conversation_manager = SlidingWindowConversationManager(
        window_size=20,  # Maximum number of messages to keep
        should_truncate_results=True, # Enable truncating the tool result when a message is too large for the model's context window
    )

    agent = Agent(
        conversation_manager=conversation_manager
    )
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/conversation-management_imports.ts:sliding_window_conversation_manager_imports"

    --8<-- "user-guide/concepts/agents/conversation-management.ts:sliding_window_conversation_manager"
    ```

Key features of the `SlidingWindowConversationManager`:

- **Maintains Window Size**: Automatically removes messages from the window if the number of messages exceeds the limit.
- **Dangling Message Cleanup**: Removes incomplete message sequences to maintain valid conversation state.
- **Overflow Trimming**: In the case of a context window overflow, it will trim the oldest messages from history until the request fits in the models context window.
- **Configurable Tool Result Truncation**: Enable / disable truncation of tool results when the message exceeds context window limits. When `should_truncate_results=True` (default), large results are truncated with a placeholder message. When `False`, full results are preserved but more historical messages may be removed.
- **Per-Turn Management**: Optionally apply context management proactively during the agent loop execution, not just at the end.

**Per-Turn Management**:

By default, the `SlidingWindowConversationManager` applies context management only after the agent loop completes. The `per_turn` parameter allows you to proactively manage context during execution, which is useful for long-running agent loops with many tool calls.

=== "Python"

    ```python
    from strands import Agent
    from strands.agent.conversation_manager import SlidingWindowConversationManager

    # Apply management before every model call
    conversation_manager = SlidingWindowConversationManager(
        per_turn=True,  # Apply management before each model call
    )

    # Or apply management every N model calls
    conversation_manager = SlidingWindowConversationManager(
        per_turn=3,  # Apply management every 3 model calls
    )

    agent = Agent(
        conversation_manager=conversation_manager
    )
    ```

{{ ts_not_supported_code() }}

The `per_turn` parameter accepts:

- `False` (default): Only apply management after the agent loop completes
- `True`: Apply management before every model call
- An integer `N` (must be > 0): Apply management every N model calls

### SummarizingConversationManager

<!-- https://github.com/strands-agents/sdk-typescript/issues/279 -->
{{ ts_not_supported("") }}

The [`SummarizingConversationManager`](../../../api-reference/python/agent/conversation_manager/summarizing_conversation_manager.md#strands.agent.conversation_manager.summarizing_conversation_manager.SummarizingConversationManager) implements intelligent conversation context management by summarizing older messages instead of simply discarding them. This approach preserves important information while staying within context limits.

Configuration parameters:

- **`summary_ratio`** (float, default: 0.3): Percentage of messages to summarize when reducing context (clamped between 0.1 and 0.8)
- **`preserve_recent_messages`** (int, default: 10): Minimum number of recent messages to always keep
- **`summarization_agent`** (Agent, optional): Custom agent for generating summaries. If not provided, uses the main agent instance. Cannot be used together with `summarization_system_prompt`.
- **`summarization_system_prompt`** (str, optional): Custom system prompt for summarization. If not provided, uses a default prompt that creates structured bullet-point summaries focusing on key topics, tools used, and technical information in third-person format. Cannot be used together with `summarization_agent`.

**Basic Usage:**

By default, the `SummarizingConversationManager` leverages the same model and configuration as your main agent to perform summarization.

=== "Python"

    ```python
    from strands import Agent
    from strands.agent.conversation_manager import SummarizingConversationManager

    agent = Agent(
        conversation_manager=SummarizingConversationManager()
    )
    ```

{{ ts_not_supported_code() }}

You can also customize the behavior by adjusting parameters like summary ratio and number of preserved messages:

=== "Python"

    ```python
    from strands import Agent
    from strands.agent.conversation_manager import SummarizingConversationManager

    # Create the summarizing conversation manager with default settings
    conversation_manager = SummarizingConversationManager(
        summary_ratio=0.3,  # Summarize 30% of messages when context reduction is needed
        preserve_recent_messages=10,  # Always keep 10 most recent messages
    )

    agent = Agent(
        conversation_manager=conversation_manager
    )
    ```

{{ ts_not_supported_code() }}

**Custom System Prompt for Domain-Specific Summarization:**

You can customize the summarization behavior by providing a custom system prompt that tailors the summarization to your domain or use case.

=== "Python"

    ```python
    from strands import Agent
    from strands.agent.conversation_manager import SummarizingConversationManager

    # Custom system prompt for technical conversations
    custom_system_prompt = """
    You are summarizing a technical conversation. Create a concise bullet-point summary that:
    - Focuses on code changes, architectural decisions, and technical solutions
    - Preserves specific function names, file paths, and configuration details
    - Omits conversational elements and focuses on actionable information
    - Uses technical terminology appropriate for software development

    Format as bullet points without conversational language.
    """

    conversation_manager = SummarizingConversationManager(
        summarization_system_prompt=custom_system_prompt
    )

    agent = Agent(
        conversation_manager=conversation_manager
    )
    ```

{{ ts_not_supported_code() }}

**Advanced Configuration with Custom Summarization Agent:**

For advanced use cases, you can provide a custom `summarization_agent` to handle the summarization process. This enables using a different model (such as a faster or a more cost-effective one), incorporating tools during summarization, or implementing specialized summarization logic tailored to your domain. The custom agent can leverage its own system prompt, tools, and model configuration to generate summaries that best preserve the essential context for your specific use case.

=== "Python"

    ```python
    from strands import Agent
    from strands.agent.conversation_manager import SummarizingConversationManager
    from strands.models import AnthropicModel

    # Create a cheaper, faster model for summarization tasks
    summarization_model = AnthropicModel(
        model_id="claude-3-5-haiku-20241022",  # More cost-effective for summarization
        max_tokens=1000,
        params={"temperature": 0.1}  # Low temperature for consistent summaries
    )
    custom_summarization_agent = Agent(model=summarization_model)

    conversation_manager = SummarizingConversationManager(
        summary_ratio=0.4,
        preserve_recent_messages=8,
        summarization_agent=custom_summarization_agent
    )

    agent = Agent(
        conversation_manager=conversation_manager
    )
    ```

{{ ts_not_supported_code() }}

Key features of the `SummarizingConversationManager`:

- **Context Window Management**: Automatically reduces context when token limits are exceeded
- **Intelligent Summarization**: Uses structured bullet-point summaries to capture key information
- **Tool Pair Preservation**: Ensures tool use and result message pairs aren't broken during summarization
- **Flexible Configuration**: Customize summarization behavior through various parameters
- **Fallback Safety**: Handles summarization failures gracefully

## Creating a ConversationManager

=== "Python"

    To create a custom conversation manager, implement the [`ConversationManager`](../../../api-reference/python/agent/conversation_manager/conversation_manager.md#strands.agent.conversation_manager.conversation_manager.ConversationManager) interface, which is composed of three key elements:

    1. [`apply_management`](../../../api-reference/python/agent/conversation_manager/conversation_manager.md#strands.agent.conversation_manager.conversation_manager.ConversationManager.apply_management): This method is called after each event loop cycle completes to manage the conversation history. It's responsible for applying your management strategy to the messages array, which may have been modified with tool results and assistant responses. The agent runs this method automatically after processing each user input and generating a response.

    2. [`reduce_context`](../../../api-reference/python/agent/conversation_manager/conversation_manager.md#strands.agent.conversation_manager.conversation_manager.ConversationManager.reduce_context): This method is called when the model's context window is exceeded (typically due to token limits). It implements the specific strategy for reducing the window size when necessary. The agent calls this method when it encounters a context window overflow exception, giving your implementation a chance to trim the conversation history before retrying.

    3. `removed_message_count`: This attribute is tracked by conversation managers, and utilized by [Session Management](./session-management.md) to efficiently load messages from the session storage. The count represents messages provided by the user or LLM that have been removed from the agent's messages, but not messages included by the conversation manager through something like summarization.

    4. `register_hooks` (optional): Override this method to integrate with [hooks](./hooks.md). This enables proactive context management patterns, such as trimming context before model calls. Always call `super().register_hooks` when overriding.
   
    See the [SlidingWindowConversationManager](https://github.com/strands-agents/sdk-python/blob/main/src/strands/agent/conversation_manager/sliding_window_conversation_manager.py) implementation as a reference example.

=== "TypeScript"

    In TypeScript, conversation managers don't have a base interface. Instead, they are simply [HookProviders](./hooks.md) that can subscribe to any event in the agent lifecycle.

    For implementing custom conversation management, it's recommended to:

    - Register for the `AfterInvocationEvent` (or other After events) to perform proactive context trimming after each agent invocation completes
    - Register for the `AfterModelCallEvent` to handle reactive context trimming when the model's context window is exceeded

    See the [SlidingWindowConversationManager](https://github.com/strands-agents/sdk-typescript/blob/main/src/conversation-manager/sliding-window-conversation-manager.ts) implementation as a reference example.
