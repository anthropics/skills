# Prompts

In the Strands Agents SDK, system prompts and user messages are the primary way to communicate with AI models. The SDK provides a flexible system for managing prompts, including both system prompts and user messages.

## System Prompts

System prompts provide high-level instructions to the model about its role, capabilities, and constraints. They set the foundation for how the model should behave throughout the conversation. You can specify the system prompt when initializing an agent:

=== "Python"

    ```python
    from strands import Agent

    agent = Agent(
        system_prompt=(
            "You are a financial advisor specialized in retirement planning. "
            "Use tools to gather information and provide personalized advice. "
            "Always explain your reasoning and cite sources when possible."
        )
    )
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/prompts.ts:systemPrompt"
    ```

If you do not specify a system prompt, the model will behave according to its default settings.

## User Messages

These are your queries or requests to the agent. The SDK supports multiple techniques for prompting.

### Text Prompt

The simplest way to interact with an agent is through a text prompt:

=== "Python"

    ```python
    response = agent("What is the time in Seattle")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/prompts.ts:textPrompt"
    ```

### Multi-Modal Prompting
The SDK supports multi-modal prompts, allowing you to include images, documents, and other content types in your messages:

=== "Python"

    ```python
    with open("path/to/image.png", "rb") as fp:
        image_bytes = fp.read()

    response = agent([
        {"text": "What can you see in this image?"},
        {
            "image": {
                "format": "png",
                "source": {
                    "bytes": image_bytes,
                },
            },
        },
    ])
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/agents/prompts.ts:multimodalPrompt"
    ```

For a complete list of supported content types, please refer to the [API Reference](../../../api-reference/python/types/content.md#strands.types.content.ContentBlock).


### Direct Tool Calls

Prompting is a primary functionality of Strands that allows you to invoke tools through natural language requests. However, if at any point you require more programmatic control, Strands also allows you to invoke tools directly:

=== "Python"

    ```python
    result = agent.tool.current_time(timezone="US/Pacific")
    ```

{{ ts_not_supported_code() }}

Direct tool calls bypass the natural language interface and execute the tool using specified parameters. These calls are added to the conversation history by default. However, you can opt out of this behavior by setting `record_direct_tool_call=False` in Python.

## Prompt Engineering

For guidance on how to write safe and responsible prompts, please refer to our [Safety & Security - Prompt Engineering](../../safety-security/prompt-engineering.md) documentation.

Further resources:

* [Prompt Engineering Guide](https://www.promptingguide.ai)
* [Amazon Bedrock - Prompt engineering concepts](https://docs.aws.amazon.com/bedrock/latest/userguide/prompt-engineering-guidelines.html)
* [Llama - Prompting](https://www.llama.com/docs/how-to-guides/prompting/)
* [Anthropic - Prompt engineering overview](https://docs.anthropic.com/en/docs/build-with-claude/prompt-engineering/overview)
* [OpenAI - Prompt engineering](https://platform.openai.com/docs/guides/prompt-engineering/six-strategies-for-getting-better-results)
