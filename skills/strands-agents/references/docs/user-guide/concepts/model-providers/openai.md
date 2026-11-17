# OpenAI

[OpenAI](https://platform.openai.com/docs/overview) is an AI research and deployment company that provides a suite of powerful language models. The Strands Agents SDK implements an OpenAI provider, allowing you to run agents against any OpenAI or OpenAI-compatible model.

## Installation

OpenAI is configured as an optional dependency in Strands Agents. To install, run:

=== "Python"

    ```bash
    pip install 'strands-agents[openai]' strands-agents-tools
    ```

=== "TypeScript"

    ```bash
    npm install @strands-agents/sdk openai
    ```

## Usage

After installing dependencies, you can import and initialize the Strands Agents' OpenAI provider as follows:

=== "Python"

    ```python
    from strands import Agent
    from strands.models.openai import OpenAIModel
    from strands_tools import calculator

    model = OpenAIModel(
        client_args={
            "api_key": "<KEY>",
        },
        # **model_config
        model_id="gpt-4o",
        params={
            "max_tokens": 1000,
            "temperature": 0.7,
        }
    )

    agent = Agent(model=model, tools=[calculator])
    response = agent("What is 2+2")
    print(response)
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/openai_imports.ts:basic_usage_imports"

    --8<-- "user-guide/concepts/model-providers/openai.ts:basic_usage"
    ```

To connect to a custom OpenAI-compatible server:

=== "Python"

    ```python
    model = OpenAIModel(
        client_args={
          "api_key": "<KEY>",
          "base_url": "<URL>",
        },
        ...
    )
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/openai.ts:custom_server"
    ```

## Configuration

### Client Configuration

=== "Python"

    The `client_args` configure the underlying OpenAI client. For a complete list of available arguments, please refer to the OpenAI [source](https://github.com/openai/openai-python).

=== "TypeScript"

    The `clientConfig` configures the underlying OpenAI client. For a complete list of available options, please refer to the [OpenAI TypeScript documentation](https://github.com/openai/openai-node).

### Model Configuration

The model configuration sets parameters for inference:

=== "Python"

    |  Parameter | Description | Example | Options |
    |------------|-------------|---------|---------|
    | `model_id` | ID of a model to use | `gpt-4o` | [reference](https://platform.openai.com/docs/models)
    | `params` | Model specific parameters | `{"max_tokens": 1000, "temperature": 0.7}` | [reference](https://platform.openai.com/docs/api-reference/chat/create)

=== "TypeScript"

    |  Parameter | Description | Example | Options |
    |------------|-------------|---------|---------|
    | `modelId` | ID of a model to use | `gpt-4o` | [reference](https://platform.openai.com/docs/models)
    | `maxTokens` | Maximum tokens to generate | `1000` | [reference](https://platform.openai.com/docs/api-reference/chat/create)
    | `temperature` | Controls randomness (0-2) | `0.7` | [reference](https://platform.openai.com/docs/api-reference/chat/create)
    | `topP` | Nucleus sampling (0-1) | `0.9` | [reference](https://platform.openai.com/docs/api-reference/chat/create)
    | `frequencyPenalty` | Reduces repetition (-2.0 to 2.0) | `0.5` | [reference](https://platform.openai.com/docs/api-reference/chat/create)
    | `presencePenalty` | Encourages new topics (-2.0 to 2.0) | `0.5` | [reference](https://platform.openai.com/docs/api-reference/chat/create)
    | `params` | Additional parameters not listed above | `{ stop: ["END"] }` | [reference](https://platform.openai.com/docs/api-reference/chat/create)

## Troubleshooting

=== "Python"

    **Module Not Found**

    If you encounter the error `ModuleNotFoundError: No module named 'openai'`, this means you haven't installed the `openai` dependency in your environment. To fix, run `pip install 'strands-agents[openai]'`.

=== "TypeScript"

    **Authentication Errors**

    If you encounter authentication errors, ensure your OpenAI API key is properly configured. Set the `OPENAI_API_KEY` environment variable or pass it via the `apiKey` parameter in the model configuration.

## Advanced Features

### Structured Output

OpenAI models support structured output through their native tool calling capabilities. When you use `Agent.structured_output()`, the Strands SDK automatically converts your schema to OpenAI's function calling format.

=== "Python"

    ```python
    from pydantic import BaseModel, Field
    from strands import Agent
    from strands.models.openai import OpenAIModel

    class PersonInfo(BaseModel):
        """Extract person information from text."""
        name: str = Field(description="Full name of the person")
        age: int = Field(description="Age in years")
        occupation: str = Field(description="Job or profession")

    model = OpenAIModel(
        client_args={"api_key": "<KEY>"},
        model_id="gpt-4o",
    )

    agent = Agent(model=model)

    result = agent.structured_output(
        PersonInfo,
        "John Smith is a 30-year-old software engineer working at a tech startup."
    )

    print(f"Name: {result.name}")      # "John Smith"
    print(f"Age: {result.age}")        # 30
    print(f"Job: {result.occupation}") # "software engineer"
    ```

{{ ts_not_supported_code("Structured output is not yet supported in the TypeScript SDK") }}

### Custom client

Users can pass their own custom OpenAI client to the OpenAIModel for Strands Agents to use directly. Users are responsible for handling the lifecycle (e.g., closing) of the client.

=== "Python"

    ```python
    from strands import Agent
    from strands.models.openai import OpenAIModel
    from openai import AsyncOpenAI

    client = AsyncOpenAI(
        api_key= "<KEY>",
    )

    agent = Agent(
        model = OpenAIModel(
            model_id="gpt-4o-mini-2024-07-18",
            client=client
        )
    )

    async def chat(prompt: str):
        result = await agent.invoke_async(prompt)
        print(result)
    
    async def main():
        await chat("What is 2+2")
        await chat("What is 2*2")
        # close the client
        client.close()

    if __name__ == "__main__":
        asyncio.run(main())
    ```

{{ ts_not_supported_code("Custom client capability is not yet supported in the TypeScript SDK") }}

## References

- [API](../../../api-reference/python/models/model.md)
- [OpenAI](https://platform.openai.com/docs/overview)
