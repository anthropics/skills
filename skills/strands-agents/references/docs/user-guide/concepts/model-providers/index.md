# Model Providers

## What are Model Providers?

A model provider is a service or platform that hosts and serves large language models through an API. The Strands Agents SDK abstracts away the complexity of working with different providers, offering a unified interface that makes it easy to switch between models or use multiple providers in the same application.

## Supported Providers

The following table shows all model providers supported by Strands Agents SDK and their availability in Python and TypeScript:

| Provider                                     | Python Support | TypeScript Support |
|----------------------------------------------|----------------|-------------------|
| [Custom Providers](custom_model_provider.md) | ✅ | ✅ |
| [Amazon Bedrock](amazon-bedrock.md)          | ✅ | ✅ |
| [Amazon Nova](amazon-nova.md)                | ✅ | ❌ |
| [OpenAI](openai.md)                          | ✅ | ✅ |
| [Anthropic](anthropic.md)                    | ✅ | ❌ |
| [Gemini](gemini.md)                          | ✅ | ❌ |
| [LiteLLM](litellm.md)                        | ✅ | ❌ |
| [llama.cpp](llamacpp.md)                     | ✅ | ❌ |
| [LlamaAPI](llamaapi.md)                      | ✅ | ❌ |
| [MistralAI](mistral.md)                      | ✅ | ❌ |
| [Ollama](ollama.md)                          | ✅ | ❌ |
| [SageMaker](sagemaker.md)                    | ✅ | ❌ |
| [Writer](writer.md)                          | ✅ | ❌ |
| [Cohere](cohere.md)                          | ✅ | ❌ |
| [CLOVA Studio](clova-studio.md)              | ✅ | ❌ |
| [FireworksAI](fireworksai.md)                | ✅ | ❌ |
| [xAI](xai.md)                                | ✅ | ❌ |

## Getting Started

### Installation

Most providers are available as optional dependencies. Install the provider you need:

=== "Python"

    ```bash
    # Install with specific provider
    pip install 'strands-agents[bedrock]'
    pip install 'strands-agents[openai]'
    pip install 'strands-agents[anthropic]'

    # Or install with all providers
    pip install 'strands-agents[all]'
    ```

=== "TypeScript"

    ```bash
    # Core SDK includes BedrockModel by default
    npm install @strands-agents/sdk

    # To use OpenAI, install the openai package
    npm install openai
    ```

    > **Note:** All model providers except Bedrock are listed as optional dependencies in the SDK. This means npm will attempt to install them automatically, but won't fail if they're unavailable. You can explicitly install them when needed.

### Basic Usage

Each provider follows a similar pattern for initialization and usage. Models are interchangeable - you can easily switch between providers by changing the model instance:

=== "Python"

    ```python
    from strands import Agent
    from strands.models.bedrock import BedrockModel
    from strands.models.openai import OpenAIModel

    # Use Bedrock
    bedrock_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0"
    )
    agent = Agent(model=bedrock_model)
    response = agent("What can you help me with?")

    # Alternatively, use OpenAI by just switching model provider
    openai_model = OpenAIModel(
        client_args={"api_key": "<KEY>"},
        model_id="gpt-4o"
    )
    agent = Agent(model=openai_model)
    response = agent("What can you help me with?")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/index_imports.ts:basic_usage_imports"

    --8<-- "user-guide/concepts/model-providers/index.ts:basic_usage"
    ```

## Next Steps

### Explore Model Providers

- **[Amazon Bedrock](amazon-bedrock.md)** - Default provider with wide model selection, enterprise features, and full Python/TypeScript support
- **[OpenAI](openai.md)** - GPT models with streaming support
- **[Custom Providers](custom_model_provider.md)** - Build your own model integration
- **[Anthropic](anthropic.md)** - Direct Claude API access (Python only)

