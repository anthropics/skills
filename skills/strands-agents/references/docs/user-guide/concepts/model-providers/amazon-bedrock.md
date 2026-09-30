# Amazon Bedrock

Amazon Bedrock is a fully managed service that offers a choice of high-performing foundation models from leading AI companies through a unified API. Strands provides native support for Amazon Bedrock, allowing you to use these powerful models in your agents with minimal configuration.

The `BedrockModel` class in Strands enables seamless integration with Amazon Bedrock's API, supporting:

- Text generation
- Multi-Modal understanding (Image, Document, etc.)
- Tool/function calling
- Guardrail configurations
- System Prompt, Tool, and/or Message caching

## Getting Started

### Prerequisites

1. **AWS Account**: You need an AWS account with access to Amazon Bedrock
2. **AWS Credentials**: Configure AWS credentials with appropriate permissions

#### Required IAM Permissions

To use Amazon Bedrock with Strands, your IAM user or role needs the following permissions:

- `bedrock:InvokeModelWithResponseStream` (for streaming mode)
- `bedrock:InvokeModel` (for non-streaming mode)

Here's a sample IAM policy that grants the necessary permissions:

```json
{
    "Version": "2012-10-17",
    "Statement": [
        {
            "Effect": "Allow",
            "Action": [
                "bedrock:InvokeModelWithResponseStream",
                "bedrock:InvokeModel"
            ],
            "Resource": "*"
        }
    ]
}
```

For production environments, it's recommended to scope down the `Resource` to specific model ARNs.

#### Setting Up AWS Credentials

=== "Python"

    Strands uses [boto3](https://boto3.amazonaws.com/v1/documentation/api/latest/index.html) (the AWS SDK for Python) to make calls to Amazon Bedrock. Boto3 has its own credential resolution system that determines which credentials to use when making requests to AWS.

    For development environments, configure credentials using one of these methods:

    **Option 1: AWS CLI**

    ```bash
    aws configure
    ```

    **Option 2: Environment Variables**

    ```bash
    export AWS_ACCESS_KEY_ID=your_access_key
    export AWS_SECRET_ACCESS_KEY=your_secret_key
    export AWS_SESSION_TOKEN=your_session_token  # If using temporary credentials
    export AWS_REGION="us-west-2"  # Used if a custom Boto3 Session is not provided
    ```

    !!! warning "Region Resolution Priority"

        Due to boto3's behavior, the region resolution follows this priority order:

        1. Region explicitly passed to `BedrockModel(region_name="...")`
        2. Region from boto3 session (AWS_DEFAULT_REGION or profile region from ~/.aws/config)
        3. AWS_REGION environment variable
        4. Default region (us-west-2)

        This means `AWS_REGION` has lower priority than regions set in AWS profiles. If you're experiencing unexpected region behavior, check your AWS configuration files and consider using `AWS_DEFAULT_REGION` or explicitly passing `region_name` to the BedrockModel constructor.

        For more details, see the [boto3 issue discussion](https://github.com/boto/boto3/issues/2574).

    **Option 3: Custom Boto3 Session**

    You can configure a custom [boto3 Session](https://boto3.amazonaws.com/v1/documentation/api/latest/reference/core/session.html) and pass it to the `BedrockModel`:

    ```python
    import boto3
    from strands.models import BedrockModel

    # Create a custom boto3 session
    session = boto3.Session(
        aws_access_key_id='your_access_key',
        aws_secret_access_key='your_secret_key',
        aws_session_token='your_session_token',  # If using temporary credentials
        region_name='us-west-2',
        profile_name='your-profile'  # Optional: Use a specific profile
    )

    # Create a Bedrock model with the custom session
    bedrock_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0",
        boto_session=session
    )
    ```

    For complete details on credential configuration and resolution, see the [boto3 credentials documentation](https://boto3.amazonaws.com/v1/documentation/api/latest/guide/credentials.html#configuring-credentials).

=== "TypeScript"

    The TypeScript SDK uses the [AWS SDK for JavaScript v3](https://docs.aws.amazon.com/sdk-for-javascript/v3/developer-guide/welcome.html) to make calls to Amazon Bedrock. The SDK has its own credential resolution system that determines which credentials to use when making requests to AWS.

    For development environments, configure credentials using one of these methods:

    **Option 1: AWS CLI**

    ```bash
    aws configure
    ```

    **Option 2: Environment Variables**

    ```bash
    export AWS_ACCESS_KEY_ID=your_access_key
    export AWS_SECRET_ACCESS_KEY=your_secret_key
    export AWS_SESSION_TOKEN=your_session_token  # If using temporary credentials
    export AWS_REGION="us-west-2"
    ```

    **Option 3: Custom Credentials**

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock_imports.ts:custom_credentials_imports"

    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:custom_credentials"
    ```

    For complete details on credential configuration, see the [AWS SDK for JavaScript documentation](https://docs.aws.amazon.com/sdk-for-javascript/v3/developer-guide/setting-credentials-node.html).

## Basic Usage

=== "Python"

    The [`BedrockModel`](../../../api-reference/python/models/bedrock.md#strands.models.bedrock) provider is used by default when creating a basic Agent, and uses the [Claude Sonnet 4](https://aws.amazon.com/blogs/aws/claude-opus-4-anthropics-most-powerful-model-for-coding-is-now-in-amazon-bedrock/) model by default. This basic example creates an agent using this default setup:

    ```python
    from strands import Agent

    agent = Agent()

    response = agent("Tell me about Amazon Bedrock.")
    ```

    You can specify which Bedrock model to use by passing in the model ID string directly to the Agent constructor:

    ```python
    from strands import Agent

    # Create an agent with a specific model by passing the model ID string
    agent = Agent(model="anthropic.claude-sonnet-4-20250514-v1:0")

    response = agent("Tell me about Amazon Bedrock.")
    ```

=== "TypeScript"

    The [`BedrockModel`](../../../api-reference/typescript/classes/BedrockModel.html) provider is used by default when creating a basic Agent, and uses the [Claude Sonnet 4.5](https://aws.amazon.com/blogs/aws/introducing-claude-sonnet-4-5-in-amazon-bedrock-anthropics-most-intelligent-model-best-for-coding-and-complex-agents/) model by default. This basic example creates an agent using this default setup:

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock_imports.ts:basic_default_imports"

    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:basic_default"
    ```

    You can specify which Bedrock model to use by passing in the model ID string directly to the Agent constructor:

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock_imports.ts:basic_default_imports"

    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:basic_model_id"
    ```

> **Note:** See [Bedrock troubleshooting](amazon-bedrock.md#troubleshooting) if you encounter any issues.

### Custom Configuration

=== "Python"

    For more control over model configuration, you can create an instance of the [`BedrockModel`](../../../api-reference/python/models/bedrock.md#strands.models.bedrock) class:

    ```python
    from strands import Agent
    from strands.models import BedrockModel

    # Create a Bedrock model instance
    bedrock_model = BedrockModel(
        model_id="us.amazon.nova-premier-v1:0",
        temperature=0.3,
        top_p=0.8,
    )

    # Create an agent using the BedrockModel instance
    agent = Agent(model=bedrock_model)

    # Use the agent
    response = agent("Tell me about Amazon Bedrock.")
    ```

=== "TypeScript"

    For more control over model configuration, you can create an instance of the [`BedrockModel`](../../../api-reference/typescript/classes/BedrockModel.html) class:

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:basic_model_instance"
    ```

## Configuration Options

=== "Python"

    The [`BedrockModel`](../../../api-reference/python/models/bedrock.md#strands.models.bedrock) supports various configuration parameters. For a complete list of available options, see the [BedrockModel API reference](../../../api-reference/python/models/bedrock.md#strands.models.bedrock).

    Common configuration parameters include:

    - `model_id` - The Bedrock model identifier
    - `temperature` - Controls randomness (higher = more random)
    - `max_tokens` - Maximum number of tokens to generate
    - `streaming` - Enable/disable streaming mode
    - `guardrail_id` - ID of the guardrail to apply
    - `cache_prompt` / `cache_tools` - Enable prompt/tool caching
    - `boto_session` - Custom boto3 session for AWS credentials
    - `additional_request_fields` - Additional model-specific parameters

=== "TypeScript"

    The [`BedrockModel`](../../../api-reference/typescript/interfaces/BedrockModelOptions.html) supports various configuration parameters. For a complete list of available options, see the [BedrockModelOptions API reference](../../../api-reference/typescript/interfaces/BedrockModelOptions.html).

    Common configuration parameters include:

    - `modelId` - The Bedrock model identifier
    - `temperature` - Controls randomness (higher = more random)
    - `maxTokens` - Maximum number of tokens to generate
    - `streaming` - Enable/disable streaming mode
    - `cacheTools` - Enable tool caching
    - `region` - AWS region to use
    - `credentials` - AWS credentials configuration
    - `additionalArgs` - Additional model-specific parameters

### Example with Configuration

=== "Python"

    ```python
    from strands import Agent
    from strands.models import BedrockModel
    from botocore.config import Config as BotocoreConfig

    # Create a boto client config with custom settings
    boto_config = BotocoreConfig(
        retries={"max_attempts": 3, "mode": "standard"},
        connect_timeout=5,
        read_timeout=60
    )

    # Create a configured Bedrock model
    bedrock_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0",
        region_name="us-east-1",  # Specify a different region than the default
        temperature=0.3,
        top_p=0.8,
        stop_sequences=["###", "END"],
        boto_client_config=boto_config,
    )

    # Create an agent with the configured model
    agent = Agent(model=bedrock_model)

    # Use the agent
    response = agent("Write a short story about an AI assistant.")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:configuration"
    ```

## Advanced Features

### Streaming vs Non-Streaming Mode

Certain Amazon Bedrock models only support non-streaming tool use, so you can set the streaming configuration to false
in order to use these models. Both modes provide the same event structure and functionality in your agent, as the non-streaming responses are converted to the streaming format internally.

=== "Python"

    ```python
    # Streaming model (default)
    streaming_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0",
        streaming=True,  # This is the default
    )

    # Non-streaming model
    non_streaming_model = BedrockModel(
        model_id="us.meta.llama3-2-90b-instruct-v1:0",
        streaming=False,  # Disable streaming
    )
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:streaming"
    ```

See the Amazon Bedrock documentation for [Supported models and model features](https://docs.aws.amazon.com/bedrock/latest/userguide/conversation-inference-supported-models-features.html) to learn about the streaming support for different models.

### Multimodal Support

Some Bedrock models support multimodal inputs (Documents, Images, etc.). Here's how to use them:

=== "Python"

    ```python
    from strands import Agent
    from strands.models import BedrockModel

    # Create a Bedrock model that supports multimodal inputs
    bedrock_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0"
    )
    agent = Agent(model=bedrock_model)

    # Send the multimodal message to the agent
    response = agent(
        [
            {
                "document": {
                    "format": "txt",
                    "name": "example",
                    "source": {
                        "bytes": b"Once upon a time..."
                    }
                }
            },
            {
                "text": "Tell me about the document."
            }
        ]
    )
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:multimodal_full"
    ```

For a complete list of input types, please refer to the [API Reference](../../../api-reference/python/types/content.md).

#### S3 Location Support

As an alternative to providing media content as bytes, Amazon Bedrock supports referencing documents, images, and videos stored in Amazon S3 directly. This is useful when working with large files or when your content is already stored in S3.

!!! note "IAM Permissions Required"

    To use S3 locations, the IAM role or user making the Bedrock API call must have `s3:GetObject` permission on the S3 bucket and objects being referenced.

=== "Python"

    ```python
    from strands import Agent
    from strands.models import BedrockModel

    agent = Agent(model=BedrockModel())

    response = agent(
        [
            {
                "document": {
                    "format": "pdf",
                    "name": "report.pdf",
                    "source": {
                        "location": {
                            "type": "s3",
                            "uri": "s3://my-bucket/documents/report.pdf",
                            "bucketOwner": "123456789012"  # Optional: for cross-account access
                        }
                    }
                }
            },
            {
                "text": "Summarize this document."
            }
        ]
    )
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:s3_location"
    ```

!!! tip "Supported Media Types"

    The same `s3Location` pattern also works for images and videos.

### Guardrails

=== "Python"

    Amazon Bedrock supports guardrails to help ensure model outputs meet your requirements. Strands allows you to configure guardrails with your [`BedrockModel`](../../../api-reference/python/models/bedrock.md#strands.models.bedrock):

    ```python
    from strands import Agent
    from strands.models import BedrockModel

    # Using guardrails with BedrockModel
    bedrock_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0",
        guardrail_id="your-guardrail-id",
        guardrail_version="DRAFT",
        guardrail_trace="enabled",  # Options: "enabled", "disabled", "enabled_full"
        guardrail_stream_processing_mode="sync",  # Options: "sync", "async"
        guardrail_redact_input=True,  # Default: True
        guardrail_redact_input_message="Blocked Input!", # Default: [User input redacted.]
        guardrail_redact_output=False,  # Default: False
        guardrail_redact_output_message="Blocked Output!" # Default: [Assistant output redacted.]
    )

    guardrail_agent = Agent(model=bedrock_model)

    response = guardrail_agent("Can you tell me about the Strands SDK?")
    ```

    Amazon Bedrock supports guardrails to help ensure model outputs meet your requirements. Strands allows you to configure guardrails with your [`BedrockModel`](../../../api-reference/typescript/classes/BedrockModel.html).

    When a guardrail is triggered:

    - Input redaction (enabled by default): If a guardrail policy is triggered, the input is redacted
    - Output redaction (disabled by default): If a guardrail policy is triggered, the output is redacted
    - Custom redaction messages can be specified for both input and output redactions

{{ ts_not_supported_code("Guardrails are not yet supported in the TypeScript SDK") }}


### Caching

Strands supports caching system prompts, tools, and messages to improve performance and reduce costs. Caching allows you to reuse parts of previous requests, which can significantly reduce token usage and latency.

When you enable prompt caching, Amazon Bedrock creates a cache composed of **cache checkpoints**. These are markers that define the contiguous subsection of your prompt that you wish to cache. Cached content must remain unchanged between requests - any alteration invalidates the cache.

Prompt caching is supported for Anthropic Claude and Amazon Nova models on Bedrock. Each model has a minimum token requirement (e.g., 1,024 tokens for Claude Sonnet, 4,096 tokens for Claude Haiku), and cached content expires after 5 minutes of inactivity. Cache writes cost more than regular input tokens, but cache reads cost significantly less - see [Amazon Bedrock pricing](https://aws.amazon.com/bedrock/pricing/) for model-specific rates.

For complete details on supported models, token requirements, and cache field support, see the [Amazon Bedrock prompt caching documentation](https://docs.aws.amazon.com/bedrock/latest/userguide/prompt-caching.html#prompt-caching-models).

#### System Prompt Caching

Cache system prompts that remain static across multiple requests. This is useful when your system prompt contains no variables, timestamps, or dynamic content, exceeds the minimum cacheable token threshold for your model, and you make multiple requests with the same system prompt.

=== "Python"

    ```python
    from strands import Agent
    from strands.types.content import SystemContentBlock

    system_content = [
        SystemContentBlock(
            text="You are a helpful assistant..." * 1600  # Must exceed minimum tokens
        ),
        SystemContentBlock(cachePoint={"type": "default"})
    ]

    # Create an agent with SystemContentBlock array
    agent = Agent(system_prompt=system_content)

    # First request will cache the system prompt
    response1 = agent("Tell me about Python")
    print(f"Cache write tokens: {response1.metrics.accumulated_usage.get('cacheWriteInputTokens')}")
    print(f"Cache read tokens: {response1.metrics.accumulated_usage.get('cacheReadInputTokens')}")

    # Second request will reuse the cached system prompt
    response2 = agent("Tell me about JavaScript")
    print(f"Cache write tokens: {response2.metrics.accumulated_usage.get('cacheWriteInputTokens')}")
    print(f"Cache read tokens: {response2.metrics.accumulated_usage.get('cacheReadInputTokens')}")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:system_prompt_caching_full"
    ```

#### Tool Caching

Tool caching allows you to reuse a cached tool definition across multiple requests:

=== "Python"

    ```python
    from strands import Agent, tool
    from strands.models import BedrockModel
    from strands_tools import calculator, current_time

    # Using tool caching with BedrockModel
    bedrock_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0",
        cache_tools="default"
    )

    # Create an agent with the model and tools
    agent = Agent(
        model=bedrock_model,
        tools=[calculator, current_time]
    )
    # First request will cache the tools
    response1 = agent("What time is it?")
    print(f"Cache write tokens: {response1.metrics.accumulated_usage.get('cacheWriteInputTokens')}")
    print(f"Cache read tokens: {response1.metrics.accumulated_usage.get('cacheReadInputTokens')}")

    # Second request will reuse the cached tools
    response2 = agent("What is the square root of 1764?")
    print(f"Cache write tokens: {response2.metrics.accumulated_usage.get('cacheWriteInputTokens')}")
    print(f"Cache read tokens: {response2.metrics.accumulated_usage.get('cacheReadInputTokens')}")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:tool_caching_full"
    ```

#### Messages Caching

Messages caching allows you to reuse cached conversation context across multiple requests. By default, message caching is not enabled. To enable it, choose Option A for automatic cache management in agent workflows, or Option B for manual control over cache placement.

**Option A: Automatic Cache Strategy (Claude models only)**

Enable automatic cache point management for agent workflows with repeated tool calls and multi-turn conversations. The SDK automatically places a cache point at the end of each assistant message to maximize cache hits without requiring manual management.

=== "Python"

    ```python
    from strands import Agent, tool
    from strands.models import BedrockModel, CacheConfig

    @tool
    def web_search(query: str) -> str:
        """Search the web for information."""
        return f"""
        Search results for '{query}':
        1. Comprehensive Guide - [Long article with detailed explanations...]
        2. Research Paper - [Detailed findings and methodology...]
        3. Stack Overflow - [Multiple answers and code snippets...]
        """

    model = BedrockModel(
        model_id="us.anthropic.claude-sonnet-4-5-20250929-v1:0",
        cache_config=CacheConfig(strategy="auto")
    )
    agent = Agent(model=model, tools=[web_search])

    # Agent call with tool uses - cache write and read occur as context accumulates
    response1 = agent("Search for Python async patterns, then compare with error handling")
    print(f"Cache write tokens: {response1.metrics.accumulated_usage.get('cacheWriteInputTokens')}")
    print(f"Cache read tokens: {response1.metrics.accumulated_usage.get('cacheReadInputTokens')}")

    # Follow-up reuses cached context from previous conversation
    response2 = agent("Summarize the key differences")
    print(f"Cache write tokens: {response2.metrics.accumulated_usage.get('cacheWriteInputTokens')}")
    print(f"Cache read tokens: {response2.metrics.accumulated_usage.get('cacheReadInputTokens')}")
    ```

{{ ts_not_supported_code("Automatic cache strategy is not yet supported in the TypeScript SDK") }}

> **Note**: Cache misses occur if you intentionally modify past conversation context (e.g., summarization or editing previous messages).

**Option B: Manual Cache Points**

Place cache points explicitly at specific locations in your conversation when you need fine-grained control over cache placement based on your workload characteristics. This is useful for static use cases with repeated query patterns where you want to cache only up to a specific point. For agent loops or multi-turn conversations with manual cache control, use [Hooks](https://strandsagents.com/latest/documentation/docs/api-reference/python/hooks/events/) to dynamically control cache points based on specific events.

=== "Python"

    ```python
    from strands import Agent

    messages = [
        {
            "role": "user",
            "content": [
                {"text": """Here is a technical document:
                [Long document content with multiple sections covering architecture,
                implementation details, code examples, and best practices spanning
                over 1000 tokens...]"""},
                {"cachePoint": {"type": "default"}}  # Cache only up to this point
            ]
        }
    ]

    agent = Agent(messages=messages)

    # First request writes the document to cache
    response1 = agent("Summarize the key points from the document")
    print(f"Cache write tokens: {response1.metrics.accumulated_usage.get('cacheWriteInputTokens')}")
    print(f"Cache read tokens: {response1.metrics.accumulated_usage.get('cacheReadInputTokens')}")

    # Subsequent requests read the cached document
    response2 = agent("What are the implementation recommendations?")
    print(f"Cache write tokens: {response2.metrics.accumulated_usage.get('cacheWriteInputTokens')}")
    print(f"Cache read tokens: {response2.metrics.accumulated_usage.get('cacheReadInputTokens')}")
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:messages_caching_full"
    ```

#### Cache Metrics

When using prompt caching, Amazon Bedrock provides cache statistics to help you monitor cache performance:

- `CacheWriteInputTokens`: Number of input tokens written to the cache (occurs on first request with new content)
- `CacheReadInputTokens`: Number of input tokens read from the cache (occurs on subsequent requests with cached content)

Strands automatically captures these metrics and makes them available:

=== "Python"

    Cache statistics are automatically included in `AgentResult.metrics.accumulated_usage`:

    ```python
    from strands import Agent

    agent = Agent()
    response = agent("Hello!")
    
    # Access cache metrics
    cache_write = response.metrics.accumulated_usage.get('cacheWriteInputTokens', 0)
    cache_read = response.metrics.accumulated_usage.get('cacheReadInputTokens', 0)
    
    print(f"Cache write tokens: {cache_write}")
    print(f"Cache read tokens: {cache_read}")
    ```

    Cache metrics are also automatically recorded in OpenTelemetry traces when telemetry is enabled.

=== "TypeScript"

    Cache statistics are included in `modelMetadataEvent.usage` during streaming:

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock_imports.ts:basic_default_imports"

    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:cache_metrics"
    ```

### Updating Configuration at Runtime

You can update the model configuration during runtime:

=== "Python"

    ```python
    # Create the model with initial configuration
    bedrock_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0",
        temperature=0.7
    )

    # Update configuration later
    bedrock_model.update_config(
        temperature=0.3,
        top_p=0.2,
    )
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:update_config"
    ```

This is especially useful for tools that need to update the model's configuration:

=== "Python"

    ```python
    @tool
    def update_model_id(model_id: str, agent: Agent) -> str:
        """
        Update the model id of the agent

        Args:
          model_id: Bedrock model id to use.
        """
        print(f"Updating model_id to {model_id}")
        agent.model.update_config(model_id=model_id)
        return f"Model updated to {model_id}"


    @tool
    def update_temperature(temperature: float, agent: Agent) -> str:
        """
        Update the temperature of the agent

        Args:
          temperature: Temperature value for the model to use.
        """
        print(f"Updating Temperature to {temperature}")
        agent.model.update_config(temperature=temperature)
        return f"Temperature updated to {temperature}"
    ```

=== "TypeScript"

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock_imports.ts:tool_update_config_imports"

    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:tool_update_config"
    ```

### Reasoning Support

Amazon Bedrock models can provide detailed reasoning steps when generating responses. For detailed information about supported models and reasoning token configuration, see the [Amazon Bedrock documentation on inference reasoning](https://docs.aws.amazon.com/bedrock/latest/userguide/inference-reasoning.html).

=== "Python"

    Strands allows you to enable and configure reasoning capabilities with your [`BedrockModel`](../../../api-reference/python/models/bedrock.md#strands.models.bedrock):

    ```python
    from strands import Agent
    from strands.models import BedrockModel

    # Create a Bedrock model with reasoning configuration
    bedrock_model = BedrockModel(
        model_id="anthropic.claude-sonnet-4-20250514-v1:0",
        additional_request_fields={
            "thinking": {
                "type": "enabled",
                "budget_tokens": 4096 # Minimum of 1,024
            }
        }
    )

    # Create an agent with the reasoning-enabled model
    agent = Agent(model=bedrock_model)

    # Ask a question that requires reasoning
    response = agent("If a train travels at 120 km/h and needs to cover 450 km, how long will the journey take?")
    ```

=== "TypeScript"

    Strands allows you to enable and configure reasoning capabilities with your [`BedrockModel`](../../../api-reference/typescript/classes/BedrockModel.html):

    ```typescript
    --8<-- "user-guide/concepts/model-providers/amazon-bedrock.ts:reasoning"
    ```

> **Note**: Not all models support structured reasoning output. Check the [inference reasoning documentation](https://docs.aws.amazon.com/bedrock/latest/userguide/inference-reasoning.html) for details on supported models.

### Structured Output

=== "Python"

    Amazon Bedrock models support structured output through their tool calling capabilities. When you use `Agent.structured_output()`, the Strands SDK converts your schema to Bedrock's tool specification format.

    ```python
    from pydantic import BaseModel, Field
    from strands import Agent
    from strands.models import BedrockModel
    from typing import List, Optional

    class ProductAnalysis(BaseModel):
        """Analyze product information from text."""
        name: str = Field(description="Product name")
        category: str = Field(description="Product category")
        price: float = Field(description="Price in USD")
        features: List[str] = Field(description="Key product features")
        rating: Optional[float] = Field(description="Customer rating 1-5", ge=1, le=5)

    bedrock_model = BedrockModel()

    agent = Agent(model=bedrock_model)

    result = agent.structured_output(
        ProductAnalysis,
        """
        Analyze this product: The UltraBook Pro is a premium laptop computer
        priced at $1,299. It features a 15-inch 4K display, 16GB RAM, 512GB SSD,
        and 12-hour battery life. Customer reviews average 4.5 stars.
        """
    )

    print(f"Product: {result.name}")
    print(f"Category: {result.category}")
    print(f"Price: ${result.price}")
    print(f"Features: {result.features}")
    print(f"Rating: {result.rating}")
    ```

{{ ts_not_supported_code("Structured output is not yet supported in the TypeScript SDK") }}

## Troubleshooting

### On-demand throughput isn’t supported

If you encounter the error:

> Invocation of model ID XXXX with on-demand throughput isn’t supported. Retry your request with the ID or ARN of an inference profile that contains this model.

This typically indicates that the model requires Cross-Region Inference, as documented in the [Amazon Bedrock documentation on inference profiles](https://docs.aws.amazon.com/bedrock/latest/userguide/inference-profiles-support.html#inference-profiles-support-system).  To resolve this issue, prefix your model ID with the appropriate regional identifier (`us.`or `eu.`) based on where your agent is running. For example:

Instead of: 

```
anthropic.claude-sonnet-4-20250514-v1:0
```

Use: 

```
us.anthropic.claude-sonnet-4-20250514-v1:0
```


### Model identifier is invalid
If you encounter the error:

> ValidationException: An error occurred (ValidationException) when calling the ConverseStream operation: The provided model identifier is invalid

This is very likely due to calling Bedrock with an inference model id, such as: `us.anthropic.claude-sonnet-4-20250514-v1:0` from a region that does not [support inference profiles](https://docs.aws.amazon.com/bedrock/latest/userguide/inference-profiles-support.html). If so, pass in a valid model id, as follows:

=== "Python"

    ```python
    agent = Agent(model="anthropic.claude-3-5-sonnet-20241022-v2:0")
    ```

=== "TypeScript"

    ```typescript
    const agent = new Agent({ 
      model: 'anthropic.claude-3-5-sonnet-20241022-v2:0' 
    })
    ```


!!! note ""

    Strands uses a default Claude 4 Sonnet inference model from the region of your credentials when no model is provided. So if you did not pass in any model id and are getting the above error, it's very likely due to the `region` from the credentials not supporting inference profiles.



## Related Resources

- [Amazon Bedrock Documentation](https://docs.aws.amazon.com/bedrock/)
- [Bedrock Model IDs Reference](https://docs.aws.amazon.com/bedrock/latest/userguide/model-ids.html)
- [Bedrock Pricing](https://aws.amazon.com/bedrock/pricing/)

