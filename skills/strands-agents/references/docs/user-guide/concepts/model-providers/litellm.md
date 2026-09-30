# LiteLLM

!!! info "Language Support"
    This provider is only supported in Python.

[LiteLLM](https://docs.litellm.ai/docs/) is a unified interface for various LLM providers that allows you to interact with models from Amazon, Anthropic, OpenAI, and many others through a single API. The Strands Agents SDK implements a LiteLLM provider, allowing you to run agents against any model LiteLLM supports.

## Installation

LiteLLM is configured as an optional dependency in Strands Agents. To install, run:

```bash
pip install 'strands-agents[litellm]' strands-agents-tools
```

## Usage

After installing `litellm`, you can import and initialize Strands Agents' LiteLLM provider as follows:

```python
from strands import Agent
from strands.models.litellm import LiteLLMModel
from strands_tools import calculator

model = LiteLLMModel(
    client_args={
        "api_key": "<KEY>",
    },
    # **model_config
    model_id="anthropic/claude-3-7-sonnet-20250219",
    params={
        "max_tokens": 1000,
        "temperature": 0.7,
    }
)

agent = Agent(model=model, tools=[calculator])
response = agent("What is 2+2")
print(response)
```

## Using LiteLLM Proxy

To use a [LiteLLM Proxy Server](https://docs.litellm.ai/docs/simple_proxy), you have two options:

### Option 1: Use `use_litellm_proxy` parameter

```python
from strands import Agent
from strands.models.litellm import LiteLLMModel

model = LiteLLMModel(
    client_args={
        "api_key": "<PROXY_KEY>",
        "api_base": "<PROXY_URL>",
        "use_litellm_proxy": True
    },
    model_id="amazon.nova-lite-v1:0"
)

agent = Agent(model=model)
response = agent("Tell me a story")
```

### Option 2: Use `litellm_proxy/` prefix in model ID

```python
model = LiteLLMModel(
    client_args={
        "api_key": "<PROXY_KEY>",
        "api_base": "<PROXY_URL>"
    },
    model_id="litellm_proxy/amazon.nova-lite-v1:0"
)
```

## Configuration

### Client Configuration

The `client_args` configure the underlying LiteLLM `completion` API. For a complete list of available arguments, please refer to the LiteLLM [docs](https://docs.litellm.ai/docs/completion/input).

### Model Configuration

The `model_config` configures the underlying model selected for inference. The supported configurations are:

|  Parameter | Description | Example | Options |
|------------|-------------|---------|---------|
| `model_id` | ID of a model to use | `anthropic/claude-3-7-sonnet-20250219` | [reference](https://docs.litellm.ai/docs/providers)
| `params` | Model specific parameters | `{"max_tokens": 1000, "temperature": 0.7}` | [reference](https://docs.litellm.ai/docs/completion/input)

## Troubleshooting

### Module Not Found

If you encounter the error `ModuleNotFoundError: No module named 'litellm'`, this means you haven't installed the `litellm` dependency in your environment. To fix, run `pip install 'strands-agents[litellm]'`.

## Advanced Features

### Caching

LiteLLM supports provider-agnostic caching through SystemContentBlock arrays, allowing you to define cache points that work across all supported model providers. This enables you to reuse parts of previous requests, which can significantly reduce token usage and latency.

#### System Prompt Caching

Use SystemContentBlock arrays to define cache points in your system prompts:

```python
from strands import Agent
from strands.models.litellm import LiteLLMModel
from strands.types.content import SystemContentBlock

# Define system content with cache points
system_content = [
    SystemContentBlock(
        text="You are a helpful assistant that provides concise answers. "
             "This is a long system prompt with detailed instructions..."
             "..." * 1000  # needs to be at least 1,024 tokens
    ),
    SystemContentBlock(cachePoint={"type": "default"})
]

# Create an agent with SystemContentBlock array
model = LiteLLMModel(
    model_id="bedrock/us.anthropic.claude-3-7-sonnet-20250219-v1:0"
)

agent = Agent(model=model, system_prompt=system_content)

# First request will cache the system prompt
response1 = agent("Tell me about Python")
# Cache metrics like cacheWriteInputTokens will be present in response1.metrics.accumulated_usage

# Second request will reuse the cached system prompt
response2 = agent("Tell me about JavaScript")
# Cache metrics like cacheReadInputTokens will be present in response2.metrics.accumulated_usage
```

> **Note**: Caching availability and behavior depends on the underlying model provider accessed through LiteLLM. Some providers may have minimum token requirements or other limitations for cache creation.

### Structured Output

LiteLLM supports structured output by proxying requests to underlying model providers that support tool calling. The availability of structured output depends on the specific model and provider you're using through LiteLLM.

```python
from pydantic import BaseModel, Field
from strands import Agent
from strands.models.litellm import LiteLLMModel

class BookAnalysis(BaseModel):
    """Analyze a book's key information."""
    title: str = Field(description="The book's title")
    author: str = Field(description="The book's author")
    genre: str = Field(description="Primary genre or category")
    summary: str = Field(description="Brief summary of the book")
    rating: int = Field(description="Rating from 1-10", ge=1, le=10)

model = LiteLLMModel(
    model_id="bedrock/us.anthropic.claude-3-7-sonnet-20250219-v1:0"
)

agent = Agent(model=model)

result = agent.structured_output(
    BookAnalysis,
    """
    Analyze this book: "The Hitchhiker's Guide to the Galaxy" by Douglas Adams.
    It's a science fiction comedy about Arthur Dent's adventures through space
    after Earth is destroyed. It's widely considered a classic of humorous sci-fi.
    """
)

print(f"Title: {result.title}")
print(f"Author: {result.author}")
print(f"Genre: {result.genre}")
print(f"Rating: {result.rating}")
```

## References

- [API](../../../api-reference/python/models/model.md)
- [LiteLLM](https://docs.litellm.ai/docs/)
