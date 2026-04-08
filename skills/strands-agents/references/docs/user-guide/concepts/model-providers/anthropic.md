# Anthropic

!!! info "Language Support"
    This provider is only supported in Python.

[Anthropic](https://docs.anthropic.com/en/home) is an AI safety and research company focused on building reliable, interpretable, and steerable AI systems. Included in their offerings is the Claude AI family of models, which are known for their conversational abilities, careful reasoning, and capacity to follow complex instructions. The Strands Agents SDK implements an Anthropic provider, allowing users to run agents against Claude models directly.

## Installation

Anthropic is configured as an optional dependency in Strands. To install, run:

```bash
pip install 'strands-agents[anthropic]' strands-agents-tools
```

## Usage

After installing `anthropic`, you can import and initialize Strands' Anthropic provider as follows:

```python
from strands import Agent
from strands.models.anthropic import AnthropicModel
from strands_tools import calculator

model = AnthropicModel(
    client_args={
        "api_key": "<KEY>",
    },
    # **model_config
    max_tokens=1028,
    model_id="claude-sonnet-4-20250514",
    params={
        "temperature": 0.7,
    }
)

agent = Agent(model=model, tools=[calculator])
response = agent("What is 2+2")
print(response)
```

## Configuration

### Client Configuration

The `client_args` configure the underlying Anthropic client. For a complete list of available arguments, please refer to the Anthropic [docs](https://docs.anthropic.com/en/api/client-sdks).

### Model Configuration

The `model_config` configures the underlying model selected for inference. The supported configurations are:

|  Parameter | Description | Example | Options |
|------------|-------------|---------|---------|
| `max_tokens` | Maximum number of tokens to generate before stopping | `1028` | [reference](https://docs.anthropic.com/en/api/messages#body-max-tokens)
| `model_id` | ID of a model to use | `claude-sonnet-4-20250514` | [reference](https://docs.anthropic.com/en/api/messages#body-model)
| `params` | Model specific parameters | `{"max_tokens": 1000, "temperature": 0.7}` | [reference](https://docs.anthropic.com/en/api/messages)

## Troubleshooting

### Module Not Found

If you encounter the error `ModuleNotFoundError: No module named 'anthropic'`, this means you haven't installed the `anthropic` dependency in your environment. To fix, run `pip install 'strands-agents[anthropic]'`.

## Advanced Features

### Structured Output

Anthropic's Claude models support structured output through their tool calling capabilities. When you use [`Agent.structured_output()`](../../../api-reference/python/agent/agent.md#strands.agent.agent.Agent.structured_output), the Strands SDK converts your Pydantic models to Anthropic's tool specification format.

```python
from pydantic import BaseModel, Field
from strands import Agent
from strands.models.anthropic import AnthropicModel

class BookAnalysis(BaseModel):
    """Analyze a book's key information."""
    title: str = Field(description="The book's title")
    author: str = Field(description="The book's author")
    genre: str = Field(description="Primary genre or category")
    summary: str = Field(description="Brief summary of the book")
    rating: int = Field(description="Rating from 1-10", ge=1, le=10)

model = AnthropicModel(
    client_args={
        "api_key": "<KEY>",
    },
    max_tokens=1028,
    model_id="claude-sonnet-4-20250514",
    params={
        "temperature": 0.7,
    }
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
- [Anthropic](https://docs.anthropic.com/en/home)

