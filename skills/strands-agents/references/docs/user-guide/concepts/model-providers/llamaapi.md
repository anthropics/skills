# Llama API

!!! info "Language Support"
    This provider is only supported in Python.

[Llama API](https://llama.developer.meta.com?utm_source=partner-strandsagent&utm_medium=website) is a Meta-hosted API service that helps you integrate Llama models into your applications quickly and efficiently.

Llama API provides access to Llama models through a simple API interface, with inference provided by Meta, so you can focus on building AI-powered solutions without managing your own inference infrastructure.

With Llama API, you get access to state-of-the-art AI capabilities through a developer-friendly interface designed for simplicity and performance.

## Installation

Llama API is configured as an optional dependency in Strands Agents. To install, run:

```bash
pip install 'strands-agents[llamaapi]' strands-agents-tools
```

## Usage

After installing `llamaapi`, you can import and initialize Strands Agents' Llama API provider as follows:

```python
from strands import Agent
from strands.models.llamaapi import LlamaAPIModel
from strands_tools import calculator

model = LlamaAPIModel(
    client_args={
        "api_key": "<KEY>",
    },
    # **model_config
    model_id="Llama-4-Maverick-17B-128E-Instruct-FP8",
)

agent = Agent(model=model, tools=[calculator])
response = agent("What is 2+2")
print(response)
```

## Configuration

### Client Configuration

The `client_args` configure the underlying LlamaAPI client. For a complete list of available arguments, please refer to the LlamaAPI [docs](https://llama.developer.meta.com/docs/).


### Model Configuration

The `model_config` configures the underlying model selected for inference. The supported configurations are:

|  Parameter | Description                                                                                         | Example | Options |
|------------|-----------------------------------------------------------------------------------------------------|---------|---------|
| `model_id` | ID of a model to use                                                                                | `Llama-4-Maverick-17B-128E-Instruct-FP8` | [reference](https://llama.developer.meta.com/docs/)
| `repetition_penalty` | Controls the likelihood and generating repetitive responses. (minimum: 1, maximum: 2, default: 1)   |  `1`  | [reference](https://llama.developer.meta.com/docs/api/chat)
| `temperature` | Controls randomness of the response by setting a temperature.                                       | `0.7` | [reference](https://llama.developer.meta.com/docs/api/chat)
| `top_p` | Controls diversity of the response by setting a probability threshold when choosing the next token. | `0.9` | [reference](https://llama.developer.meta.com/docs/api/chat)
| `max_completion_tokens` | The maximum number of tokens to generate.                                                           | `4096` | [reference](https://llama.developer.meta.com/docs/api/chat)
| `top_k` | Only sample from the top K options for each subsequent token.                                       | `10` | [reference](https://llama.developer.meta.com/docs/api/chat)


## Troubleshooting

### Module Not Found

If you encounter the error `ModuleNotFoundError: No module named 'llamaapi'`, this means you haven't installed the `llamaapi` dependency in your environment. To fix, run `pip install 'strands-agents[llamaapi]'`.

## Advanced Features

### Structured Output

Llama API models support structured output through their tool calling capabilities. When you use [`Agent.structured_output()`](../../../api-reference/python/agent/agent.md#strands.agent.agent.Agent.structured_output), the Strands SDK converts your Pydantic models to tool specifications that Llama models can understand.

```python
from pydantic import BaseModel, Field
from strands import Agent
from strands.models.llamaapi import LlamaAPIModel

class BookAnalysis(BaseModel):
    """Analyze a book's key information."""
    title: str = Field(description="The book's title")
    author: str = Field(description="The book's author")
    genre: str = Field(description="Primary genre or category")
    summary: str = Field(description="Brief summary of the book")
    rating: int = Field(description="Rating from 1-10", ge=1, le=10)

model = LlamaAPIModel(
    client_args={"api_key": "<KEY>"},
    model_id="Llama-4-Maverick-17B-128E-Instruct-FP8",
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
- [LlamaAPI](https://llama.developer.meta.com/docs/)
