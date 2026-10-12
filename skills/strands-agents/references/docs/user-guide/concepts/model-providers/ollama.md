# Ollama

!!! info "Language Support"
    This provider is only supported in Python.

Ollama is a framework for running open-source large language models locally. Strands provides native support for Ollama, allowing you to use locally-hosted models in your agents.

The [`OllamaModel`](../../../api-reference/python/models/ollama.md#strands.models.ollama) class in Strands enables seamless integration with Ollama's API, supporting:

- Text generation
- Image understanding
- Tool/function calling
- Streaming responses
- Configuration management

## Getting Started

### Prerequisites

First install the python client into your python environment:
```bash
pip install 'strands-agents[ollama]' strands-agents-tools
```

Next, you'll need to install and setup ollama itself.

#### Option 1: Native Installation

1. Install Ollama by following the instructions at [ollama.ai](https://ollama.ai)
2. Pull your desired model:
   ```bash
   ollama pull llama3.1
   ```
3. Start the Ollama server:
   ```bash
   ollama serve
   ```

#### Option 2: Docker Installation

1. Pull the Ollama Docker image:
   ```bash
   docker pull ollama/ollama
   ```

2. Run the Ollama container:
   ```bash
   docker run -d -v ollama:/root/.ollama -p 11434:11434 --name ollama ollama/ollama
   ```

   > Note: Add `--gpus=all` if you have a GPU and if Docker GPU support is configured.

3. Pull a model using the Docker container:
   ```bash
   docker exec -it ollama ollama pull llama3.1
   ```

4. Verify the Ollama server is running:
   ```bash
   curl http://localhost:11434/api/tags
   ```

## Basic Usage

Here's how to create an agent using an Ollama model:

```python
from strands import Agent
from strands.models.ollama import OllamaModel

# Create an Ollama model instance
ollama_model = OllamaModel(
    host="http://localhost:11434",  # Ollama server address
    model_id="llama3.1"               # Specify which model to use
)

# Create an agent using the Ollama model
agent = Agent(model=ollama_model)

# Use the agent
agent("Tell me about Strands agents.") # Prints model output to stdout by default
```

## Configuration Options

The [`OllamaModel`](../../../api-reference/python/models/ollama.md#strands.models.ollama) supports various [configuration parameters](../../../api-reference/python/models/ollama.md#strands.models.ollama.OllamaModel.OllamaConfig):

| Parameter | Description | Default |
|-----------|-------------|---------|
| `host` | The address of the Ollama server | Required |
| `model_id` | The Ollama model identifier | Required |
| `keep_alive` | How long the model stays loaded in memory | "5m" |
| `max_tokens` | Maximum number of tokens to generate | None |
| `temperature` | Controls randomness (higher = more random) | None |
| `top_p` | Controls diversity via nucleus sampling | None |
| `stop_sequences` | List of sequences that stop generation | None |
| `options` | Additional model parameters (e.g., top_k) | None |
| `additional_args` | Any additional arguments for the request | None |

### Example with Configuration

```python
from strands import Agent
from strands.models.ollama import OllamaModel

# Create a configured Ollama model
ollama_model = OllamaModel(
    host="http://localhost:11434",
    model_id="llama3.1",
    temperature=0.7,
    keep_alive="10m",
    stop_sequences=["###", "END"],
    options={"top_k": 40}
)

# Create an agent with the configured model
agent = Agent(model=ollama_model)

# Use the agent
response = agent("Write a short story about an AI assistant.")
```

## Advanced Features

### Updating Configuration at Runtime

You can update the model configuration during runtime:

```python
# Create the model with initial configuration
ollama_model = OllamaModel(
    host="http://localhost:11434",
    model_id="llama3.1",
    temperature=0.7
)

# Update configuration later
ollama_model.update_config(
    temperature=0.9,
    top_p=0.8
)
```

This is especially useful if you want a tool to update the model's config for you:

```python
@tool
def update_model_id(model_id: str, agent: Agent) -> str:
    """
    Update the model id of the agent

    Args:
      model_id: Ollama model id to use.
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

### Using Different Models

Ollama supports many different models. You can switch between them (make sure they are pulled first). See the list of
available models here: https://ollama.com/search

```python
# Create models for different use cases
creative_model = OllamaModel(
    host="http://localhost:11434",
    model_id="llama3.1",
    temperature=0.8
)

factual_model = OllamaModel(
    host="http://localhost:11434",
    model_id="mistral",
    temperature=0.2
)

# Create agents with different models
creative_agent = Agent(model=creative_model)
factual_agent = Agent(model=factual_model)
```

### Structured Output

Ollama supports structured output for models that have tool calling capabilities. When you use [`Agent.structured_output()`](../../../api-reference/python/agent/agent.md#strands.agent.agent.Agent.structured_output), the Strands SDK converts your Pydantic models to tool specifications that compatible Ollama models can understand.

```python
from pydantic import BaseModel, Field
from strands import Agent
from strands.models.ollama import OllamaModel

class BookAnalysis(BaseModel):
    """Analyze a book's key information."""
    title: str = Field(description="The book's title")
    author: str = Field(description="The book's author")
    genre: str = Field(description="Primary genre or category")
    summary: str = Field(description="Brief summary of the book")
    rating: int = Field(description="Rating from 1-10", ge=1, le=10)

ollama_model = OllamaModel(
    host="http://localhost:11434",
    model_id="llama3.1",
)

agent = Agent(model=ollama_model)

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

## Tool Support

[Ollama models that support tool use](https://ollama.com/search?c=tools) can use tools through Strands' tool system:

```python
from strands import Agent
from strands.models.ollama import OllamaModel
from strands_tools import calculator, current_time

# Create an Ollama model
ollama_model = OllamaModel(
    host="http://localhost:11434",
    model_id="llama3.1"
)

# Create an agent with tools
agent = Agent(
    model=ollama_model,
    tools=[calculator, current_time]
)

# Use the agent with tools
response = agent("What's the square root of 144 plus the current time?")
```

## Troubleshooting

### Common Issues

1. **Connection Refused**:
    - Ensure the Ollama server is running (`ollama serve` or check Docker container status)
    - Verify the host URL is correct
    - For Docker: Check if port 11434 is properly exposed

2. **Model Not Found**:
    - Pull the model first: `ollama pull model_name` or `docker exec -it ollama ollama pull model_name`
    - Check for typos in the model_id

3. **Module Not Found**:
    - If you encounter the error `ModuleNotFoundError: No module named 'ollama'`, this means you haven't installed the `ollama` dependency in your python environment
    - To fix, run `pip install 'strands-agents[ollama]'`

## Related Resources

- [Ollama Documentation](https://github.com/ollama/ollama/blob/main/README.md)
- [Ollama Docker Hub](https://hub.docker.com/r/ollama/ollama)
- [Available Ollama Models](https://ollama.ai/library)
