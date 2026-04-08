# NVIDIA NIM

{{ community_contribution_banner }}

!!! info "Language Support"
    This provider is only supported in Python.

[strands-nvidia-nim](https://github.com/thiago4go/strands-nvidia-nim) is a custom model provider that enables Strands Agents to work with [Nvidia NIM](https://www.nvidia.com/en-us/ai/) APIs. It bridges the message format compatibility gap between Strands Agents SDK and Nvidia NIM API endpoints.

**Features:**

- **Message Format Conversion**: Automatically converts Strands' structured content to simple string format required by Nvidia NIM
- **Tool Support**: Full support for Strands tools with proper error handling
- **Clean Streaming**: Proper streaming output without artifacts
- **Error Handling**: Context window overflow detection and Strands-specific errors

## Installation

Install strands-nvidia-nim from PyPI:

```bash
pip install strands-nvidia-nim strands-agents-tools
```

## Usage

### Basic Agent

```python
from strands import Agent
from strands_tools import calculator
from strands_nvidia_nim import NvidiaNIM

model = NvidiaNIM(
    api_key="your-nvidia-nim-api-key",
    model_id="meta/llama-3.1-70b-instruct",
    params={
        "max_tokens": 1000,
        "temperature": 0.7,
    }
)

agent = Agent(model=model, tools=[calculator])
agent("What is 123.456 * 789.012?")
```

### Using Environment Variables

```bash
export NVIDIA_NIM_API_KEY=your-nvidia-nim-api-key
```

```python
import os
from strands import Agent
from strands_tools import calculator
from strands_nvidia_nim import NvidiaNIM

model = NvidiaNIM(
    api_key=os.getenv("NVIDIA_NIM_API_KEY"),
    model_id="meta/llama-3.1-70b-instruct",
    params={"max_tokens": 1000, "temperature": 0.7}
)

agent = Agent(model=model, tools=[calculator])
agent("What is 123.456 * 789.012?")
```

## Configuration

### Model Configuration

The `NvidiaNIM` provider accepts the following parameters:

| Parameter | Description | Example |
| --------- | ----------- | ------- |
| `api_key` | Your Nvidia NIM API key | `"nvapi-..."` |
| `model_id` | Model identifier | `"meta/llama-3.1-70b-instruct"` |
| `params` | Generation parameters | `{"max_tokens": 1000}` |

### Available Models

Popular Nvidia NIM models:

- `meta/llama-3.1-70b-instruct` - High quality, larger model
- `meta/llama-3.1-8b-instruct` - Faster, smaller model
- `meta/llama-3.3-70b-instruct` - Latest Llama model
- `mistralai/mistral-large` - Mistral's flagship model
- `nvidia/llama-3.1-nemotron-70b-instruct` - Nvidia-optimized variant

### Generation Parameters

```python
model = NvidiaNIM(
    api_key="your-api-key",
    model_id="meta/llama-3.1-70b-instruct",
    params={
        "max_tokens": 1500,
        "temperature": 0.7,
        "top_p": 0.9,
        "frequency_penalty": 0.0,
        "presence_penalty": 0.0
    }
)
```

## Troubleshooting

### `BadRequestError` with message formatting

This provider exists specifically to solve message formatting issues between Strands and Nvidia NIM. If you encounter this error using standard LiteLLM integration, switch to `strands-nvidia-nim`.

### Context window overflow

The provider includes detection for context window overflow errors. If you encounter this, try reducing `max_tokens` or the size of your prompts.

## References

* [strands-nvidia-nim Repository](https://github.com/thiago4go/strands-nvidia-nim)
* [PyPI Package](https://pypi.org/project/strands-nvidia-nim/)
* [Nvidia NIM Documentation](https://docs.nvidia.com/nim/)
* [Strands Custom Model Provider](../../user-guide/concepts/model-providers/custom_model_provider.md)
