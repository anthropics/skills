# Mistral AI

!!! info "Language Support"
    This provider is only supported in Python.

[Mistral AI](https://mistral.ai/)  is a research lab building the best open source models in the world.

Mistral AI offers both premier models and free models, driving innovation and convenience for the developer community. Mistral AI models are state-of-the-art for their multilingual, code generation, maths, and advanced reasoning capabilities.

## Installation

Mistral API is configured as an optional dependency in Strands Agents. To install, run:

```bash
pip install 'strands-agents[mistral]' strands-agents-tools
```

## Usage

After installing `mistral`, you can import and initialize Strands Agents' Mistral API provider as follows:

```python
from strands import Agent
from strands.models.mistral import MistralModel
from strands_tools import calculator

model = MistralModel(
    api_key="<YOUR_MISTRAL_API_KEY>",
    # **model_config
    model_id="mistral-large-latest",
)

agent = Agent(model=model, tools=[calculator])
response = agent("What is 2+2")
print(response)
```

## Configuration

### Client Configuration

The `client_args` configure the underlying Mistral client. You can pass additional arguments to customize the client behavior:

```python
model = MistralModel(
    api_key="<YOUR_MISTRAL_API_KEY>",
    client_args={
        "timeout": 30,
        # Additional client configuration options
    },
    model_id="mistral-large-latest"
)
```

For a complete list of available client arguments, please refer to the Mistral AI [documentation](https://docs.mistral.ai/).

### Model Configuration

The `model_config` configures the underlying model selected for inference. The supported configurations are:

| Parameter | Description | Example | Options |
|-----------|-------------|---------|---------|
| `model_id` | ID of a Mistral model to use | `mistral-large-latest` | [reference](https://docs.mistral.ai/getting-started/models/) |
| `max_tokens` | Maximum number of tokens to generate in the response | `1000` | Positive integer |
| `temperature` | Controls randomness in generation (0.0 to 1.0) | `0.7` | Float between 0.0 and 1.0 |
| `top_p` | Controls diversity via nucleus sampling | `0.9` | Float between 0.0 and 1.0 |
| `stream` | Whether to enable streaming responses | `true` | `true` or `false` |

## Environment Variables

You can set your Mistral API key as an environment variable instead of passing it directly:

```bash
export MISTRAL_API_KEY="your_api_key_here"
```

Then initialize the model without the API key parameter:

```python
model = MistralModel(model_id="mistral-large-latest")
```

## Troubleshooting

### Module Not Found

If you encounter the error `ModuleNotFoundError: No module named 'mistralai'`, this means you haven't installed the `mistral` dependency in your environment. To fix, run `pip install 'strands-agents[mistral]'`.

## References

- [API Reference](../../../api-reference/python/models/model.md)
- [Mistral AI Documentation](https://docs.mistral.ai/)