# Nebius Token Factory

{{ community_contribution_banner }}

!!! info "Language Support"
    This provider is only supported in Python.

[Nebius Token Factory](https://tokenfactory.nebius.com) provides fast inference for open-source language models. Nebius Token Factory is accessible through OpenAI's SDK via full API compatibility, allowing easy and portable integration with the Strands Agents SDK using the familiar OpenAI interface.

## Installation

The Strands Agents SDK provides access to Nebius Token Factory models through the OpenAI compatibility layer, configured as an optional dependency. To install, run:

```bash
pip install 'strands-agents[openai]' strands-agents-tools
```

## Usage

After installing the `openai` package, you can import and initialize the Strands Agents' OpenAI-compatible provider for Nebius Token Factory models as follows:

```python
from strands import Agent
from strands.models.openai import OpenAIModel
from strands_tools import calculator

model = OpenAIModel(
    client_args={
        "api_key": "<NEBIUS_API_KEY>",
        "base_url": "https://api.tokenfactory.nebius.com/v1/",
    },
    model_id="deepseek-ai/DeepSeek-R1-0528",  # or see https://docs.tokenfactory.nebius.com/ai-models-inference/overview
    params={
        "max_tokens": 5000,
        "temperature": 0.1
    }
)

agent = Agent(model=model, tools=[calculator])
agent("What is 2+2?")
```

## Configuration

### Client Configuration

The `client_args` configure the underlying OpenAI-compatible client. When using Nebius Token Factory, you must set:

* `api_key`: Your Nebius Token Factory API key. Get one from the [Nebius Token Factory Console](https://tokenfactory.nebius.com/).
* `base_url`: `https://api.tokenfactory.nebius.com/v1/`

Refer to [OpenAI Python SDK GitHub](https://github.com/openai/openai-python) for full client options.

### Model Configuration

The `model_config` specifies which Nebius Token Factory model to use and any additional parameters.

| Parameter  | Description               | Example                                                           | Options                                                            |
| ---------- | ------------------------- | ----------------------------------------------------------------- | ------------------------------------------------------------------ |
| `model_id` | Model name                | `deepseek-ai/DeepSeek-R1-0528`                                   | See [Nebius Token Factory Models](https://nebius.com/services/token-factory) |
| `params`   | Model-specific parameters | `{"max_tokens": 5000, "temperature": 0.7, "top_p": 0.9}`         | [API reference](https://docs.tokenfactory.nebius.com/api-reference)          |

## Troubleshooting

### `ModuleNotFoundError: No module named 'openai'`

You must install the `openai` dependency to use this provider:

```bash
pip install 'strands-agents[openai]'
```

### Unexpected model behavior?

Ensure you're using a model ID compatible with Nebius Token Factory (e.g., `deepseek-ai/DeepSeek-R1-0528`, `meta-llama/Meta-Llama-3.1-70B-Instruct`), and your `base_url` is set to `https://api.tokenfactory.nebius.com/v1/`.

## References

* [Nebius Token Factory Documentation](https://docs.tokenfactory.nebius.com/)
* [Nebius Token Factory API Reference](https://docs.tokenfactory.nebius.com/api-reference)
* [Nebius Token Factory Models](https://docs.tokenfactory.nebius.com/ai-models-inference/overview)
* [OpenAI Python SDK](https://github.com/openai/openai-python)
* [Strands Agents API](../../api-reference/python/models/model.md)

