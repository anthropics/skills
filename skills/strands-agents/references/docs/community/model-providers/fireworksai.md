# FireworksAI

{{ community_contribution_banner }}

!!! info "Language Support"
    This provider is only supported in Python.

[Fireworks AI](https://fireworks.ai) provides blazing fast inference for open-source language models. Fireworks AI is accessible through OpenAI's SDK via full API compatibility, allowing easy and portable integration with the Strands Agents SDK using the familiar OpenAI interface.

## Installation

The Strands Agents SDK provides access to Fireworks AI models through the OpenAI compatibility layer, configured as an optional dependency. To install, run:

```bash
pip install 'strands-agents[openai]' strands-agents-tools
```

## Usage

After installing the `openai` package, you can import and initialize the Strands Agents' OpenAI-compatible provider for Fireworks AI models as follows:

```python
from strands import Agent
from strands.models.openai import OpenAIModel
from strands_tools import calculator

model = OpenAIModel(
    client_args={
        "api_key": "<FIREWORKS_API_KEY>",
        "base_url": "https://api.fireworks.ai/inference/v1",
    },
    model_id="accounts/fireworks/models/deepseek-v3p1-terminus",  # or see https://fireworks.ai/models
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

The `client_args` configure the underlying OpenAI-compatible client. When using Fireworks AI, you must set:

* `api_key`: Your Fireworks AI API key. Get one from the [Fireworks AI Console](https://app.fireworks.ai/settings/users/api-keys).
* `base_url`: `https://api.fireworks.ai/inference/v1`

Refer to [OpenAI Python SDK GitHub](https://github.com/openai/openai-python) for full client options.

### Model Configuration

The `model_config` specifies which Fireworks AI model to use and any additional parameters.

| Parameter  | Description               | Example                                                           | Options                                                            |
| ---------- | ------------------------- | ----------------------------------------------------------------- | ------------------------------------------------------------------ |
| `model_id` | Model name                | `accounts/fireworks/models/deepseek-v3p1-terminus`               | See [Fireworks Models](https://fireworks.ai/models)               |
| `params`   | Model-specific parameters | `{"max_tokens": 5000, "temperature": 0.7, "top_p": 0.9}`         | [API reference](https://docs.fireworks.ai/api-reference)          |

## Troubleshooting

### `ModuleNotFoundError: No module named 'openai'`

You must install the `openai` dependency to use this provider:

```bash
pip install 'strands-agents[openai]'
```

### Unexpected model behavior?

Ensure you're using a model ID compatible with Fireworks AI (e.g., `accounts/fireworks/models/deepseek-v3p1-terminus`, `accounts/fireworks/models/kimi-k2-instruct-0905`), and your `base_url` is set to `https://api.fireworks.ai/inference/v1`.

## References

* [Fireworks AI OpenAI Compatibility Guide](https://fireworks.ai/docs/tools-sdks/openai-compatibility#openai-compatibility)
* [Fireworks AI API Reference](https://docs.fireworks.ai/api-reference)
* [Fireworks AI Models](https://fireworks.ai/models)
* [OpenAI Python SDK](https://github.com/openai/openai-python)
* [Strands Agents API](../../api-reference/python/models/model.md)