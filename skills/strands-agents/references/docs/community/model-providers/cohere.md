# Cohere

{{ community_contribution_banner }}

!!! info "Language Support"
    This provider is only supported in Python.

[Cohere](https://cohere.com) provides cutting-edge language models. These are accessible through OpenAI's SDK via the Compatibility API. This allows easy and portable integration with the Strands Agents SDK using the familiar OpenAI interface.

## Installation

The Strands Agents SDK provides access to Cohere models through the OpenAI compatibility layer, configured as an optional dependency. To install, run:

```bash
pip install 'strands-agents[openai]' strands-agents-tools
```

## Usage

After installing the `openai` package, you can import and initialize the Strands Agents' OpenAI-compatible provider for Cohere models as follows:

```python
from strands import Agent
from strands.models.openai import OpenAIModel
from strands_tools import calculator

model = OpenAIModel(
    client_args={
        "api_key": "<COHERE_API_KEY>",
        "base_url": "https://api.cohere.ai/compatibility/v1",  # Cohere compatibility endpoint
    },
    model_id="command-a-03-2025",  # or see https://docs.cohere.com/docs/models
    params={
        "stream_options": None
    }
)

agent = Agent(model=model, tools=[calculator])
agent("What is 2+2?")
```

## Configuration

### Client Configuration

The `client_args` configure the underlying OpenAI-compatible client. When using Cohere, you must set:

* `api_key`: Your Cohere API key. Get one from the [Cohere Dashboard](https://dashboard.cohere.com).
* `base_url`:
    * `https://api.cohere.ai/compatibility/v1`

Refer to [OpenAI Python SDK GitHub](https://github.com/openai/openai-python) for full client options.

### Model Configuration

The `model_config` specifies which Cohere model to use and any additional parameters.

| Parameter  | Description               | Example                                    | Options                                                            |
| ---------- | ------------------------- | ------------------------------------------ | ------------------------------------------------------------------ |
| `model_id` | Model name                | `command-r-plus`                           | See [Cohere docs](https://docs.cohere.com/docs/models)             |
| `params`   | Model-specific parameters | `{"max_tokens": 1000, "temperature": 0.7}` | [API reference](https://docs.cohere.com/docs/compatibility-api) |

## Troubleshooting

### `ModuleNotFoundError: No module named 'openai'`

You must install the `openai` dependency to use this provider:

```bash
pip install 'strands-agents[openai]'
```

### Unexpected model behavior?

Ensure you're using a model ID compatible with Cohere’s Compatibility API (e.g., `command-r-plus`, `command-a-03-2025`, `embed-v4.0`), and your `base_url` is set to `https://api.cohere.ai/compatibility/v1`.

## References

* [Cohere Docs: Using the OpenAI SDK](https://docs.cohere.com/docs/compatibility-api)
* [Cohere API Reference](https://docs.cohere.com/reference)
* [OpenAI Python SDK](https://github.com/openai/openai-python)
