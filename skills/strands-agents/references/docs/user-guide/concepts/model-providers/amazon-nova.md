# Amazon Nova

!!! info "Language Support"
    This provider is only supported in Python.

[Amazon Nova](https://nova.amazon.com/) is a new generation of foundation models with frontier intelligence and industry leading price performance. Generate text, code, and images with natural language prompts. The [`strands-amazon-nova`](https://pypi.org/project/strands-amazon-nova/) package ([GitHub](https://github.com/amazon-nova-api/strands-nova)) provides an integration for the Strands Agents SDK, enabling seamless use of Amazon Nova models.

## Installation

Amazon Nova integration is available as a separate package:

```bash
pip install strands-agents strands-amazon-nova
```

## Usage

After installing `strands-amazon-nova`, you can import and initialize the Amazon Nova API provider:

```python
from strands import Agent
from strands_amazon_nova import NovaAPIModel

model = NovaAPIModel(
    api_key=os.env(NOVA_API_KEY"),  # or set NOVA_API_KEY env var
    model_id="nova-2-lite-v1",
    params={
      "max_tokens": 1000,
      "temperature": 0.7,
    }
)

agent = Agent(model=model)
response = await agent.invoke_async("Can you write a short story?")
print(response.message)
```

## Configuration

### Environment Variables

```bash
export NOVA_API_KEY="your-api-key"
```

### Model Configuration

```python
from strands_amazon_nova import NovaAPIModel

model = NovaAPIModel(
    api_key=os.env(NOVA_API_KEY"),          # Required: Nova API key
    model_id="nova-2-lite-v1",              # Required: Model ID
    base_url="https://api.nova.amazon.com/v1",  # Optional, default shown
    timeout=300.0,                       # Optional, request timeout in seconds
    params={                             # Optional: Model parameters
        "max_tokens": 4096,              # Maximum tokens to generate
        "max_completion_tokens": 4096,   # Alternative to max_tokens
        "temperature": 0.7,              # Sampling temperature (0.0-1.0)
        "top_p": 0.9,                    # Nucleus sampling (0.0-1.0)
        "reasoning_effort": "medium",    # For reasoning models: "low", "medium", "high"
        "system_tools": ["nova_grounding", "nova_code_interpreter"] # Available system tools from Nova API
        "metadata": {},                  # Additional metadata
    }
)
```

**Supported Parameters in `params`:**

- `max_tokens` (int): Maximum tokens to generate (deprecated, use max_completion_tokens)
- `max_completion_tokens` (int): Maximum tokens to generate
- `temperature` (float): Controls randomness (0.0 = deterministic, 1.0 = maximum randomness)
- `top_p` (float): Nucleus sampling threshold
- `reasoning_effort` (str): For reasoning models - "low", "medium", or "high"
- `system_tools` (list): Available system tools from the Nova API - currently `nova_grounding` and `nova_code_interpreter`
- `metadata` (dict): Additional request metadata

## References

- [strands-amazon-nova GitHub Repository](https://github.com/amazon-nova-api/strands-nova)
- [Amazon Nova](https://nova.amazon.com/)
- **Issues**: Report bugs and feature requests in the [strands-amazon-nova repository](https://github.com/amazon-nova-api/strands-nova/issues/new/choose)
