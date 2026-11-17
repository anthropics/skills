---
project:
  pypi: https://pypi.org/project/strands-xai/
  github: https://github.com/Cerrix/strands-xai
  maintainer: Cerrix
service:
  name: xAI
  link: https://x.ai/
---

# xAI

!!! info "Community Contribution"
    This is a community-maintained package that is not owned or supported by the Strands team. Validate and review 
    the package before using it in your project.

    Have your own integration? [We'd love to add it here too!](https://github.com/strands-agents/docs/issues/new?assignees=&labels=enhancement&projects=&template=content_addition.yml&title=%5BContent+Addition%5D%3A+)

!!! note "Language Support"
    This provider is only supported in Python.

[xAI](https://x.ai/) is an AI company that develops the Grok family of large language models with advanced reasoning capabilities. The [`strands-xai`](https://pypi.org/project/strands-xai/) package ([GitHub](https://github.com/Cerrix/strands-xai)) provides a community-maintained integration for the Strands Agents SDK, enabling seamless use of xAI's Grok models with powerful server-side tools including real-time X platform access, web search, and code execution.

## Installation

xAI integration is available as a separate community package:

```bash
pip install strands-agents strands-xai
```

## Usage

After installing `strands-xai`, you can import and initialize the xAI provider.

!!! note "API Key Required"
    Ensure `XAI_API_KEY` is set in your environment, or pass it via `client_args={"api_key": "your-key"}`.

```python
from strands import Agent
from strands_xai import xAIModel

model = xAIModel(
    client_args={"api_key": "xai-key"},  # or set XAI_API_KEY env var
    model_id="grok-4-1-fast-non-reasoning-latest",
)

agent = Agent(model=model)
response = agent("What's trending on X right now?")
print(response.message)
```

### With Strands Tools

You can use regular Strands tools just like with any other model provider:

```python
from strands import Agent, tool
from strands_xai import xAIModel

@tool
def calculate(expression: str) -> str:
    """Evaluate a mathematical expression."""
    try:
        result = eval(expression)
        return f"Result: {result}"
    except Exception as e:
        return f"Error: {e}"

@tool
def get_weather(city: str) -> str:
    """Get the current weather for a city."""
    return f"Weather in {city}: Sunny, 22°C"

model = xAIModel(
    client_args={"api_key": "xai-key"},
    model_id="grok-4-1-fast-non-reasoning-latest",
)

agent = Agent(model=model, tools=[calculate, get_weather])
response = agent("What's 15 * 7 and what's the weather in Paris?")
```

## Configuration

### Environment Variables

```bash
export XAI_API_KEY="your-api-key"
```

### Model Configuration

The supported configurations are:

| Parameter | Description | Example | Default |
|-----------|-------------|---------|---------|
| `model_id` | Grok model identifier | `grok-4-1-fast-reasoning-latest` | `grok-4-1-fast-non-reasoning-latest` |
| `client_args` | xAI client arguments | `{"api_key": "xai-key"}` | `{}` |
| `params` | Model parameters dict | `{"temperature": 0.7}` | `{}` |
| `xai_tools` | Server-side tools list | `[web_search(), x_search()]` | `[]` |
| `reasoning_effort` | Reasoning level (grok-3-mini only) | `"high"` | `None` |
| `use_encrypted_content` | Enable encrypted reasoning | `True` | `False` |
| `include` | Optional features | `["inline_citations"]` | `[]` |

**Model Parameters (in `params` dict):**
- `temperature` - Sampling temperature (0.0-2.0), default: varies by model
- `max_tokens` - Maximum tokens in response, default: 2048
- `top_p` - Nucleus sampling parameter (0.0-1.0), default: varies by model
- `frequency_penalty` - Frequency penalty (-2.0 to 2.0), default: 0
- `presence_penalty` - Presence penalty (-2.0 to 2.0), default: 0

**Available Models:**
- `grok-4-1-fast-reasoning` - Fast reasoning with encrypted thinking
- `grok-4-1-fast-non-reasoning` - Fast model without reasoning
- `grok-3-mini` - Compact model with visible reasoning  
- `grok-3-mini-non-reasoning` - Compact model without reasoning
- `grok-4-1-reasoning` - Full reasoning capabilities
- `grok-4-1-non-reasoning` - Full model without reasoning
- `grok-code-fast-1` - Code-optimized model

## Advanced Features

### Server-Side Tools

xAI models come with built-in server-side tools executed by xAI's infrastructure, providing unique capabilities:

```python
from strands_xai import xAIModel
from strands import Agent
from xai_sdk.tools import web_search, x_search, code_execution

# Server-side tools are automatically available
model = xAIModel(
    client_args={"api_key": "xai-key"},
    model_id="grok-4-1-fast-reasoning-latest",
    xai_tools=[web_search(), x_search(), code_execution()],
)

agent = Agent(model=model)
# Model can autonomously use web_search, x_search, and code_execution tools
response = agent("Search X for recent AI developments and analyze the sentiment")
```

**Built-in Server-Side Tools:**
- **X Search**: Real-time access to X platform posts, trends, and conversations
- **Web Search**: Live web search capabilities across diverse data sources
- **Code Execution**: Python code execution for data analysis and computation

### Real-Time X Platform Access

Grok has exclusive real-time access to X platform data:

```python
# Access real-time X data and trends
response = agent("What are people saying about the latest tech announcements on X?")

# Analyze trending topics
response = agent("Find trending hashtags related to AI and summarize the discussions")
```

### Hybrid Tool Usage

Combine xAI's server-side tools with your own Strands tools for maximum flexibility:

```python
from strands import Agent, tool
from strands_xai import xAIModel
from xai_sdk.tools import x_search

@tool
def calculate(expression: str) -> str:
    """Evaluate a mathematical expression."""
    try:
        result = eval(expression)
        return f"Result: {result}"
    except Exception as e:
        return f"Error: {e}"

@tool
def get_weather(city: str) -> str:
    """Get the current weather for a city."""
    return f"Weather in {city}: Sunny, 22°C"

model = xAIModel(
    client_args={"api_key": "xai-key"},
    model_id="grok-4-1-fast-reasoning-latest",
    xai_tools=[x_search()],  # Server-side X search
)

# Combine server-side and client-side tools
agent = Agent(model=model, tools=[calculate, get_weather])
response = agent("Search X for AI news, calculate 15*7, and tell me the weather in Tokyo")
```

This powerful combination allows the agent to:
- Search X platform in real-time (server-side)
- Perform calculations (client-side)
- Get weather information (client-side)
- All in a single conversation!

### Reasoning Models

Access models with visible reasoning capabilities:

```python
# Use reasoning model to see the thinking process
model = xAIModel(
    client_args={"api_key": "xai-key"},
    model_id="grok-3-mini",  # Shows reasoning steps
    reasoning_effort="high",
    params={"temperature": 0.3}
)

agent = Agent(model=model)
response = agent("Analyze the current AI market trends based on X discussions")
```

## References

- [strands-xai GitHub Repository](https://github.com/Cerrix/strands-xai)
- [xAI API Documentation](https://docs.x.ai/)
- [xAI Models and Pricing](https://docs.x.ai/docs/models)
