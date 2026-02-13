# Writer

!!! info "Language Support"
    This provider is only supported in Python.

[Writer](https://writer.com/) is an enterprise generative AI platform offering specialized Palmyra models for finance, healthcare, creative, and general-purpose use cases. The models excel at tool calling, structured outputs, and domain-specific tasks, with Palmyra X5 supporting a 1M token context window.

## Installation

Writer is configured as an optional dependency in Strands Agents. To install, run:

```bash
pip install 'strands-agents[writer]' strands-agents-tools
```

## Usage

After installing `writer`, you can import and initialize Strands Agents' Writer provider as follows:

```python
from strands import Agent
from strands.models.writer import WriterModel
from strands_tools import calculator

model = WriterModel(
    client_args={"api_key": "<WRITER_API_KEY>"},
    # **model_config
    model_id="palmyra-x5",
)

agent = Agent(model=model, tools=[calculator])
response = agent("What is 2+2")
print(response)
```

> **Note**: By default, Strands Agents use a `PrintingCallbackHandler` that streams responses to stdout as they're generated. When you call `agent("What is 2+2")`, you'll see the response appear in real-time as it's being generated. The `print(response)` above also shows the final collected result after the response is complete. See [Callback Handlers](../streaming/callback-handlers.md) for more details.

## Configuration

### Client Configuration

The `client_args` configure the underlying Writer client. You can pass additional arguments to customize the client behavior:

```python
model = WriterModel(
    client_args={
        "api_key": "<WRITER_API_KEY>",
        "timeout": 30,
        "base_url": "https://api.writer.com/v1",
        # Additional client configuration options
    },
    model_id="palmyra-x5"
)
```

### Model Configuration

The `WriterModel` accepts configuration parameters as keyword arguments to the model constructor:

| Parameter | Type | Description | Default | Options |
|-----------|------|-------------|---------|---------|
| `model_id` | `str` | Model name to use (e.g. `palmyra-x5`, `palmyra-x4`, etc.) | Required | [reference](https://dev.writer.com/home/models) |
| `max_tokens` | `Optional[int]` | Maximum number of tokens to generate | See the Context Window for [each available model](#available-models) | [reference](https://dev.writer.com/api-reference/completion-api/chat-completion#body-max- tokens) |
| `stop` | `Optional[Union[str, List[str]]]` | A token or sequence of tokens that, when generated, will cause the model to stop producing further content. This can be a single token or an array of tokens, acting as a signal to end the output. | `None` | [reference](https://dev.writer.com/api-reference/completion-api/chat-completion#body-stop) |
| `stream_options` | `Dict[str, Any]` | Additional options for streaming. Specify `include_usage` to include usage information in the response, in the `accumulated_usage` field. If you do not specify this, `accumulated_usage` will show `0` for each value. | `None` | [reference](https://dev.writer.com/api-reference/completion-api/chat-completion#body-stream) |
| `temperature` | `Optional[float]` | What sampling temperature to use (0.0 to 2.0). A higher temperature will produce more random output. | `1` | [reference](https://dev.writer.com/api-reference/completion-api/chat-completion#body-temperature) |
| `top_p` | `Optional[float]` | Threshold for "nucleus sampling" | `None` | [reference](https://dev.writer.com/api-reference/completion-api/chat-completion#body-top_p) |

### Available Models

Writer offers several specialized Palmyra models:

| Model | Model ID | Context Window | Description |
|-------|----------|----------------|-------------|
| Palmyra X5 | `palmyra-x5` | 1M tokens | Latest model with 1 million token context for complex workflows, supports vision and multi-content |
| Palmyra X4 | `palmyra-x4` | 128k tokens | Advanced model for workflow automation and tool calling |
| Palmyra Fin | `palmyra-fin` | 128k tokens | Finance-specialized model (first to pass CFA exam) |
| Palmyra Med | `palmyra-med` | 32k tokens | Healthcare-specialized model for medical analysis |
| Palmyra Creative | `palmyra-creative` | 128k tokens | Creative writing and brainstorming model |

See the [Writer API documentation](https://dev.writer.com/home/models) for more details on the available models and use cases for each.

## Environment Variables

You can set your Writer API key as an environment variable instead of passing it directly:

```bash
export WRITER_API_KEY="your_api_key_here"
```

Then initialize the model without the `client_args["api_key"]` parameter:

```python
model = WriterModel(model_id="palmyra-x5")
```

## Examples

### Enterprise workflow automation

```python
from strands import Agent
from strands.models.writer import WriterModel
from my_tools import web_search, email_sender  # Custom tools from your local module

# Use Palmyra X5 for tool calling and workflow automation
model = WriterModel(
    client_args={"api_key": "<WRITER_API_KEY>"},
    model_id="palmyra-x5",
)

agent = Agent(
    model=model, 
    tools=[web_search, email_sender],  # Custom tools that you would define
    system_prompt="You are an enterprise assistant that helps automate business workflows."
)

response = agent("Research our competitor's latest product launch and draft a summary email for the leadership team")
```

> **Note**: The `web_search` and `email_sender` tools in this example are custom tools that you would need to define. See [Python Tools](../tools/custom-tools.md) for guidance on creating custom tools, or use existing tools from the [strands_tools package](../tools/community-tools-package.md).

### Financial analysis with Palmyra Fin

```python
from strands import Agent
from strands.models.writer import WriterModel

# Use specialized finance model for financial analysis
model = WriterModel(
    client_args={"api_key": "<WRITER_API_KEY>"},
    model_id="palmyra-fin"
)

agent = Agent(
    model=model,
    system_prompt="You are a financial analyst assistant. Provide accurate, data-driven analysis."
)

# Replace the placeholder with your actual financial report content
actual_report = """
[Your quarterly earnings report content would go here - this could include:
- Revenue figures
- Profit margins
- Growth metrics
- Risk factors
- Market analysis
- Any other financial data you want analyzed]
"""

response = agent(f"Analyze the key financial risks in this quarterly earnings report: {actual_report}")
```
### Long-context document processing

```python
from strands import Agent
from strands.models.writer import WriterModel

# Use Palmyra X5 for processing very long documents
model = WriterModel(
    client_args={"api_key": "<WRITER_API_KEY>"},
    model_id="palmyra-x5",
    temperature=0.2
)

agent = Agent(
    model=model,
    system_prompt="You are a document analysis assistant that can process and summarize lengthy documents."
)

# Can handle documents up to 1M tokens
# Replace the placeholder with your actual document content
actual_transcripts = """
[Meeting transcript content would go here - this could be thousands of lines of text
from meeting recordings, documents, or other long-form content that you want to analyze]
"""

response = agent(f"Summarize the key decisions and action items from these meeting transcripts: {actual_transcripts}")
```

### Structured Output Generation

Palmyra X5 and X4 support structured output generation using [Pydantic models](https://docs.pydantic.dev/latest/). This is useful for ensuring consistent, validated responses. The example below shows how to use structured output generation with Palmyra X5 to generate a marketing campaign.

> **Note**: Structured output disables streaming and returns the complete response at once, unlike regular chat completions, which stream by default. See [Callback Handlers](../streaming/callback-handlers.md) for more details.

```python
from strands import Agent
from strands.models.writer import WriterModel
from pydantic import BaseModel
from typing import List

# Define a structured schema for creative content
class MarketingCampaign(BaseModel):
    campaign_name: str
    target_audience: str
    key_messages: List[str]
    call_to_action: str
    tone: str
    estimated_engagement: float

# Use Palmyra X5 for creative marketing content
model = WriterModel(
    client_args={"api_key": "<WRITER_API_KEY>"},
    model_id="palmyra-x5",
    temperature=0.8  # Higher temperature for creative output
)

agent = Agent(
    model=model,
    system_prompt="You are a creative marketing strategist. Generate innovative marketing campaigns with structured data."
)

# Generate structured marketing campaign
response = agent.structured_output(
    output_model=MarketingCampaign,
    prompt="Create a marketing campaign for a new eco-friendly water bottle targeting young professionals aged 25-35."
)

print(f"Campaign Name: {response.campaign_name}\nTarget Audience: {response.target_audience}\nKey Messages: {response.key_messages}\nCall to Action: {response.call_to_action}\nTone: {response.tone}\nEstimated Engagement: {response.estimated_engagement}")
```

### Vision and Image Analysis

Palmyra X5 supports vision capabilities, allowing you to analyze images and extract information from visual content. This is useful for tasks like image description, content analysis, and visual data extraction. When using vision capabilities, provide the image data in bytes format.

```python
from strands import Agent
from strands.models.writer import WriterModel

# Use Palmyra X5 for vision tasks
model = WriterModel(
    client_args={"api_key": "<WRITER_API_KEY>"},
    model_id="palmyra-x5"
)

agent = Agent(
    model=model,
    system_prompt="You are a visual analysis assistant. Provide detailed, accurate descriptions of images and extract relevant information."
)

# Read the image file
with open("path/to/image.png", "rb") as image_file:
    image_data = image_file.read()

messages = [
    {
        "role": "user",
        "content": [
            {
                "image": {
                    "format": "png",
                    "source": {
                        "bytes": image_data
                    }
                }
            },
            {
                "text": "Analyze this image and describe what you see. What are the key elements, colors, and any text or objects visible?"
            }
        ]
    }
]

# Create an agent with the image message
vision_agent = Agent(model=model, messages=messages)

# Analyze the image
response = vision_agent("What are the main features of this image and what might it be used for?")

print(response)
```

## Troubleshooting

### Module Not Found

If you encounter the error `ModuleNotFoundError: No module named 'writer'`, this means you haven't installed the `writer` dependency in your environment. To fix, run `pip install 'strands-agents[writer]'`.

### Authentication Errors

Ensure your Writer API key is valid and has the necessary permissions. You can get an API key from the [Writer AI Studio](https://app.writer.com/aistudio) dashboard. Learn more about [Writer API Keys](https://dev.writer.com/api-reference/api-keys).

## References

- [API Reference](../../../api-reference/python/models/model.md)
- [Writer Documentation](https://dev.writer.com/)
- [Writer Models Guide](https://dev.writer.com/home/models)
- [Writer API Reference](https://dev.writer.com/api-reference)

