# llama.cpp

!!! info "Language Support"
    This provider is only supported in Python.

[llama.cpp](https://github.com/ggml-org/llama.cpp) is a high-performance C++ inference engine for running large language models locally. The Strands Agents SDK implements a llama.cpp provider, allowing you to run agents against any llama.cpp server with quantized models.

## Installation

llama.cpp support is included in the base Strands Agents package. To install, run:

```bash
pip install strands-agents strands-agents-tools
```

## Usage

After setting up a llama.cpp server, you can import and initialize the Strands Agents' llama.cpp provider as follows:

```python
from strands import Agent
from strands.models.llamacpp import LlamaCppModel
from strands_tools import calculator

model = LlamaCppModel(
    base_url="http://localhost:8080",
    # **model_config
    model_id="default",
    params={
        "max_tokens": 1000,
        "temperature": 0.7,
        "repeat_penalty": 1.1,
    }
)

agent = Agent(model=model, tools=[calculator])
response = agent("What is 2+2")
print(response)
```

To connect to a remote llama.cpp server, you can specify a different base URL:

```python
model = LlamaCppModel(
    base_url="http://your-server:8080",
    model_id="default",
    params={
        "temperature": 0.7,
        "cache_prompt": True
    }
)
```

## Configuration

### Server Setup

Before using LlamaCppModel, you need a running llama.cpp server with a GGUF model:

```bash
# Download a model (e.g., using Hugging Face CLI)
hf download ggml-org/Qwen3-4B-GGUF Qwen3-4B-Q4_K_M.gguf --local-dir ./models

# Start the server
llama-server -m models/Qwen3-4B-Q4_K_M.gguf --host 0.0.0.0 --port 8080 -c 8192 --jinja
```

### Model Configuration

The `model_config` configures the underlying model selected for inference. The supported configurations are:

| Parameter | Description | Example | Default |
|-----------|-------------|---------|---------|
| `base_url` | llama.cpp server URL | `http://localhost:8080` | `http://localhost:8080` |
| `model_id` | Model identifier | `default` | `default` |
| `params` | Model parameters | `{"temperature": 0.7, "max_tokens": 1000}` | `None` |

### Supported Parameters

Standard parameters:

- `temperature`, `max_tokens`, `top_p`, `frequency_penalty`, `presence_penalty`, `stop`, `seed`

llama.cpp-specific parameters:

- `repeat_penalty`, `top_k`, `min_p`, `typical_p`, `tfs_z`, `mirostat`, `grammar`, `json_schema`, `cache_prompt`

## Troubleshooting

### Connection Refused

If you encounter connection errors, ensure:

1. The llama.cpp server is running (`llama-server` command)
2. The server URL and port are correct
3. No firewall is blocking the connection

### Context Window Overflow

If you get context overflow errors:

- Increase context size with `-c` flag when starting server
- Reduce input size
- Enable prompt caching with `cache_prompt: True`

## Advanced Features

### Structured Output

llama.cpp models support structured output through native JSON schema validation. When you use [`Agent.structured_output()`](../../../api-reference/python/agent/agent.md#strands.agent.agent.Agent.structured_output), the SDK uses llama.cpp's json_schema parameter to constrain output:

```python
from pydantic import BaseModel, Field
from strands import Agent
from strands.models.llamacpp import LlamaCppModel

class PersonInfo(BaseModel):
    """Extract person information from text."""
    name: str = Field(description="Full name of the person")
    age: int = Field(description="Age in years")
    occupation: str = Field(description="Job or profession")

model = LlamaCppModel(
    base_url="http://localhost:8080",
    model_id="default",
)

agent = Agent(model=model)

result = agent.structured_output(
    PersonInfo,
    "John Smith is a 30-year-old software engineer working at a tech startup."
)

print(f"Name: {result.name}")      # "John Smith"
print(f"Age: {result.age}")        # 30
print(f"Job: {result.occupation}") # "software engineer"
```

### Grammar Constraints

llama.cpp supports GBNF grammar constraints to ensure output follows specific patterns:

```python
model = LlamaCppModel(
    base_url="http://localhost:8080",
    params={
        "grammar": '''
            root ::= answer
            answer ::= "yes" | "no" | "maybe"
        '''
    }
)

agent = Agent(model=model)
response = agent("Is the Earth flat?")  # Will only output "yes", "no", or "maybe"
```

### Advanced Sampling

llama.cpp offers sophisticated sampling parameters for fine-tuning output:

```python
# High-quality output (slower)
model = LlamaCppModel(
    base_url="http://localhost:8080",
    params={
        "temperature": 0.3,
        "top_k": 10,
        "repeat_penalty": 1.2,
    }
)

# Creative writing
model = LlamaCppModel(
    base_url="http://localhost:8080",
    params={
        "temperature": 0.9,
        "top_p": 0.95,
        "mirostat": 2,
        "mirostat_ent": 5.0,
    }
)
```

### Multimodal Support

For multimodal models like Qwen2.5-Omni, llama.cpp can process images and audio:

```python
# Requires multimodal model and --mmproj flag when starting server
from PIL import Image
import base64
import io

# Image analysis
img = Image.open("example.png")
img_bytes = io.BytesIO()
img.save(img_bytes, format='PNG')
img_base64 = base64.b64encode(img_bytes.getvalue()).decode()

image_message = {
    "role": "user",
    "content": [
        {"type": "image", "image": {"data": img_base64, "format": "png"}},
        {"type": "text", "text": "Describe this image"}
    ]
}

response = agent([image_message])
```

## References

- [API](../../../api-reference/python/models/model.md)
- [llama.cpp](https://github.com/ggml-org/llama.cpp)
- [llama.cpp Server Documentation](https://github.com/ggml-org/llama.cpp/tree/master/tools/server)
- [GGUF Models on Hugging Face](https://huggingface.co/models?search=gguf)
