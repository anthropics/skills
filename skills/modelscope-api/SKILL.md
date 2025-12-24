---
name: modelscope-api
description: Provides convenient access and invocation capabilities for ModelScope platform APIs, supporting text generation, image generation, and other AI model services. Use when working with ModelScope APIs for text generation, image generation, or model management tasks.
license: Complete terms in LICENSE.txt
---

# ModelScope API Skill

This skill provides convenient access to ModelScope platform APIs for text generation, image generation, and AI model services.

## Quick Start

### Text Generation

```python
from skills.modelscope_api import ModelScopeAPI

# Initialize API client
api = ModelScopeAPI(api_key="your-modelscope-token")

# Generate text with streaming
response = api.chat_completion(
    model="Qwen/Qwen3-VL-235B-A22B-Instruct",
    messages=[{"role": "user", "content": "Hello"}],
    stream=True
)

# Process streaming response
for chunk in response:
    if chunk.choices and chunk.choices[0].delta.content:
        print(chunk.choices[0].delta.content, end='', flush=True)
```

### Image Generation

```python
# Generate image
image_path = api.generate_image(
    model="Tongyi-MAI/Z-Image-Turbo",
    prompt="A golden cat",
    output_path="result_image.jpg"
)
```

## When to Use References

- **API Configuration**: See [references/api_configuration.md](references/api_configuration.md) for setup details and supported models
- **Advanced Usage**: See [references/advanced_usage.md](references/advanced_usage.md) for custom parameters, batch operations, and error handling
- **Complete Examples**: See [references/examples.md](references/examples.md) for detailed usage examples including LoRA models

## Key Features

- Text generation with OpenAI-compatible interface
- Image generation with asynchronous processing
- LoRA model support
- Streaming responses for text generation
- Batch image generation capabilities