---
name: modelscope-api
description: Provides convenient access and invocation capabilities for ModelScope platform APIs, supporting text generation, image generation, and other AI model services. Use when working with ModelScope APIs for text generation, image generation, or model management tasks.
license: Complete terms in LICENSE.txt
---

# ModelScope API Skill

This skill provides convenient access to ModelScope platform APIs for text generation, image generation, and AI model services.

## Quick Start

### Text Generation

```javascript
const { ModelScopeAPI } = require('./scripts/modelscope-api');

// Initialize API client
const api = new ModelScopeAPI('your-modelscope-token');

// Generate text
const response = await api.chatCompletion(
    'Qwen/Qwen3-VL-235B-A22B-Instruct',
    [{ role: 'user', content: 'Hello' }]
);
console.log(response.choices[0].message.content);

// Generate text with streaming
const stream = await api.chatCompletionStream(
    'Qwen/Qwen3-VL-235B-A22B-Instruct',
    [{ role: 'user', content: 'Hello' }]
);
// Process streaming response (see examples.js for full implementation)
```

### Image Generation

```javascript
// Generate image
const imageUrl = await api.generateImage(
    'Tongyi-MAI/Z-Image-Turbo',
    'A golden cat'
);
console.log('Generated image:', imageUrl);
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