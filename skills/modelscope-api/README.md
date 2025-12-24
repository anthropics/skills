# ModelScope API JavaScript Client

A JavaScript client for ModelScope API that provides easy access to text generation and image generation models.

## Installation

```bash
npm install
```

## Quick Start

### Text Generation

```javascript
const { ModelScopeAPI } = require('./scripts/modelscope-api');

const client = new ModelScopeAPI(); // Uses MODELSCOPE_API_KEY env var
const model = 'Qwen/Qwen2.5-7B-Instruct';
const messages = [
    { role: 'user', content: 'Hello! How are you?' }
];

const response = await client.chatCompletion(model, messages);
console.log(response.choices[0].message.content);
```

### Image Generation

```javascript
const { ModelScopeAPI } = require('./scripts/modelscope-api');

const client = new ModelScopeAPI();
const model = 'Tongyi-MAI/Z-Image-Turbo';
const prompt = 'A beautiful sunset over mountains';

const imageUrl = await client.generateImage(model, prompt);
console.log('Generated image:', imageUrl);
```

## API Reference

### ModelScopeAPI Class

#### Constructor
```javascript
new ModelScopeAPI(apiKey?, baseUrl?)
```
- `apiKey`: Your ModelScope API key (optional, uses MODELSCOPE_API_KEY env var)
- `baseUrl`: API base URL (optional, defaults to 'https://api-inference.modelscope.cn')

#### Methods

##### Text Generation
- `chatCompletion(model, messages, options?)` - Generate text completion
- `chatCompletionStream(model, messages, options?)` - Stream text completion

##### Image Generation
- `generateImage(model, prompt, size?, options?)` - Generate single image
- `batchGenerateImages(model, prompts, size?, options?)` - Generate multiple images

##### Utilities
- `validateLoraWeights(loraConfig)` - Validate LoRA configuration
- `getModelInfo(modelId)` - Get model information
- `listModels(filters?)` - List available models

### Convenience Functions

```javascript
const { chatWithModel, generateImageFromText } = require('./scripts/modelscope-api');

// Quick text generation
const response = await chatWithModel('Qwen/Qwen2.5-7B-Instruct', 'Hello!');

// Quick image generation
const imageUrl = await generateImageFromText('Tongyi-MAI/Z-Image-Turbo', 'A cute cat');
```

## Environment Variables

- `MODELSCOPE_API_KEY`: Your ModelScope API key

## Examples

Run all examples:
```bash
npm run example
```

Or run specific examples from `scripts/examples.js`.

## Features

- ✅ Text generation with OpenAI-compatible API
- ✅ Image generation with async polling
- ✅ Batch image generation
- ✅ LoRA support (single and multiple)
- ✅ Streaming responses
- ✅ Comprehensive error handling
- ✅ Type validation

## Error Handling

The client includes comprehensive error handling:

```javascript
try {
    const response = await client.chatCompletion(model, messages);
} catch (error) {
    console.error('API Error:', error.message);
}
```

## License

MIT