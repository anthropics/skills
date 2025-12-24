# Advanced Usage

## Custom Request Parameters

```javascript
// Custom headers and parameters
const response = await api.chatCompletion(
    'Qwen/Qwen3-VL-235B-A22B-Instruct',
    [{ role: 'user', content: 'Hello' }],
    {
        stream: true,
        temperature: 0.7,
        max_tokens: 1000
    }
);
```

## Batch Image Generation

```javascript
// Generate multiple images
const prompts = ["A golden cat", "A blue dog", "A red bird"];
const imageUrls = await api.batchGenerateImages(
    'Tongyi-MAI/Z-Image-Turbo',
    prompts
);

// Process results
imageUrls.forEach((url, index) => {
    if (url) {
        console.log(`Image ${index + 1}: ${url}`);
    }
});
```

## Error Handling

The skill provides comprehensive error handling:

- **API Request Failures**: Automatic retry mechanism
- **Task Status Monitoring**: Real-time checking for image generation tasks
- **Exception Handling**: Detailed error messages and exception handling

## Important Notes

1. **Token Security**: Keep your ModelScope Token secure
2. **Model IDs**: Ensure correct ModelScope model IDs are used
3. **Async Waiting**: Image generation may require waiting, checks status every 5 seconds by default
4. **LoRA Weights**: When using multiple LoRAs, weights must sum to 1.0
5. **Rate Limiting**: Be aware of ModelScope API rate limits