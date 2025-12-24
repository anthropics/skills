# Advanced Usage

## Custom Request Parameters

```python
# Custom headers and parameters
response = api.chat_completion(
    model="Qwen/Qwen3-VL-235B-A22B-Instruct",
    messages=[{"role": "user", "content": "Hello"}],
    stream=True,
    temperature=0.7,
    max_tokens=1000
)
```

## Batch Image Generation

```python
# Generate multiple images
prompts = ["A golden cat", "A blue dog", "A red bird"]
image_paths = api.batch_generate_images(
    model="Tongyi-MAI/Z-Image-Turbo",
    prompts=prompts,
    output_dir="batch_images/"
)
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