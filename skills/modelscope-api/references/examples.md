# Usage Examples

## Text Generation Example

```python
from skills.modelscope_api import ModelScopeAPI

# Initialize API client
api = ModelScopeAPI(api_key="your-modelscope-token")

# Call text generation
response = api.chat_completion(
    model="Qwen/Qwen3-VL-235B-A22B-Instruct",
    messages=[{"role": "user", "content": "Hello"}],
    stream=True
)

# Handle streaming response
for chunk in response:
    if chunk.choices:
        content = chunk.choices[0].delta.content
        if content:
            print(content, end='', flush=True)
```

## Image Generation Example

```python
# Generate image
image_path = api.generate_image(
    model="Tongyi-MAI/Z-Image-Turbo",
    prompt="A golden cat",
    output_path="result_image.jpg"
)
print(f"Image saved to: {image_path}")
```

## Using LoRA Models

### Single LoRA
```python
image_path = api.generate_image(
    model="Tongyi-MAI/Z-Image-Turbo",
    prompt="A golden cat",
    loras="lora-repo-id",
    output_path="result_with_lora.jpg"
)
```

### Multiple LoRAs (weights must sum to 1.0)
```python
image_path = api.generate_image(
    model="Tongyi-MAI/Z-Image-Turbo",
    prompt="A golden cat",
    loras={"lora1": 0.6, "lora2": 0.4},
    output_path="result_with_multiple_loras.jpg"
)
```