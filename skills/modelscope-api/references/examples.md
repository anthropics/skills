# Usage Examples

## Text Generation Example

```javascript
const { ModelScopeAPI } = require('../scripts/modelscope-api');

// Initialize API client
const api = new ModelScopeAPI('your-modelscope-token');

// Call text generation
const response = await api.chatCompletion(
    'Qwen/Qwen3-VL-235B-A22B-Instruct',
    [{ role: 'user', content: 'Hello' }],
    { stream: true }
);

// Handle response
console.log(response.choices[0].message.content);
```

## Image Generation Example

```javascript
// Generate image
const imageUrl = await api.generateImage(
    'Tongyi-MAI/Z-Image-Turbo',
    'A golden cat'
);
console.log('Generated image:', imageUrl);
```

## Using LoRA Models

### Single LoRA
```javascript
const imageUrl = await api.generateImage(
    'Tongyi-MAI/Z-Image-Turbo',
    'A golden cat',
    '752x1280',
    {
        lora_path: 'lora-repo-id',
        lora_weight: 0.8
    }
);
console.log('Generated image with LoRA:', imageUrl);
```

### Multiple LoRAs (weights must sum to 1.0)
```javascript
const loras = {
    lora_paths: ['lora1-repo-id', 'lora2-repo-id'],
    lora_weights: [0.6, 0.4]
};

// Validate LoRA weights first
if (api.validateLoraWeights(loras)) {
    const imageUrl = await api.generateImage(
        'Tongyi-MAI/Z-Image-Turbo',
        'A golden cat',
        '752x1280',
        {
            lora_paths: loras.lora_paths,
            lora_weights: loras.lora_weights
        }
    );
    console.log('Generated image with multiple LoRAs:', imageUrl);
}
```