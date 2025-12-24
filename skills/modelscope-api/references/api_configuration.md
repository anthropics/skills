# API Configuration

## Base Configuration

- **API Endpoint**: `https://api-inference.modelscope.cn/`
- **Authentication**: Bearer Token
- **API Key**: Obtain from ModelScope platform

## Supported Model Types

### Text Generation Models
- `Qwen/Qwen3-VL-235B-A22B-Instruct`
- Other models supporting OpenAI-compatible interfaces

### Image Generation Models
- `Tongyi-MAI/Z-Image-Turbo`
- Other models supporting asynchronous image generation

## Installation Requirements

```bash
npm install node-fetch
```

Or if using yarn:
```bash
yarn add node-fetch
```