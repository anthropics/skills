# LiteRT-LM: On-Device LLM Deployment

## Overview

LiteRT-LM is a C++ library for running large language models on edge devices. It powers Gemini Nano deployments in Chrome, Chromebook Plus, and Pixel Watch.

## Supported Models

| Model | Size | Quantization | Type |
|-------|------|--------------|------|
| Gemma3-1B | 557 MB | 4-bit | Chat |
| Gemma-3n-E2B | 2965 MB | 4-bit | Chat |
| Gemma-3n-E4B | 4235 MB | 4-bit | Chat |
| Phi-4-mini | 3728 MB | 8-bit | Chat |
| Qwen2.5-1.5b | 1524 MB | 8-bit | Chat |
| FunctionGemma-270M | 288 MB | - | Base |

Models use `.litertlm` format (converted from standard formats).

## Performance Benchmarks

**Gemma3-1B (1024 prefill, 256 decode):**

| Device | Prefill (tok/s) | Decode (tok/s) |
|--------|-----------------|----------------|
| MacBook Pro M3 (CPU) | 422.98 | 66.89 |
| Samsung S24 Ultra (GPU) | 1876.5 | 44.57 |
| Samsung S25 Ultra (NPU) | 5836.6 | 84.8 |

LiteRT-LM outperforms llama.cpp by 3x on CPU, 7x on GPU decode, and 19x on GPU prefill.

## Quick Start with CLI (LIT)

### Install

Pre-built binaries available for macOS ARM64, Linux x86_64/ARM64, Windows x86_64.

```bash
# Download from GitHub releases
# Set HuggingFace token for model downloads
export HUGGING_FACE_HUB_TOKEN="your_token"
```

### List and Download Models

```bash
lit list --show_all
lit pull gemma3-1b
```

### Run Inference

```bash
# Interactive mode
lit run gemma3-1b --backend=cpu

# With GPU
lit run gemma3-1b --backend=gpu

# Custom prompt
lit run gemma3-1b --input_prompt="Write me a song"
```

### Benchmarking

```bash
lit run gemma3-1b --backend=cpu \
    --benchmark \
    --benchmark_prefill_tokens=1024 \
    --benchmark_decode_tokens=256
```

## C++ API

### Engine (Entry Point)

```cpp
#include "litert_lm/engine.h"

// Create engine from model
auto engine = Engine::Create("model.litertlm", backend);
```

### Conversation API (Recommended)

Handles tokenization, prompt templating, and stateful chat.

```cpp
// Create conversation
auto conversation = engine->CreateConversation();

// Add messages
conversation->AddUserMessage("Hello, how are you?");

// Generate response
auto response = conversation->Generate();
std::cout << response.text << std::endl;

// Continue conversation
conversation->AddUserMessage("Tell me more");
auto response2 = conversation->Generate();
```

### Session API (Low-Level)

For fine-grained control over prefill/decode phases.

```cpp
auto session = engine->CreateSession();

// Manual prefill
session->Prefill(token_ids);

// Manual decode loop
while (!done) {
    auto next_token = session->Decode();
    // Process token...
}
```

## Android Deployment

### AI Edge Gallery App

Available on Google Play Store for testing models on device.

### Building from Source

```bash
git clone https://github.com/google-ai-edge/LiteRT-LM.git
cd LiteRT-LM

# Build for Android
bazel build //runtime/engine:litert_lm_main \
    --config=android_arm64
```

### Gradle Integration

```groovy
// Coming in stable release
implementation 'com.google.ai.edge.litert:litert-lm:x.x.x'
```

## Multimodal Support

LiteRT-LM supports vision and audio inputs for multimodal models:

```cpp
// Add image to conversation
conversation->AddImage(image_data);
conversation->AddUserMessage("What's in this image?");
auto response = conversation->Generate();
```

## Function Calling

For models like FunctionGemma:

```cpp
// Define available functions
conversation->SetFunctions(function_definitions);

// Generate with potential function calls
auto response = conversation->Generate();
if (response.has_function_call) {
    // Execute function and provide result
    conversation->AddFunctionResult(result);
    auto final_response = conversation->Generate();
}
```

## Model Conversion

Convert PyTorch transformer models using AI Edge Torch Generative API:

```python
import ai_edge_torch

# Convert model
converted = ai_edge_torch.generative.convert(model)
converted.export("model.litertlm")
```
