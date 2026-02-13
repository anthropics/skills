# MLX

{{ community_contribution_banner }}

!!! info "Language Support"
    This provider is only supported in Python.

[strands-mlx](https://github.com/cagataycali/strands-mlx) is an [MLX](https://ml-explore.github.io/mlx/) model provider for Strands Agents SDK that enables running AI agents locally on Apple Silicon. It supports inference, fine-tuning with LoRA, and vision models.

**Features:**

- **Apple Silicon Native**: Optimized for M1/M2/M3/M4 chips using Apple's MLX framework
- **LoRA Fine-tuning**: Train custom adapters from agent conversations
- **Vision Support**: Process images, audio, and video with multimodal models
- **Local Inference**: Run agents completely offline without API calls
- **Training Pipeline**: Collect data → Split → Train → Deploy workflow

## Installation

Install strands-mlx along with the Strands Agents SDK:

```bash
pip install strands-mlx strands-agents-tools
```

## Requirements

- macOS with Apple Silicon (M1/M2/M3/M4)
- Python ≤3.13

## Usage

### Basic Agent

```python
from strands import Agent
from strands_mlx import MLXModel
from strands_tools import calculator

model = MLXModel(model_id="mlx-community/Qwen3-1.7B-4bit")
agent = Agent(model=model, tools=[calculator])

agent("What is 29 * 42?")
```

### Vision Model

```python
from strands import Agent
from strands_mlx import MLXVisionModel

model = MLXVisionModel(model_id="mlx-community/Qwen2-VL-2B-Instruct-4bit")
agent = Agent(model=model)

agent("Describe: <image>photo.jpg</image>")
```

### Fine-tuning with LoRA

Collect training data from agent conversations and fine-tune:

```python
from strands import Agent
from strands_mlx import MLXModel, MLXSessionManager, dataset_splitter, mlx_trainer

# Collect training data
agent = Agent(
    model=MLXModel(model_id="mlx-community/Qwen3-1.7B-4bit"),
    session_manager=MLXSessionManager(session_id="training", storage_dir="./dataset"),
    tools=[dataset_splitter, mlx_trainer],
)

# Have conversations (auto-saved)
agent("Teach me about quantum computing")

# Split and train
agent.tool.dataset_splitter(input_path="./dataset/training.jsonl")
agent.tool.mlx_trainer(
    action="train",
    config={
        "model": "mlx-community/Qwen3-1.7B-4bit",
        "data": "./dataset/training",
        "adapter_path": "./adapter",
        "iters": 200,
    }
)

# Use trained model
trained = MLXModel("mlx-community/Qwen3-1.7B-4bit", adapter_path="./adapter")
expert_agent = Agent(model=trained)
```

## Configuration

### Model Configuration

The `MLXModel` accepts the following parameters:

| Parameter | Description | Example | Required |
| --------- | ----------- | ------- | -------- |
| `model_id` | HuggingFace model ID | `"mlx-community/Qwen3-1.7B-4bit"` | Yes |
| `adapter_path` | Path to LoRA adapter | `"./adapter"` | No |

### Recommended Models

**Text:**

- `mlx-community/Qwen3-1.7B-4bit` (recommended for agents)
- `mlx-community/Qwen3-4B-4bit`
- `mlx-community/Llama-3.2-1B-4bit`

**Vision:**

- `mlx-community/Qwen2-VL-2B-Instruct-4bit` (recommended)
- `mlx-community/llava-v1.6-mistral-7b-4bit`

Browse more models at [mlx-community on HuggingFace](https://huggingface.co/mlx-community).

## Troubleshooting

### Out of memory

Use smaller quantized models or reduce batch size:

```python
config = {
    "grad_checkpoint": True,
    "batch_size": 1,
    "max_seq_length": 1024
}
```

### Model not found

Ensure you're using a valid mlx-community model ID. Models are automatically downloaded from HuggingFace on first use.

## References

- [strands-mlx Repository](https://github.com/cagataycali/strands-mlx)
- [MLX Documentation](https://ml-explore.github.io/mlx/)
- [mlx-community Models](https://huggingface.co/mlx-community)
- [Strands Agents SDK](https://strandsagents.com)
