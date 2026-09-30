# SGLang

{{ community_contribution_banner }}

!!! info "Language Support"
    This provider is only supported in Python.

[strands-sglang](https://github.com/horizon-rl/strands-sglang) is an [SGLang](https://docs.sglang.io/) model provider for Strands Agents SDK with Token-In/Token-Out (TITO) support for agentic RL training. It provides direct integration with SGLang servers using the native `/generate` endpoint, optimized for reinforcement learning workflows.

**Features:**

- **SGLang Native API**: Uses SGLang's native `/generate` endpoint with non-streaming POST for optimal parallelism
- **TITO Support**: Tracks complete token trajectories with logprobs for RL training - no retokenization drift
- **Tool Call Parsing**: Customizable tool parsing aligned with model chat templates (Hermes/Qwen format)
- **Iteration Limiting**: Built-in hook to limit tool iterations with clean trajectory truncation
- **RL Training Optimized**: Connection pooling, aggressive retry (60 attempts), and non-streaming design aligned with [Slime's http_utils.py](https://github.com/THUDM/slime/blob/main/slime/utils/http_utils.py)

## Installation

Install strands-sglang along with the Strands Agents SDK:

```bash
pip install strands-sglang strands-agents-tools
```


## Requirements

- SGLang server running with your model
- HuggingFace tokenizer for the model

## Usage

### 1. Start SGLang Server

First, start an SGLang server with your model:

```bash
python -m sglang.launch_server \
    --model-path Qwen/Qwen3-4B-Instruct-2507 \
    --port 30000 \
    --host 0.0.0.0
```

### 2. Basic Agent

```python
import asyncio
from transformers import AutoTokenizer
from strands import Agent
from strands_tools import calculator
from strands_sglang import SGLangModel

async def main():
    tokenizer = AutoTokenizer.from_pretrained("Qwen/Qwen3-4B-Instruct-2507")
    model = SGLangModel(tokenizer=tokenizer, base_url="http://localhost:30000")
    agent = Agent(model=model, tools=[calculator])

    model.reset()  # Reset TITO state for new episode
    result = await agent.invoke_async("What is 25 * 17?")
    print(result)

    # Access TITO data for RL training
    print(f"Tokens: {model.token_manager.token_ids}")
    print(f"Loss mask: {model.token_manager.loss_mask}")
    print(f"Logprobs: {model.token_manager.logprobs}")

asyncio.run(main())
```

### 3. Slime RL Training

For RL training with [Slime](https://github.com/THUDM/slime/), `SGLangModel` with TITO eliminates the retokenization step:

```python
from strands import Agent, tool
from strands_sglang import SGLangClient, SGLangModel, ToolIterationLimiter
from slime.utils.types import Sample

SYSTEM_PROMPT = "..."
MAX_TOOL_ITERATIONS = 5
_client_cache: dict[str, SGLangClient] = {}

def get_client(args) -> SGLangClient:
    """Get shared client for connection pooling (like Slime)."""
    base_url = f"http://{args.sglang_router_ip}:{args.sglang_router_port}"
    if base_url not in _client_cache:
        _client_cache[base_url] = SGLangClient.from_slime_args(args)
    return _client_cache[base_url]

@tool
def execute_python_code(code: str):
    """Execute Python code and return the output."""
    ...

async def generate(args, sample: Sample, sampling_params) -> Sample:
    """Generate with TITO: tokens captured during generation, no retokenization."""
    assert not args.partial_rollout, "Partial rollout not supported."

    state = GenerateState(args)

    # Set up Agent with SGLangModel and ToolIterationLimiter hook
    model = SGLangModel(
        tokenizer=state.tokenizer,
        client=get_client(args),
        model_id=args.hf_checkpoint.split("/")[-1],
        params={k: sampling_params[k] for k in ["max_new_tokens", "temperature", "top_p"]},
    )
    limiter = ToolIterationLimiter(max_iterations=MAX_TOOL_ITERATIONS)
    agent = Agent(
        model=model,
        tools=[execute_python_code],
        hooks=[limiter],
        callback_handler=None,
        system_prompt=SYSTEM_PROMPT,
    )

    # Run Agent Loop
    prompt = sample.prompt if isinstance(sample.prompt, str) else sample.prompt[0]["content"]
    try:
        await agent.invoke_async(prompt)
        sample.status = Sample.Status.COMPLETED
    except Exception as e:
        # Always use TRUNCATED instead of ABORTED because Slime doesn't properly
        # handle ABORTED samples in reward processing. See: https://github.com/THUDM/slime/issues/200
        sample.status = Sample.Status.TRUNCATED
        logger.warning(f"TRUNCATED: {type(e).__name__}: {e}")

    # TITO: extract trajectory from token_manager
    tm = model.token_manager
    prompt_len = len(tm.segments[0])  # system + user are first segment
    sample.tokens = tm.token_ids
    sample.loss_mask = tm.loss_mask[prompt_len:]
    sample.rollout_log_probs = tm.logprobs[prompt_len:]
    sample.response_length = len(sample.tokens) - prompt_len
    sample.response = model.tokenizer.decode(sample.tokens[prompt_len:], skip_special_tokens=False)

    # Cleanup and return
    model.reset()
    agent.cleanup()
    return sample
```

## Configuration

### Model Configuration

The `SGLangModel` accepts the following parameters:

| Parameter | Description | Example | Required |
| --------- | ----------- | ------- | -------- |
| `tokenizer` | HuggingFace tokenizer instance | `AutoTokenizer.from_pretrained("Qwen/Qwen3-4B-Instruct-2507")` | Yes |
| `base_url` | SGLang server URL | `"http://localhost:30000"` | Yes (or `client`) |
| `client` | Pre-configured `SGLangClient` | `SGLangClient.from_slime_args(args)` | Yes (or `base_url`) |
| `model_id` | Model identifier for logging | `"Qwen3-4B-Instruct-2507"` | No |
| `params` | Generation parameters | `{"max_new_tokens": 2048, "temperature": 0.7}` | No |
| `enable_thinking` | Enable thinking mode for Qwen3 hybrid models | `True` or `False` | No |

### Client Configuration

For RL training, use a centralized `SGLangClient` with connection pooling:

```python
from strands_sglang import SGLangClient, SGLangModel

# Option 1: Direct configuration
client = SGLangClient(
    base_url="http://localhost:30000",
    max_connections=1000,  # Default: 1000
    timeout=None,          # Default: None (infinite, like Slime)
    max_retries=60,        # Default: 60 (aggressive retry for RL stability)
    retry_delay=1.0,       # Default: 1.0 seconds
)

# Option 2: Adaptive to Slime's training args
client = SGLangClient.from_slime_args(args)

model = SGLangModel(tokenizer=tokenizer, client=client)
```

| Parameter | Description | Default |
| --------- | ----------- | ------- |
| `base_url` | SGLang server URL | Required |
| `max_connections` | Maximum concurrent connections | `1000` |
| `timeout` | Request timeout (None = infinite) | `None` |
| `max_retries` | Retry attempts on transient errors | `60` |
| `retry_delay` | Delay between retries (seconds) | `1.0` |

## Troubleshooting

### Connection errors to SGLang server

Ensure your SGLang server is running and accessible:

```bash
# Check if server is responding
curl http://localhost:30000/health
```

### Token trajectory mismatch

If TITO data doesn't match expected output, ensure you call `model.reset()` before each new episode to clear the token manager state.

## References

* [strands-sglang Repository](https://github.com/horizon-rl/strands-sglang)
* [SGLang Documentation](https://docs.sglang.io/)
* [Slime RL Training Framework](https://github.com/THUDM/slime/)
* [Strands Agents API](../../api-reference/python/models/model.md)
