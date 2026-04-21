# Security & Data Privacy

## Why this matters

SEAL skills handle information about an organization's security posture:
- Which controls they **fail** (security gaps)
- Missing incident response capabilities
- Weak multisig configurations
- Unencrypted communication channels
- Lack of monitoring or detection
- Hiring practices and insider threat exposure

**Using these skills with a cloud LLM provider sends sensitive organizational security data to a third party.**

## Trust assumptions

| Provider | What they see | Risk level | When to use |
|---|---|---|---|
| **Local LLM** (Ollama, vLLM) | Nothing leaves the machine | None | Highest security, air-gapped |
| **Venice.ai** | Queries during inference, no retention | Low | Privacy + quality balance |
| **Self-hosted** (Modal, Lambda) | You control the infrastructure | Low-Medium | Scale + full control |
| **Anthropic/Claude** | All queries retained, potentially used for training | High | Non-sensitive tasks only |
| **OpenAI** | All queries retained, training data policies change | High | Exploration only |
| **OpenRouter** | Aggregator — depends on underlying provider | Varies | Never for sensitive data |

### Venice.ai guarantees (verify independently)

- No data retention on queries
- No training on user data
- OpenAI-compatible API (drop-in replacement)
- Models: qwen3-5-35b-a3b, kimi-k2-5, others

**Caveat:** "No retention" is a policy, not a technical guarantee. Treat Venice as lower-risk than Anthropic/OpenAI, but not equivalent to local inference.

### Local LLM

For zero-trust environments, run locally:

```bash
# Ollama (simplest)
ollama pull llama3.3:70b
# Hermes config: OPENAI_BASE_URL=http://localhost:11434/v1

# vLLM (more control)
vllm serve meta-llama/Llama-3.3-70B-Instruct
# Hermes config: OPENAI_BASE_URL=http://localhost:8000/v1
```

**Tradeoffs:**
- 70B+ models recommended for full framework knowledge
- Tool calling support varies by model
- Requires significant GPU (70B needs ~40GB VRAM)

## What flows to the LLM

Every interaction with seal skills sends context that includes:
- The user's security questions (reveals what they're worried about)
- Answers to cert controls ("no" = specific gap identified)
- Incident scenarios (details of real or hypothetical breaches)
- Gotchas discussed (indicates known weaknesses)

## Deployment patterns

### Pattern 1: Venice.ai (recommended for demo)

```yaml
# config.yaml (Hermes)
# Uncomment to use Venice.ai
# provider: openai
# base_url: https://api.venice.ai/v1
# api_key: ${VENICE_API_KEY}
# model: qwen3-5-35b-a3b
```

```bash
# .env
# VENICE_API_KEY=your-venice-api-key
```

### Pattern 2: Local Ollama

```yaml
# config.yaml
# provider: openai
# base_url: http://localhost:11434/v1
# api_key: ollama
# model: llama3.3:70b
```

### Pattern 3: Air-gapped

Same as local Ollama, but machine has no internet access. All seal skill reference files are included in the repo — no external calls needed.

## Inference provider config (.env template)

```bash
# Venice.ai (private inference, no data retention)
# VENICE_API_KEY=your-key-here
# VENICE_MODEL=qwen3-5-35b-a3b

# Local Ollama
# OLLAMA_BASE_URL=http://localhost:11434/v1

# Local vLLM
# VLLM_BASE_URL=http://localhost:8000/v1

# Self-hosted
# SELF_HOSTED_API_KEY=your-key
# SELF_HOSTED_BASE_URL=https://your-endpoint.com/v1
```

## Key rule

**Before deploying seal skills for any organization, ask: "Are we comfortable with our inference provider seeing this data?"**

If the answer is no, use local inference or Venice.ai. Don't default to Anthropic/OpenAI without considering the sensitivity of the security data being processed.
