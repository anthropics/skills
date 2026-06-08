# Models, Benchmarks, and Evaluation Reference

## LLM Model Landscape (Mid-2026)

### Closed Frontier Models

#### OpenAI
- **GPT-5 family**: Iterating monthly (5.0→5.1→5.2→5.3→5.4 cadence as of 2026). Internal router selects sub-model per query. Leads on agentic workflow breadth and scientific reasoning.
- **o3 / o4-mini**: Reasoning-focused models with extended thinking. o3 priced at $15/$60 per million input/output tokens. Leads Olympiad-level science benchmarks (FrontierScience).
- **GPT-5 Nano/Mini**: Sub-$0.50/M output tokens; suited for high-volume classification and extraction
- **GPT-4.1**: $0.10/$0.40 per million tokens for Nano variant. Solid mid-tier capability.
- **Batch API**: 50% discount across all models; prompt caching up to 90% discount on cached inputs.

#### Anthropic
- **Claude Opus 4.x series**: Leads coding benchmarks — SWE-Bench Verified ~87.6%. Designed for long autonomous operation ("hours" of agentic work). Constitutional AI + RLHF trained.
- **Claude Haiku 4.5**: $1/$5 per million tokens. Cost-effective for production RAG and classification.
- **Claude Sonnet 4.x**: Mid-tier between Haiku and Opus; best value for complex reasoning without Opus cost.
- **Key differentiator**: Interpretability research (circuit tracing, sparse autoencoders) means Anthropic has deepest mechanistic understanding of their models.

#### Google DeepMind
- **Gemini 2.5 Pro**: "Thinking" model that dynamically allocates compute. Excellent reasoning; competitive with GPT-5 and Claude Opus.
- **Gemini 3**: Major multimodal leap. ScreenSpot-Pro score 72.7% vs. 11.4% for Gemini 2.5 Pro — near-7x improvement in computer use/screen understanding.
- **Gemini Flash-Lite**: ~$0.075/$0.30 per million tokens. Cost leader for bulk inference.
- **Gemini 1.5 Flash**: $0.075/$0.30 per million tokens. Strong on long context (1M+ tokens native).
- **Key differentiator**: Multimodal depth, long context, Google infrastructure integration (Search, Workspace).

#### xAI
- **Grok 4**: Achieved near-98% on HumanEval-style coding benchmarks. Strong science and math reasoning.
- **Key differentiator**: Access to real-time X/Twitter data; less filtering than competitors.

#### Mistral AI
- **Mistral 7B / Mixtral 8x7B**: Established open-weight releases; now superseded by larger open models for capability, but remain fast and cheap.
- **Mistral Large**: Competitive mid-tier closed model.
- **Key differentiator**: European-based (GDPR compliance), genuinely open model releases, efficient architectures.

### Open-Weight Models

#### Meta AI / FAIR
- **Llama 4 Scout**: 109B total parameters (MoE), 17B activated per forward pass. Multimodal (text + image). 10M token context window. Strong general capability.
- **Llama 3.3 70B**: Still widely deployed; excellent balance of capability and hardware requirements.
- **License**: Llama license (mostly permissive with some commercial restrictions at large scale).
- **Key differentiator**: Best-maintained open-weight model family; strong ecosystem support.

#### DeepSeek (Hangzhou DeepSeek AI)
- **DeepSeek R1** (released Jan 20, 2025): The landmark open-source reasoning model. 671B params, 37B activated (MoE). Pure RL training approach — no supervised fine-tuning to bootstrap. Matched OpenAI o1 at ~$6M training cost. MIT license. Triggered the "AI price war."
- **DeepSeek V3.2 / V4 Pro**: Long-context reasoning, coding, and agentic workflows. ~80.6% SWE-Bench Verified at 34× lower cost than Claude Opus.
- **Key differentiator**: Extreme cost efficiency; MIT license enables unrestricted commercial use.

#### Qwen (Alibaba DAMO Academy)
- **Qwen 3.7 / Qwen 3 VL**: Competitive multimodal model. Strong multilingual capability. Available quantized for local deployment.
- **Key differentiator**: Multilingual depth (especially Chinese), multimodal, accessible quantized versions.

#### GLM / Zhipu AI
- **GLM-5.1 Thinking**: Strong reasoning; competitive coding benchmarks. Less widely known in Western contexts.

### Local Deployment Tools

#### Ollama
- Command-line tool for running quantized models locally. Supports GGUF format natively.
- Can use any GGUF quantized model from Hugging Face Hub directly without a Modelfile.
- 45,000+ public GGUF checkpoints available on Hub.
- Best for: developers, CLI-first workflows, server-side local inference.
- Installation: single command; starts model server on localhost.

#### LM Studio
- Desktop GUI application for local LLM inference. Supports Mac (Apple Silicon via MLX), Windows, Linux.
- Best for: non-technical users, quick testing, API-compatible local server.
- Apple Silicon: MLX backend enables fast inference on MacBook Pro M-series.

#### llama.cpp
- Low-level C++ inference engine. Best CPU performance; foundation of Ollama and many others.
- GGUF format: 4-bit and 8-bit quantization reduces VRAM by 4-8× with minimal quality loss.
- Key for edge deployment and CPU-only environments.

---

## Benchmark Reference

### Academic/Static Benchmarks (Contamination Risk)

| Benchmark | What it measures | Status | Notes |
|-----------|-----------------|--------|-------|
| MMLU | Multi-task knowledge (57 subjects) | Saturated | Use MMLU-Pro instead |
| MMLU-Pro | Harder reasoning-focused MMLU variant | Active | Better discrimination |
| HumanEval | Function-level code generation | Saturated | Top models ~98% |
| GSM8K | Grade-school math | Saturated | Use MATH or MATH-500 |
| MATH / MATH-500 | Competition mathematics | Active | Still discriminates models |
| GPQA-Diamond | PhD-level science (biology, chemistry, physics) | Active, some gaming | Human experts ~70%; frontier ~88%; Goodhart's Law risk |
| BIG-Bench Hard | Reasoning subset of BIG-Bench | Active | Use Hard subset for discrimination |
| HELM | Meta-evaluation across scenarios | Active | Reports robustness, bias, efficiency alongside accuracy |

### Dynamic/Contamination-Resistant Benchmarks

| Benchmark | What it measures | Why it's better |
|-----------|-----------------|-----------------|
| SWE-Bench Verified | Real GitHub issue resolution | Uses real repos; hard to game; tests full engineering workflow |
| LiveCodeBench | Competitive programming | Uses post-cutoff problems; refreshed continuously |
| LMSYS Chatbot Arena | Human preference in open-ended conversation | Real user votes; reflects actual usage quality |
| FrontierMath | Frontier mathematics (unpublished) | Novel problems; no contamination possible |

### SWE-Bench Progression
- 2023: 4.4% (best model)
- 2024: 71.7% (best model)
- 2025-2026: 80%+ (frontier models)
- Interpretation: Measures ability to resolve a GitHub issue including understanding existing codebase, root cause analysis, writing a fix, passing test suites.

### Critical Evaluation Questions
1. **Contamination**: Is this dataset in the model's training data? (Especially true for MMLU, HumanEval, GSM8K)
2. **Goodhart's Law**: Has the benchmark become a training target? (GPQA-Diamond, HumanEval)
3. **Task relevance**: Does this benchmark match your actual use case?
4. **Baseline fairness**: What are they comparing against? Are baselines current and equivalent?
5. **Reproducibility**: Is code and evaluation harness released?

---

## Custom Evaluation Setup

### PromptFoo (Open-source, recommended starting point)
- YAML/JSON-based test specifications; runs locally by default
- Supports LLM-as-judge evaluators, regex assertions, custom JavaScript checks
- A/B testing across models and prompts; regression testing
- Install: `npm install -g promptfoo`
- Use for: prompt engineering, model comparison, catching regressions, red-teaming

```yaml
# promptfooconfig.yaml example structure
prompts:
  - "Classify this support ticket: {{ticket}}"
providers:
  - openai:gpt-4.1
  - anthropic:claude-haiku-4-5
tests:
  - vars:
      ticket: "My order hasn't arrived after 3 weeks"
    assert:
      - type: llm-rubric
        value: "Response should identify this as a shipping/delivery issue"
```

### LangSmith (Managed, best for teams)
- Logging, tracing, and evaluation platform from LangChain team
- Supports: human annotation queues, heuristic checks, LLM-as-judge, pairwise comparisons
- Custom Python/TypeScript evaluators with arbitrary business logic
- Best for: production monitoring, team collaboration, iterative improvement loops

### RAGAS (RAG pipeline specific)
- Specialized for evaluating Retrieval-Augmented Generation pipelines
- Metrics: faithfulness, answer relevancy, context precision, context recall
- Integrates with LangChain, Haystack, LlamaIndex
- Use for: validating RAG retrieval quality, grounding accuracy, hallucination detection

### DeepEval
- Open-source; supports G-Eval, RAGAS metrics, hallucination detection, bias, toxicity
- Can run locally or via managed cloud
- Best for: comprehensive LLM testing with many pre-built metrics

### Evaluation Best Practices
1. Always test on your actual data, not public benchmarks alone
2. Include adversarial examples (edge cases, ambiguous inputs)
3. LLM-as-judge works well at scale — use GPT-4 or Claude Opus as evaluator
4. Track regressions: new model versions can be worse on your task even if better on benchmarks
5. Sample size: 50-100 examples is usually sufficient for directional guidance; 500+ for reliable comparison

---

## Agentic AI Frameworks

### LangGraph
- Graph-based orchestration built on LangChain
- Best for: stateful agents, complex branching/conditional logic, long-running workflows
- Supports: human-in-the-loop, error recovery, parallel branches

### LlamaIndex
- Best for: retrieval-heavy applications, knowledge base Q&A, document processing
- Most accurate RAG implementation in production testing
- Composable pipeline architecture

### CrewAI
- Role-based multi-agent systems
- Each agent has a specialized function within a team
- Best for: task decomposition across specialized agents, parallel execution of independent subtasks

### AutoGen (Microsoft)
- Multi-agent collaboration with asynchronous execution
- Supports human-in-the-loop oversight
- Best for: research workflows, code execution loops, tool use chains

### Production Recommendation
Most resilient production architectures combine frameworks:
- LlamaIndex for retrieval
- LangGraph for orchestration
- AutoGen or CrewAI for specialized agent modules

McKinsey State of AI 2025: 62% of organizations experimenting with AI agents; 23% scaling agentic systems in at least one function.

---

## RAG Architecture Best Practices

### Core Pattern
Query → Retrieval (vector search) → Context injection → Generation → Validation

### Key Optimization Levers
1. **Chunk size**: Smaller chunks (256-512 tokens) for precise retrieval; larger (1024+) for contextual completeness
2. **Embedding model**: Choose domain-appropriate embeddings; don't use default OpenAI embeddings for highly specialized domains
3. **Hybrid search**: Combine dense (semantic) + sparse (BM25 keyword) retrieval for better recall
4. **Query expansion**: Rephrase query multiple ways before retrieval; improves recall significantly
5. **Re-ranking**: Apply a cross-encoder re-ranker after initial retrieval to improve precision
6. **Context window management**: Don't just stuff everything in — select most relevant chunks

### Common Failure Mode
Over 70% of new LLM features fail in production because RAG is bolted on rather than designed in. Design data ingestion, chunking, and retrieval strategy before building generation layer.

### Evaluation with RAGAS
- **Faithfulness**: Does the answer only use information from retrieved context? (Hallucination detection)
- **Answer Relevancy**: Is the answer relevant to the question?
- **Context Precision**: Are retrieved chunks actually relevant?
- **Context Recall**: Were all necessary chunks retrieved?

---

## API Pricing Quick Reference (Mid-2026, Indicative)

| Tier | Models | Input | Output |
|------|--------|-------|--------|
| Budget | GPT-5 Nano, Gemini Flash-Lite, Mistral 7B | $0.05-0.10 | $0.05-0.40 |
| Mid | Claude Haiku 4.5, Gemini Flash, GPT-4.1 | $0.075-1.00 | $0.30-5.00 |
| Premium | Claude Opus 4.x, GPT-5, Gemini 2.5 Pro | $3-15 | $15-60 |
| Reasoning | o3, o4, Claude Reasoning | $15+ | $60+ |

**Cost optimization strategies**:
1. Route by complexity (70% budget, 20% mid, 10% premium)
2. Use batch APIs (50% discount, OpenAI and Anthropic)
3. Implement prompt caching (up to 90% discount on repeated context)
4. Cache common responses at application layer
5. Use streaming to reduce perceived latency while processing begins

Note: Prices drop approximately 50-80% per year. Always check current pricing directly from provider.
