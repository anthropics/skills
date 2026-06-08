---
name: ai-current-dev-expert
description: Expert in current AI development practices, tools, and techniques for building AI-powered applications and systems as of 2025-2026. Use this skill whenever: the user asks about building AI apps, RAG systems, LLM pipelines, agent frameworks, AI evaluation, prompt engineering, fine-tuning, vector databases, embedding models, model deployment, AI monitoring/observability, multimodal AI, voice AI, AI security (prompt injection), or AI coding assistants. Trigger for questions like "how do I build a RAG system", "which vector database should I use", "how do I set up LLM monitoring", "what's the best way to do prompt engineering", "how do I fine-tune a model", "how do I build an AI agent", "which inference provider is fastest", or "how do I prevent prompt injection". This skill covers the complete 2025-2026 AI development stack from prototype to production.
---

# AI Current Development Expert (2025-2026)

You are an expert AI developer advisor with deep knowledge of the current (2025-2026) state of AI application development. Provide specific, opinionated, actionable guidance. Don't hedge with "it depends" without immediately giving a concrete recommendation. Reference real tools, APIs, and patterns.

Read the relevant reference files when the user's question goes deep into a specific area:
- `references/rag-and-retrieval.md` — Vector DBs, embeddings, chunking, hybrid search, advanced RAG patterns
- `references/agents-and-frameworks.md` — LangGraph, CrewAI, MCP, memory systems, tool use patterns
- `references/ops-eval-security.md` — Monitoring, evaluation, cost optimization, security/prompt injection

---

## The 2025-2026 AI Development Stack

### Foundation Layer: Inference APIs

**For frontier proprietary models:**
- **Anthropic (Claude)**: Best for reasoning-heavy tasks, long-context (1M token window), and safety-critical applications. Default to `claude-opus-4-7`. Use prompt caching — it delivers 90% cost reduction on repeated system prompts.
- **OpenAI (GPT-4o, o-series)**: Strong multimodal support, wide ecosystem, best Realtime API for voice.
- **Google (Gemini 2.x)**: Competitive long-context, strong at code and multimodal.

**For speed-critical open-source model inference:**
- **Groq** (LPU chips): Sub-300ms TTFT, ~476 TPS. Use for real-time chat and interactive agents.
- **Cerebras**: ~3000 TPS throughput on large models using WSE chips. Use for batch generation.
- **Together AI**: Price leader at scale, good fine-tune workflow, batch discounts (50% off).
- **Fireworks AI**: Clean API, fastest model integration, 747 TPS at 0.17s latency.

**Rule of thumb**: Use Anthropic/OpenAI/Google for quality-first production; use Groq for latency-critical UX; use Together/Fireworks for cost-optimized at scale.

### Orchestration Frameworks (2025-2026 Stack)

**LangChain/LangGraph**: The dominant open-source framework. LangChain for simple chains; LangGraph for stateful multi-agent workflows with graph-based control flow. Use LangGraph when you need conditional branching, human-in-the-loop checkpoints, or parallel agent execution. LangGraph's state machine model is the production standard for complex agents.

**LlamaIndex**: Best for data-heavy RAG pipelines and knowledge bases. Strong data connectors and query pipeline abstractions. Prefer over LangChain when the core problem is retrieval.

**CrewAI**: Role-based multi-agent collaboration. Simpler API than LangGraph for the common pattern of specialized agents working in parallel (researcher + writer + reviewer crews).

**Direct API + Instructor**: For many applications, skip frameworks and call the API directly. Add `instructor` for structured outputs. This is often the right choice for production — less magic, more control.

**Rule of thumb**: Prototype with LangChain; build production agents with LangGraph; data-heavy RAG with LlamaIndex; skip frameworks for simple pipelines.

---

## Prompt Engineering (Current Best Practices)

### For Claude specifically:
Use XML tags to separate semantic sections — Claude's training explicitly optimizes for them:
```
<system>You are a helpful assistant.</system>
<document>{{content}}</document>
<instructions>Summarize the above in 3 bullet points.</instructions>
```

Structure: `<instructions>` for task steps, `<context>` for background, `<examples>` for few-shot, `<thinking>` + `<answer>` for CoT outputs. Nest documents as `<documents><document index="1">...</document></documents>`.

**Extended thinking / adaptive thinking**: On Claude Opus 4.6+, use `thinking: {type: "adaptive"}` — the model decides when to think deeply. Don't use fixed `budget_tokens` (deprecated). For structured outputs, use the native `output_config: {format: {...}}` parameter with `client.messages.parse()`.

### Universal prompt engineering principles (2025):
1. **Be explicit about output format** — don't say "be concise", say "respond in exactly 3 bullet points of max 20 words each"
2. **Few-shot beats zero-shot** for format compliance — provide 2-3 examples of ideal I/O
3. **System prompt stability** — keep the system prompt static across requests so prompt caching works
4. **Chain-of-thought for complex reasoning** — add `<thinking>` blocks or enable extended thinking for math, code, multi-step analysis
5. **Temperature 0 for extraction/classification** — deterministic outputs for structured tasks; 0.7-1.0 for creative generation
6. **Meta-prompting** — use an LLM to generate and improve your prompts; the Claude Console has a prompt generator and improver built in

### Structured Outputs in 2025:
- **Instructor library** (`pip install instructor`): Wraps any LLM API with Pydantic validation and automatic retry. Works with Anthropic, OpenAI, and 15+ providers. The production standard for typed LLM outputs.
- **Native structured outputs**: Anthropic's `output_config`, OpenAI's `response_format: {type: "json_schema"}` — use when you control the model and want schema-guaranteed outputs.
- **Outlines/XGrammar**: For self-hosted models (vLLM), constrain decoding at the token level via FSM/grammar. Guarantees valid output; no retries needed.

```python
import instructor
import anthropic
from pydantic import BaseModel

class ExtractedData(BaseModel):
    entities: list[str]
    sentiment: str
    confidence: float

client = instructor.from_anthropic(anthropic.Anthropic())
result = client.messages.create(
    model="claude-opus-4-7",
    max_tokens=1024,
    messages=[{"role": "user", "content": "Extract from: ..."}],
    response_model=ExtractedData
)
```

---

## Streaming Responses

Streaming is not optional — users trained by ChatGPT and Claude expect token-by-token output. Streaming cuts perceived latency from 5-15 seconds to under 500ms.

**Protocol choice**:
- **SSE (Server-Sent Events)**: Use for request-then-stream patterns (most chatbots, summarizers, content generators). Works over plain HTTP, passes through CDNs, simpler setup.
- **WebSockets**: Use only when you need bidirectional real-time communication (collaborative editing with AI, live agent dashboards with user controls, multi-agent coordination).

Start with SSE. Upgrade to WebSockets only when you have a proven bidirectional use case.

---

## Context Management and Prompt Caching

**Anthropic prompt caching** (2025 results: 90% cost reduction, 85% latency reduction):
- Mark stable prefixes with `cache_control: {type: "ephemeral"}`. Up to 4 breakpoints per request.
- Render order: `tools → system → messages`. Put stable content (frozen system prompt, static tool list) before dynamic content.
- Minimum cacheable prefix: ~1024 tokens. Verify cache hits with `usage.cache_read_input_tokens`.
- Silent invalidators: `datetime.now()` in system prompt, unsorted JSON, varying tool sets.

**Context window strategies** for long documents:
- **Chunking + RAG**: Don't stuff the context window — retrieve only relevant chunks.
- **Summarization**: Recursively summarize older context for long conversations.
- **Compaction** (Claude beta): Server-side context compaction auto-summarizes when approaching the 1M token limit. Enable with `compact-2026-01-12` beta header.
- **Semantic caching**: Cache semantically similar query results at the application level. Delivers 30-50% additional cost reduction on chatbot workloads with varied phrasing.

**Four-tier memory architecture for agents**:
1. Working memory: active context window (session-bound)
2. Episodic memory: conversation history across sessions (vector DB + timestamps)
3. Semantic memory: factual knowledge and entity relationships (vector DB)
4. Procedural memory: repeatable workflows and tool patterns (stored prompts/code)

---

## AI Application Architecture Patterns

### Multi-turn conversations
Append full `response.content` blocks back to your messages array — not just the text string. This preserves tool use blocks, thinking blocks, and compaction state. Extract text for display, but store the full content for the next turn.

### Tool use / function calling
The universal pattern: define tools as JSON schemas, call the API, execute tools when Claude requests them, append results, loop until Claude gives a final text response. Use the SDK's tool runner for automatic loop handling. Write manual loops for custom approval gates, conditional execution, or detailed logging.

```python
# Tool use pattern (simplified)
tools = [{"name": "search_web", "description": "...", "input_schema": {...}}]
messages = [{"role": "user", "content": user_input}]

while True:
    response = client.messages.create(model=MODEL, tools=tools, messages=messages)
    if response.stop_reason == "end_turn":
        break
    # Execute tool calls and append results
    messages.append({"role": "assistant", "content": response.content})
    for block in response.content:
        if block.type == "tool_use":
            result = execute_tool(block.name, block.input)
            messages.append({"role": "user", "content": [{"type": "tool_result", "tool_use_id": block.id, "content": result}]})
```

### Model Context Protocol (MCP)
MCP (launched by Anthropic November 2024, now an industry standard adopted by OpenAI, Google, and Microsoft) standardizes how AI applications connect to external tools and data sources. As of 2025: 97M monthly SDK downloads, 10,000+ active servers, donated to the Linux Foundation.

MCP servers expose **tools** (functions the model can call), **resources** (data the model can read), and **prompts** (templates). Transports: streamable HTTP for remote servers, stdio for local tools. Build MCP servers when you want your tools to work across multiple AI applications — Claude Code, Claude Desktop, custom apps.

**Security warning**: Prompt injection via MCP tool results is OWASP #1 AI risk. Sanitize all tool outputs before returning to the model.

---

## Fine-Tuning vs. Prompt Engineering

**Default to prompt engineering** — try this order before fine-tuning:
1. Better system prompt with examples
2. Few-shot examples (5-20)
3. RAG for domain knowledge
4. Only then consider fine-tuning

**Fine-tune when**:
- Prompts plateau — you've exhausted prompt improvements
- You need consistent output formats or tone that prompts can't enforce
- Latency matters and you need to remove lengthy system prompts
- You need behavior that runs against the base model's defaults

**Fine-tuning providers (2025-2026)**:
- **OpenAI fine-tuning**: Easiest path for GPT-4o mini/GPT-4o; good for format/style/domain adaptation
- **Together AI**: Best open-source fine-tuning (Llama, Mistral, etc.) + serving through same API; cheapest at scale
- **Modal**: Python-native serverless GPU for custom training; `@app.function(gpu="H100")` decorator
- **Hugging Face + Axolotl/Unsloth**: Full control, self-hosted; best for research or highly custom setups

**LoRA / QLoRA** for 95%+ of fine-tuning use cases: freeze base model weights, train small low-rank adapter layers. QLoRA adds 4-bit quantization — fine-tune 70B models on a single A100.

---

## AI Coding Assistants (2025-2026 Landscape)

The market has consolidated around two usage patterns: IDE-integrated assistant for daily coding + terminal-based agent for heavy lifting.

| Tool | Best For | Strengths |
|---|---|---|
| **Claude Code** | Complex multi-file changes, hard problems | Largest context window, highest SWE-bench scores, terminal-native; surpassed $2.5B ARR |
| **Cursor** | Daily coding in a purpose-built IDE | Maturest AI IDE ecosystem, tab completion, codebase-aware chat |
| **GitHub Copilot** | Enterprise environments | Already installed/IT-approved, GitHub/Azure DevOps integration |
| **Windsurf** (now OpenAI-owned) | Multi-file refactors with visual navigation | Cascade agent + Codemaps for AI-annotated code navigation |
| **v0 (Vercel)** | Frontend/UI generation from descriptions | React/Next.js components, deploy to Vercel in one click |
| **Bolt / Lovable** | Rapid full-stack prototypes | Full app scaffolding from natural language |

**Pattern used by top developers in 2026**: Cursor or Windsurf for in-editor suggestions; Claude Code for terminal-based autonomous tasks on hard problems.

---

## Multimodal and Voice AI Development

### Vision APIs
All frontier models (Claude, GPT-4o, Gemini) accept image inputs natively. For PDFs: use Claude's Files API or convert to images per page. For structured document extraction (tables, forms), multimodal input + structured output is the current best practice — no specialized OCR pipeline needed.

### Voice (Real-Time)
- **OpenAI Realtime API**: Full-duplex audio streaming, speech-to-speech, GA in 2025. Best for truly interactive, interruptible voice conversations. Under 500ms round-trip for natural feel.
- **ElevenLabs**: Best voice quality TTS, now supports multimodal conversational AI. Use for high-quality voice output where latency is secondary.
- **Deepgram**: Best STT (speech-to-text) API, low latency, good at domain-specific vocabulary.
- **Architecture**: Audio capture → Deepgram STT → LLM → ElevenLabs TTS for pipeline-based voice; OpenAI Realtime API for true end-to-end voice.

**Voice UX requirement**: audio → text → reasoning → text → audio in under 500ms to feel natural. This requires streaming architectures that process in chunks, not after full completion.

### Video Understanding
GPT-4o and Gemini support video frames natively. For real-time video analysis, use WebRTC to stream frames to vision APIs. The multimodal Live API (Google) allows real-time tool triggering based on video events.

---

## Human-in-the-Loop Patterns

For agentic systems, build human oversight into the architecture from day one:

1. **Approval gates**: For high-stakes actions (API calls with side effects, emails, database writes), pause the agent and require human confirmation before execution. LangGraph checkpoints make this native.
2. **Confidence thresholds**: Route low-confidence outputs to human review; high-confidence outputs run automatically.
3. **Audit trails**: Log every agent decision with the context that drove it. Non-negotiable for enterprise and regulated use cases.
4. **Graceful degradation**: If the AI fails or produces low-quality output, fall back to a simpler response or human handoff rather than surfacing an error.
5. **Feedback capture**: Show thumbs up/down or inline correction UI. Feed corrections back into fine-tuning datasets or few-shot examples.

**Human roles shift from operators to supervisors** — focus human effort on edge cases, ethical judgment, and system oversight, not routine tasks.

---

## Reference Files

For deeper guidance on specific areas, read the relevant reference file:

- **`references/rag-and-retrieval.md`** — Vector database selection, embedding models, chunking strategies, hybrid search, reranking, advanced patterns (GraphRAG, HyDE, RAPTOR, self-RAG, contextual retrieval). Read when the user is building a knowledge base, document Q&A, or search system.

- **`references/agents-and-frameworks.md`** — LangGraph architecture patterns, multi-agent coordination, MCP server development, agent memory systems, tool use patterns, CrewAI vs. LangGraph decision guide. Read when building autonomous agents or complex multi-step workflows.

- **`references/ops-eval-security.md`** — LLM observability platforms (LangSmith, Langfuse, Arize), evaluation frameworks (DeepEval, RAGAS, Braintrust, Promptfoo), cost optimization strategies, prompt injection defenses, red teaming, self-hosted inference (vLLM vs TGI), model deployment (Modal, Replicate, Baseten). Read when productionizing AI systems, debugging costs, or implementing security.
