# Model Build-vs-Buy — The Decision: "API, fine-tune, or build?"

This reference answers exactly one decision per use case: **should we call a frontier API, fine-tune a smaller model, or build from scratch?**

Pair with `scripts/model_buildvsbuy_calculator.py` for use-case-specific TCO.

## The Three Paths

### Path 1: Frontier API (default, 80% of use cases)

**What it is:** Call Claude, GPT, Gemini, or similar via API. Pay per token. No infrastructure.

**Use when:**
- Use case is well-served by general capability (chat, summarization, classification, code, writing)
- QPS < 100/sec sustained
- Latency budget > 1 second
- No data residency constraints
- Monthly cost < $50K at current volume
- Team has 0-1 ML engineers

**Why it dominates at startup scale:**
- Frontier APIs in 2026 are 10–100x more capable than any in-house fine-tune. Model cards show Claude 3.5 Sonnet, GPT-4o, and Gemini 2.5 outperform fine-tuned Llama 3.1 70B on most reasoning benchmarks by 20–40 points.
- Zero infrastructure overhead. No GPUs, no MLOps, no on-call.
- Pay-as-you-go scales linearly; no capacity planning.
- Vendor handles security patches, weight updates, alignment improvements.

**Failure modes:**
- **Vendor lock-in.** Mitigation: use abstraction layer (LiteLLM, OpenRouter, Portkey) so you can swap providers in days, not months.
- **Capability drift between versions.** Mitigation: pin model IDs; run regression evals before upgrading.
- **Rate limits at QPS spikes.** Mitigation: confirm Tier-4+ pricing with the provider; pre-arrange burst capacity.
- **Cost growth.** Below $50K/mo it's noise; above $200K/mo, revisit fine-tune. Above $1M/mo, revisit self-hosted.
- **Data residency.** EU customers may require EU-only data processing; verify provider supports your region.

**Anti-patterns:**
- "We need privacy, so we have to self-host." Almost always false at startup scale. Use enterprise contracts with zero-retention provisions instead.
- "Frontier APIs are too expensive." Run the math. Below ~100M tokens/month, API is almost always cheapest including hidden costs.

### Path 2: Fine-tune a smaller open model (the 15% case)

**What it is:** Take an open-weights model (Llama 3.1 70B, Qwen 2.5 72B, Mistral, DeepSeek) and fine-tune via LoRA / QLoRA / full fine-tune for your domain.

**Use when:**
- Domain-specific behavior the API can't be prompted into (medical coding patterns, legal redlining style, regulated terminology)
- Latency budget < 500ms sustained (frontier APIs typically p95 at 600-1500ms for non-trivial responses)
- High volume (>500M tokens/month) where TCO favors fine-tune
- Labeled data available (≥10K high-quality examples typical for LoRA)
- ML engineering capacity (≥2 engineers comfortable with HuggingFace, vLLM, fine-tuning loops)

**Fine-tuning approaches (from least to most invasive):**

| Approach | What it changes | When to use | Cost |
|---|---|---|---|
| Few-shot prompting | Nothing (in-context) | First attempt, always | $0 setup |
| Prompt engineering + system prompt | Nothing | When few-shot insufficient | $0 setup |
| RAG (retrieval-augmented) | Adds knowledge, not behavior | When you need facts, not style | $5-50K setup |
| LoRA fine-tuning | Adapter weights only | Behavior + style adjustments | $10-50K |
| Full fine-tuning | All weights | Major behavioral shift | $50-200K |
| RLHF / DPO | Alignment to preferences | Subjective quality (writing, support) | $100-500K |
| Continued pre-training | Domain knowledge baked in | Truly novel domain (medical, scientific) | $500K-5M |

**Failure modes:**
- **Quality lags frontier by ~6 months.** Frontier model improvements outpace your fine-tune cycle. Plan for refresh every 12-18 months.
- **Retraining cadence is a recurring engineering cost.** Quarterly retraining typical; budget 30% of one ML engineer.
- **Without an eval set, fine-tune drift is invisible.** You won't know quality degraded until a customer complains.
- **Inference is your problem now.** Fine-tuned models often run via hosted inference (Together, Fireworks, Replicate) for $0.50-2.00/M tokens; self-host adds operational complexity.

**Anti-patterns:**
- "Fine-tune to get better results." If frontier API is already at 90%+ accuracy, fine-tune to a smaller model usually drops it to 80-85%. The "better results" framing is backwards.
- "Fine-tune to save money." Only economically valid at high volume (>500M tokens/mo); below that, API wins even at frontier-premium pricing.

### Path 3: Build from scratch / pre-train (the <1% case)

**What it is:** Train a foundation model from scratch.

**Use when:** Almost never. Only:
- You are a foundation-model company (Anthropic, OpenAI, Cohere, Mistral, DeepSeek, etc.).
- You have a uniquely valuable corpus + $50M+ funding + 18-month patience.
- Your moat IS the model.

**Why it rarely makes sense:**
- Frontier models have caught up to specialized models in most domains within 18 months (medical, legal, code).
- By the time you ship, frontier capability has advanced 2 generations.
- Pre-training cost: $5M-50M+ depending on model size and data.
- Hidden cost: continued pre-training and alignment to keep up.

**Failure modes:**
- **Sunk cost trap.** Once you've spent $20M pre-training, sunk cost bias prevents switching to frontier APIs even when they're better.
- **Talent dependency.** Pre-training requires research scientists who can leave for $1M+ TC at frontier labs.
- **Compute access.** H100 / B200 supply remains constrained; access depends on hyperscaler relationships.

## Decision Tree (use the calculator for the full version)

1. **Is this well-served by frontier capability?** (YES → API, unless...)
2. **Do you have data residency / sovereignty constraints?** (YES → fine-tune self-hosted)
3. **Do you have domain-specific behavior the API can't be prompted into?** (YES + labeled data + team → fine-tune)
4. **Latency budget < 500ms?** (YES → fine-tune at high volume; API + streaming may suffice at lower volume)
5. **Volume > 500M tokens/month + multi-year stable workload?** (YES → run breakeven, consider fine-tune)
6. **All above NO + need maximum capability?** → API frontier-premium tier

## The Eval-First Discipline

**Rule:** Don't pick a path without an eval set. Without measurement, all three paths look the same.

Minimum eval set:
- 50-100 representative inputs covering your use case
- Expected outputs OR rubric for human grading
- Edge cases: ambiguous inputs, adversarial inputs, format edge cases
- Run on every path you consider; the scores determine the decision

Tools: `engineering/self-eval/`, `promptfoo`, `Inspect-AI`, internal eval harnesses.

## When This Reference Doesn't Help

- **RAG architecture choices.** See `engineering/rag-architect/`.
- **Agent design patterns.** See `engineering/agent-designer/`.
- **Prompt engineering technique.** See `engineering/prompt-governance/`.
- **Eval harness implementation.** See `engineering/self-eval/`.
- **Inference cost optimization tactics.** See `engineering/llm-cost-optimizer/`.

This reference is about the strategic choice between API / fine-tune / build, not how to implement any of them.

---

**Source authorities (non-exhaustive):**

- Anthropic, "Model Cards for Claude 3.5 Sonnet, Claude 4 family" — published model performance and capability disclosures
- OpenAI, "GPT-4 Technical Report" (arXiv:2303.08774, 2023) and subsequent model spec releases
- Google DeepMind, "Gemini: A Family of Highly Capable Multimodal Models" (2023, updated 2024-2026)
- Meta AI, "Llama 3.1: Open Foundation and Instruction Models" (2024)
- Hu et al., "LoRA: Low-Rank Adaptation of Large Language Models" (arXiv:2106.09685, 2021)
- Ouyang et al., "Training Language Models to Follow Instructions with Human Feedback" (RLHF, 2022)
- Rafailov et al., "Direct Preference Optimization: Your Language Model is Secretly a Reward Model" (DPO, 2023)
- Stanford CRFM, "On the Opportunities and Risks of Foundation Models" (2021)
- Henderson et al., "Foundation Models and Fair Use" (2023)
