# AI Cost Economics — The Decision: "When does self-hosted beat API, and at what hidden cost?"

This reference answers exactly one decision: **at what monthly token volume does self-hosting beat API, and what hidden costs determine whether the migration is worth it?**

Pair with `scripts/ai_cost_economics.py` for automation.

## The Mental Model

API cost is **fully variable**: linear in token volume, zero fixed cost.

Self-hosted cost is **mostly fixed**: warm GPUs cost the same whether you process 1M or 1B tokens. The marginal cost of additional tokens approaches the marginal electricity + amortization cost, which is small.

The crossover happens where API variable cost exceeds the self-hosted fixed floor. **For 70B-class models on rented A100s, this is typically 1–10 billion tokens per month** depending on which API tier you're comparing against and what GPU pricing you can negotiate.

## 2026 API Pricing (illustrative; verify quarterly)

Per million tokens, USD:

| Tier | Example models | Input | Output |
|---|---|---|---|
| Frontier-premium | Claude Sonnet 4.6, GPT-4o-tier | $3.00 | $15.00 |
| Frontier-economy | Gemini 2.5 Flash, Claude Haiku 4.5-tier | $1.25 | $5.00 |
| Open-hosted | Llama 3.1 70B / Qwen 2.5 72B via Together, Fireworks, OpenRouter | $0.50 | $1.50 |
| Open-economy | 8B-13B-class hosted | $0.10 | $0.30 |

**Caveats:**
- Frontier pricing dropped ~10x from 2023 to 2026 and continues to drop. Pin your TCO to current pricing only.
- Provider rate limits matter: Tier 1 customers get throttled at QPS spikes; Tier 4+ (~$10K+/mo commitment) get burst capacity.
- Long-context surcharge: requests >100K tokens often charged differently.
- Caching: most providers offer prompt caching at 50-90% discount on cached tokens. Significantly changes economics for repeated system prompts.

## Self-Hosted Inference Economics

### GPU Rental Pricing (2026 spot, $/hour)

| GPU | Low | Mid | High |
|---|---|---|---|
| A100 (40/80GB) | $1.50 | $2.50 | $3.50 |
| H100 (80GB) | $3.50 | $5.00 | $8.00 |
| H200 (141GB) | $5.00 | $7.50 | $12.00 |
| B200 (192GB, limited availability) | $8.00 | $14.00 | $22.00 |

Pricing varies by provider (AWS, GCP, Azure, Lambda, RunPod, Coreweave, Crusoe, etc.), commitment (spot, on-demand, reserved 1-yr, reserved 3-yr), and geographic region.

### How Many GPUs Do You Need?

Per model size, minimum to serve at frontier-equivalent quality:

| Model class | A100-80GB | H100 | Why |
|---|---|---|---|
| 7B-13B | 1 | 1 | Fits in single GPU memory |
| 70B-class (fp16) | 4 | 2 | ~140GB weights + KV cache |
| 405B-class | 8 | 4 | Multi-GPU tensor parallelism |
| Mixture-of-Experts (e.g., Mixtral 8x22B active) | 4 | 2 | Sparse routing reduces active params |

### Throughput (tokens/sec/GPU at 70% utilization)

| Model class | A100 | H100 |
|---|---|---|
| 7B-13B | ~1,500 | ~3,500 |
| 70B-class | ~200 | ~600 |

### Cost Per Million Tokens (rough)

70B-class on rented A100s at $2.50/hr × 4 GPUs at 70% utilization = $10/hr for 4 × 200 × 0.7 × 3600 tokens/hr = ~2M tokens/hr → **$5/M tokens.**

70B-class on rented H100s at $5/hr × 2 GPUs at 70% utilization = $10/hr for 2 × 600 × 0.7 × 3600 tokens/hr = ~3M tokens/hr → **$3.30/M tokens.**

Compare to API frontier-economy at $1.25/$5 input/output → blended ~$2.50/M tokens for typical 4:1 input:output ratio.

**Bottom line:** self-hosted 70B-class is roughly equivalent to or slightly more expensive than frontier-economy API at the per-token level. The "savings" only appear when self-hosted is highly utilized AND the alternative is frontier-premium API.

## Utilization Reality Check

The 70% utilization assumption above is **optimistic**. Realistic utilization patterns:

- **Continuous batch workload** (e.g., async classification): 60-80% achievable with proper batching
- **User-facing interactive (chat):** 20-40% typical — bursty demand, idle time between user turns
- **Mixed workload:** 30-50%

If your utilization is 30% instead of 70%, your effective cost per token roughly doubles. Plan for utilization explicitly.

## Hidden Costs of Self-Hosted

### 1. Ops On-Call
- 24/7 on-call rotation requires ≥3 engineers
- Pager duty for inference outages
- Realistic attribution: 30% of one engineer (~$75K/yr fully-loaded)
- At scale: dedicated MLOps team

### 2. Monitoring & Observability
- Token throughput, latency p50/p95/p99
- Quality monitoring (drift, hallucination rate vs eval set)
- GPU health, memory pressure, OOM events
- Cost monitoring (idle GPU detection)
- **Budget:** $5-20K/mo in tooling (Datadog, Honeycomb, custom)

### 3. Model Updates
- Open-weights models release new versions every 3-6 months
- Each update requires re-evaluation against your eval set
- Quality regressions are common; rollback path required
- **Budget:** 1-2 engineer-weeks per quarter

### 4. Capacity Planning
- Warm GPUs must serve peak QPS, not average
- 2-3x over-provisioning typical for user-facing workloads
- Auto-scaling exists but has 5-10 minute lag for GPU warm-up

### 5. Failover & Redundancy
- Single-region self-hosting is a single point of failure
- Multi-region adds 2x capex
- Or: hybrid with API failover (best of both, but requires routing logic)

### 6. Security & Compliance
- Self-hosted = you own the security boundary
- SOC 2 / ISO 27001 scope expands to inference infrastructure
- Model weights protection (worth $$ if fine-tuned proprietary)

## Hidden Costs of API

### 1. Vendor Lock-In
- Migration to another provider: 2-8 weeks of engineering work
- Output format differences, prompt sensitivity differences
- Mitigation: abstraction layer (LiteLLM, OpenRouter, Portkey) — $100-500/mo + engineering time

### 2. Capability Drift
- Provider updates models silently or with brief notice
- Your prompts may produce different outputs after upgrade
- Mitigation: pin model IDs (e.g., `claude-sonnet-4-6` vs `claude-sonnet-latest`)
- Cost: regression eval runs on every model swap

### 3. Rate Limits
- Default tiers throttle aggressively
- Burst capacity requires Tier 4+ commitment ($10K+/mo)
- Mitigation: multi-vendor load balancing (failure path: degraded quality)

### 4. Long-Context Pricing
- Many providers charge differently above 100K-200K context
- 1M-token context (Gemini, Claude) priced higher per token

### 5. Data Residency
- EU customers may require EU-only inference (Claude EU, Azure OpenAI EU regions, Vertex EU)
- Limits provider options

### 6. Privacy / Training Data Use
- Default provider TOS often allows training on your inputs
- Enterprise / business contracts disable this (zero retention available from major providers)
- Mitigation: enterprise contract; verify zero-retention clause

## Migration Cost: API → Self-Hosted

Realistic engineering effort for a production migration:

| Phase | Effort |
|---|---|
| Inference platform setup (vLLM, TGI, TensorRT-LLM) | 4-6 weeks |
| Model deployment + benchmarking | 2-3 weeks |
| Eval harness rebuild (different model = different eval) | 2-4 weeks |
| Production rollout with shadow traffic | 4-8 weeks |
| Monitoring + on-call setup | 2-4 weeks |
| **Total** | **3-6 months, 2-3 engineers** |

At fully-loaded $250K/engineer/yr, migration cost is ~$150-300K in engineering time alone, plus migration risk (regressions, latency spikes during rollout).

**Implication:** migration should pay back in 12-18 months of cost savings, OR provide a strategic capability (data residency, capability not in API).

## Decision Heuristics

### Stay with API when:
- Monthly cost < $50K
- Volume < 500M tokens/month
- Latency p95 acceptable at API levels
- No compliance forcing self-host
- ML team < 3 engineers

### Consider hybrid when:
- $50K-$500K/mo API spend
- Some workloads have predictable high volume (good for self-host)
- Some workloads have bursty / low-volume (good for API)
- Have ML platform engineer in seat

### Migrate to self-hosted when:
- > 500M tokens/month on stable workload
- $250K+/mo API spend
- Data residency / sovereignty requires it
- Have 2+ ML engineers and 1 platform engineer
- 3-6 month migration capacity available
- Multi-year stable workload (don't migrate if you're pivoting)

### Hybrid is often the right answer.

## Prompt Caching: The Underrated Lever

Most major providers (Anthropic, OpenAI, Google) offer prompt caching: cached input tokens cost 10-50% of normal.

**When it dominates economics:**
- Repeated system prompt across queries (typical for agents, RAG)
- Large context with small variable suffix
- Multi-turn conversations

**Realistic savings:** 30-70% reduction in input token costs for cache-friendly workloads. Often makes self-host migration unnecessary by closing the cost gap.

## Failure Modes

### API failure modes
- **Vendor outage during peak hours** — multi-vendor failover required for B2B SaaS SLAs
- **Capability degradation between versions** — pin model IDs and run regressions
- **Rate limit surprise** — Tier 1 customers get throttled; commit to higher tier

### Self-hosted failure modes
- **Quality regression on model update** — invisible without eval set
- **GPU spot price spike** — convert to reserved capacity for predictability above $20K/mo
- **Idle GPU bleeding cash** — auto-shutdown / dynamic scaling required
- **Out-of-memory at peak** — KV cache pressure during long-context burst

## When This Reference Doesn't Help

- **Tactical inference optimization (quantization, speculative decoding, vLLM tuning).** See `engineering/llm-cost-optimizer/`.
- **Prompt caching implementation.** See `engineering/prompt-governance/`.
- **Multi-vendor abstraction implementation.** See `engineering/agent-designer/` and LiteLLM/OpenRouter docs.

This reference is about strategic economics and the migration decision, not tactical implementation.

---

**Source authorities (non-exhaustive):**

- Kwon et al., "Efficient Memory Management for Large Language Model Serving with PagedAttention" (vLLM, 2023)
- "DistServe: Disaggregating Prefill and Decoding for Goodput-optimized LLM Serving" (NSDI 2024)
- Stanford HELM benchmark — public LLM cost / quality / latency tracking
- Artificial Analysis (artificialanalysis.ai) — independent LLM pricing and performance tracking
- Anthropic, OpenAI, Google Cloud, AWS Bedrock pricing pages (verify current)
- Together AI, Fireworks, OpenRouter, Replicate pricing pages (verify current)
- "Llama 3.1: Open Foundation and Instruction Models" — model performance vs frontier benchmarks
- Lambda Labs, Coreweave, Runpod GPU pricing pages (verify current; spot pricing is volatile)
