# Build vs Buy vs Wrap: Decision Guide

## Decision Tree

Use these questions in sequence to classify each use case:

```
1. Is there an off-the-shelf foundation model API that solves 80%+ of this?
   YES → Is there a data privacy / sovereignty constraint preventing API usage?
         NO → WRAP (use the API, add integration layer)
         YES → Can a self-hosted open model (Llama, Mistral) fill the gap?
               YES → WRAP (self-hosted)
               NO → FINE-TUNE

   NO → Is there a vertical SaaS product purpose-built for this use case in this domain?
        YES → EVALUATE BUY (check: does it integrate, can data stay in-boundary, is cost justified?)
        NO → Does the use case require proprietary training data to be meaningfully differentiated?
             YES → Is the org at Tier 3 readiness?
                   YES → BUILD (custom model training)
                   NO → FINE-TUNE on a foundation model with proprietary data
             NO → Is this a known ML task with off-the-shelf model types?
                  YES → WRAP or FINE-TUNE
                  NO → Research spike needed before deciding
```

---

## Sourcing Options Explained

### WRAP — Use a Foundation Model API
Best for: LLM-based tasks (summarization, generation, extraction, classification, Q&A, RAG)
Effort: Low (weeks)
Risk: Vendor dependency, latency, cost at scale, data privacy

**Suitable APIs:**
- **Anthropic Claude** — Long-context reasoning, document analysis, complex Q&A, code
- **OpenAI GPT-4o** — Multimodal, function calling, structured outputs
- **Google Gemini** — Multimodal, long context, Google ecosystem integration
- **Cohere** — Enterprise search, embeddings, RAG
- **Mistral / Llama (self-hosted)** — When data cannot leave the org

**When WRAP is right:**
- Use case is primarily text in / text out
- Prompt engineering alone gets you to 80%+ quality
- Volume is moderate (API cost is acceptable)
- Time to value is critical

---

### BUY — Procure a Vertical SaaS AI Tool
Best for: Specific, well-defined use cases in established categories
Effort: Low to Medium (procurement + integration, weeks to months)
Risk: Vendor lock-in, limited customization, data sharing with third party

**Category → Vendor Examples:**
| Category | Vendors to Evaluate |
|---|---|
| Enterprise search / knowledge | Glean, Guru, Notion AI, Confluence AI |
| Call analytics / conversation intelligence | Observe.AI, Gong, Chorus |
| Support ticket deflection | Intercom AI, Zendesk AI, Freshdesk Freddy |
| Sales intelligence / lead scoring | Clari, 6sense, Apollo AI |
| Document processing (IDP) | Hyperscience, Instabase, AWS Textract + Comprehend |
| Code review / security scanning | Snyk, GitHub Copilot, Veracode |
| Recruiting / HR AI | HireVue, Eightfold.ai, Ashby AI |
| BI / analytics copilot | Tableau AI, ThoughtSpot, Sigma AI |
| Personalization engine | Braze, Iterable, Dynamic Yield |
| Fraud detection | Sardine, Sift, Stripe Radar |

**When BUY is right:**
- A mature vendor already solves the exact problem
- Customization needs are low
- Speed to value > customization
- Org does not want to maintain ML infrastructure

---

### FINE-TUNE — Adapt a Foundation Model on Proprietary Data
Best for: When a base model is close but domain-specific performance matters
Effort: Medium (1–4 months)
Risk: Training cost, ongoing maintenance, data quality dependency

**Good candidates for fine-tuning:**
- Classification tasks with proprietary taxonomy
- Domain-specific generation (medical notes, legal docs, financial reports)
- Tone/style adaptation for brand-specific generation
- When base model hallucination rate on domain content is too high

**Fine-tuning platforms:**
- OpenAI fine-tuning API (GPT-4o mini fine-tuning)
- Anthropic fine-tuning (where available)
- Hugging Face + PEFT/LoRA (self-hosted)
- AWS Bedrock fine-tuning
- Google Vertex AI fine-tuning

**Data requirements for fine-tuning:**
- Minimum: ~500–1000 labeled examples for classification
- Recommended: 5,000–50,000 for generative tasks
- Must be representative of production distribution

---

### BUILD — Train a Custom Model from Scratch
Best for: Proprietary problems where no existing model architecture applies
Effort: High (6–18 months minimum)
Risk: High — talent, compute, data, time, ongoing maintenance

**Only recommend BUILD when:**
- The use case is core IP and differentiation
- Org is Tier 3 (dedicated ML team, MLOps, data infrastructure)
- Proprietary data is the competitive moat
- Off-the-shelf models have been evaluated and are genuinely insufficient
- The problem type is non-standard (novel architecture needed)

**Common BUILD scenarios:**
- Custom recommendation engines on proprietary behavioral data
- Anomaly detection on proprietary time-series (very domain-specific signals)
- Multimodal models on proprietary image + metadata combinations
- Real-time fraud models requiring sub-50ms inference at high scale

---

## Cost Benchmarks (Order of Magnitude)

| Sourcing | Prototype Cost | Production Year-1 Cost | Ongoing/Year |
|---|---|---|---|
| Wrap (LLM API) | $0–$5K | $10K–$100K (depends on volume) | API costs + eng |
| Buy (SaaS) | $0 (trial) | $50K–$500K (enterprise contract) | License renewal |
| Fine-tune | $10K–$50K | $50K–$200K | Retraining + hosting |
| Build (custom) | $50K–$200K | $500K–$2M+ | Team + infra |

Use these as conversation-starters, not quotes. Actual costs vary significantly.