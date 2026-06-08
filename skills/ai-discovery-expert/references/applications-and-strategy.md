# AI Applications, Strategy, and Safety Reference

## AI Use Case Discovery Framework

### High-ROI Use Case Categories

Based on enterprise deployments (McKinsey, BCG, MIT data 2024-2026):

**1. Repetitive Text Processing** (Highest ROI, fastest to deploy)
- Document classification and routing
- Contract extraction and review
- Receipt/invoice processing
- Support ticket categorization
- Regulatory compliance checking
- Build approach: API-based; prompt engineering + structured outputs; no fine-tuning needed typically
- Expected ROI: 60-80% cost reduction on task; 2-4 week deployment

**2. Code Acceleration** (High ROI, fast adoption)
- AI pair programming (GitHub Copilot, Cursor, Claude in IDE)
- Code review automation
- Test generation
- Documentation generation
- Bug detection (especially security scanning)
- Data: 25-43% developer productivity gains reported; PR merge volume up 23% YoY
- Build approach: Use existing tools (Copilot, Cursor) before building custom; integrate AI code review into CI/CD

**3. Internal Knowledge Q&A / RAG** (Medium-high ROI)
- HR policy questions
- IT support first-line
- Sales enablement / product knowledge
- Legal research assistance
- Build approach: RAG over internal documents; requires investment in data quality and chunking strategy
- Common failure: Bolting RAG on without designing retrieval first; 70%+ of RAG implementations fail in production

**4. Customer-Facing Applications** (High ROI if done right)
- Customer support automation (deflection + escalation)
- Product recommendation
- Onboarding personalization
- Self-service knowledge base
- Risk: Hallucination in customer-facing context is costly; requires strong grounding and confidence thresholds

**5. Decision Augmentation** (Medium ROI, longer cycle)
- Risk scoring with AI explanation
- Demand forecasting with anomaly explanation
- Fraud detection with case narratives
- Build approach: Often ML model (prediction) + LLM (explanation); separate concerns

**6. Content Generation at Scale** (High ROI for marketing/content teams)
- Product descriptions (e-commerce scale)
- Marketing copy variants for A/B testing
- Localization assistance
- Personalized email campaigns
- Data: Human-AI hybrid workflow delivers ~60% cost reduction vs. human-only

### Use Case Prioritization Matrix

Score each use case on:
- **Business impact**: Revenue, cost, risk, or customer experience impact (1-5)
- **Feasibility**: Data availability, technical complexity, regulatory constraints (1-5)
- **AI readiness**: Is this task well-defined? Consistent? Evaluable? (1-5)

High-scoring use cases on all three dimensions = start here.

**Tasks AI does well**: Pattern recognition in structured data, text classification, information extraction, code generation, summarization, translation, search/retrieval
**Tasks AI does poorly**: Novel reasoning in completely new domains, tasks requiring physical world grounding, anything requiring up-to-date knowledge without RAG, high-stakes single decisions without human oversight

### Discovery Process
1. Interview domain experts: "What tasks do you do repeatedly that are tedious?"
2. Map information flows: Where does text/data get processed by humans?
3. Identify bottlenecks: Where do things queue up waiting for human review?
4. Assess task clarity: Can you write a rubric for what "good" looks like?
5. Check data availability: Do you have examples of good/bad outputs?
6. Estimate volume and frequency: High volume + repetitive = stronger AI ROI case

---

## ROI Analysis for AI Implementations

### Cost Model Components

**Development cost**:
- Engineering time (typically 2-8 weeks for a focused API-based feature; 3-6 months for a full platform)
- Data labeling (if fine-tuning: $1-10 per labeled example; budget for at least 1,000 examples)
- Infrastructure setup (typically $5K-50K one-time for most implementations)

**Ongoing cost**:
- API costs (model inference): Size × price per token × volume
- Infrastructure maintenance: Embedding pipeline, vector database, monitoring
- Human review and quality assurance (often underestimated)
- Compliance and audit overhead

**Benefit calculation**:
- Time saved × loaded labor rate × volume
- Error rate reduction × cost per error
- Throughput increase (if constraining resource is automated)
- Customer satisfaction improvement → retention value

### Common ROI Mistakes
1. **Ignoring integration cost**: The model is 20% of the work; integration is 80%
2. **Ignoring maintenance**: Models drift, prompts need updating, data pipelines break
3. **Overestimating automation rate**: Expect 60-80% automation in a good case; 20-40% is realistic for complex tasks
4. **Underestimating error cost**: A 95% accuracy model makes 1 error per 20 outputs — acceptable for some tasks, catastrophic for others
5. **Ignoring change management**: BCG: only 5% of organizations achieve AI value at scale; bottleneck is adoption, not technology

### Benchmark Stat
- Organizations following top 4 AI best practices: median ROI 55% on GenAI
- Companies buying specialized AI tools: 67% success rate
- Companies building everything in-house with limited expertise: 33% success rate
- MIT 2025: 95% of generative AI pilots are failing (mostly due to wrong use cases or insufficient change management)

---

## Build vs. Buy vs. API Decision Framework

### Decision Tree

**Start here: Is this use case strategic and differentiating?**

If NO → Buy a specialized SaaS tool:
- Examples: Jasper for marketing, Harvey for legal, Glean for enterprise search
- When: Standard use case, team lacks ML expertise, time-to-value matters most
- Tradeoff: Less control, vendor dependency, data privacy concerns, recurring cost

If YES → Continue: Do you need custom behavior beyond what prompting achieves?

If NO → Use foundational model APIs:
- OpenAI, Anthropic, Google APIs with prompt engineering + RAG
- When: Most enterprise use cases fall here; highly customizable without ML expertise
- Tradeoff: Per-token cost scales with volume; vendor concentration risk

If YES → Continue: Do you have >1,000 labeled examples and ML engineering capacity?

If NO → Start with API + few-shot prompting, build labeled dataset, revisit
If YES → Fine-tune open-source model:
- LoRA on Llama/Mistral/Qwen with your data
- Deploy on dedicated infrastructure (Modal, Together AI, Replicate, self-hosted)
- When: Cost at scale, latency requirements, data privacy, unique domain
- Tradeoff: ML engineering investment; ongoing maintenance; model updates manual

If you need to control training data completely → Train from scratch:
- Almost never justified unless you're a frontier lab or have genuinely unique data at 100B+ token scale

### Open vs. Closed Model Decision

| Factor | Favors Closed (API) | Favors Open (Self-hosted) |
|--------|--------------------|--------------------|
| Capability | Best overall frontier capability | Strong open models closing gap |
| Cost at scale | Expensive at high volume | Fixed infrastructure cost |
| Data privacy | Data sent to third party | Data stays on-premise |
| Maintenance | Zero; provider handles updates | Significant; own updates/monitoring |
| Latency | Variable; network-dependent | Predictable; local hardware |
| Compliance | SOC2/HIPAA available from major providers | Full control |
| Fine-tuning | Limited (some providers offer) | Full control |
| Team expertise | No ML expertise needed | ML engineering required |

**Rule of thumb**: Start with APIs (Claude, GPT-5, Gemini). Move to open models when: (1) monthly API bill exceeds $5-10K and use case is stable, (2) data privacy requirements prohibit third-party APIs, or (3) you need deep customization.

---

## Technology Radar for AI Tools

### The Thoughtworks Methodology (Adapted for AI)

Rate each tool/technology in four rings:

**Adopt** — Proven and mature; use now without reservations
- Examples (mid-2026): LangGraph for agentic orchestration, RAGAS for RAG evaluation, Ollama for local model serving, PromptFoo for prompt testing

**Trial** — Ready to use but not fully proven; test in bounded scope
- Examples: Newer reasoning models in agentic workflows, computer-use agents for RPA replacement, fine-tuned smaller models for specialized tasks

**Assess** — Watch closely; not ready to trial unless you're a perfect fit
- Examples: Multimodal video understanding in production, autonomous AI scientists, embodied robotics AI

**Hold** — Avoid or reconsider; problematic patterns
- Examples: Training from scratch for most use cases, single-model without fallback in production, trusting benchmark numbers without custom evaluation, LLM for sole decision-making in high-stakes contexts without human oversight

### Building Your Domain-Specific Radar

1. **Inventory phase**: Collect all AI tools in the domain
   - Product Hunt, GitHub trending, Hugging Face Spaces
   - G2/Capterra/Gartner Peer Insights for enterprise tools
   - Conference demos and workshops
   - Competitor product teardowns

2. **Classify phase**: Apply four-ring methodology
   - Assess based on: maturity, vendor stability, community size, your team's capability to adopt
   - Don't just use Gartner ratings — they lag the actual frontier by 12-18 months

3. **Evaluate phase**: Run PoCs on Trial-ring candidates
   - 2-week PoC minimum; test on your actual data
   - Measure: capability, latency, cost, reliability, integration effort

4. **Publish and update**: Share radar with team; update quarterly (AI moves too fast for annual)

### Vendor Evaluation Dimensions

For any AI vendor/tool:
1. **Capability fit**: Can it actually do your task? Test empirically — don't trust demos.
2. **Reliability/SLA**: Uptime guarantees? Latency p99? Fallback options?
3. **Cost model**: Per-token, per-seat, or flat? How does it scale with your volume?
4. **Data handling**: Where does your data go? Training? Privacy policy?
5. **Vendor stability**: Funding runway? Enterprise contracts? Customer base?
6. **Integration**: REST API? SDKs in your language? Webhook support?
7. **Compliance**: SOC2? HIPAA if healthcare? GDPR if EU users?
8. **Open vs. locked**: Can you export your data? Switch vendors? Is there a standard API?

---

## Competitive AI Intelligence

### Methodology

**What to monitor for competitors**:
1. **Product feature tracking**: New AI features in product releases; job postings (AI/ML roles signal where they're investing); patent filings
2. **Model capability inference**: Public demos, API terms, accuracy claims (reverse-engineer through testing)
3. **Pricing signals**: Pricing page changes; enterprise contract terms (via analyst reports, customer references)
4. **Research output**: Papers published by competitor researchers; conference presentations; blog posts
5. **Partnership signals**: Cloud provider announcements; model provider partnerships; data licensing deals

### Tools

**Klue**: Market leader in competitive enablement. "Compete Agent" (launched 2025) delivers real-time competitive deal intelligence to sellers. Automated battlecard generation and updates. Best for: sales enablement, win/loss analysis.

**Crayon**: Automated competitor website tracking — monitors pricing pages, product messaging, job listings. First CI-specific MCP server (launched Sept 2025) for AI tool integration. Best for: marketing and product teams monitoring messaging changes.

**Unkover**: AI-native competitive intelligence. Monitors across digital presence. Good for smaller teams.

**Kompyte**: Similar to Crayon; acquired by Semrush. Best for: companies already in Semrush ecosystem.

**DIY approach**: 
- ChangeDetection.io for webpage monitoring
- Google Alerts for company name + "AI" + "launch"
- LinkedIn company page follower for job trends
- AppFollow/SensorTower for app review sentiment tracking

### Industry Adoption Stats (2025-2026)
- 72% of companies use AI for competitor tracking
- Market growing from $4.8B (2020) to $11.6B (2025)
- 60% of CI teams use AI daily (up from 48% in 2024)

### Ethical Boundaries
Competitive intelligence is legal and valuable. Avoid:
- Scraping protected content in violation of ToS
- Monitoring competitor employees' personal social media
- Reverse-engineering proprietary data through prompt injection or other technical means
- Misrepresenting yourself to access competitor information

---

## AI Safety and Alignment Landscape

### Core Alignment Techniques

**RLHF (Reinforcement Learning from Human Feedback)**
- Process: Supervised fine-tuning → train reward model from human preference data → PPO optimization against reward model
- Used by: OpenAI (InstructGPT), Anthropic, Google DeepMind
- Strength: Powerful at shaping model behavior toward human preferences
- Weakness: Expensive (human labelers), reward hacking (model exploits reward model loopholes), preference data biases

**Constitutional AI (Anthropic)**
- Process: Define a "constitution" of principles → train model to evaluate its own outputs against principles → RLHF from AI feedback
- Key insight: Reduces need for human feedback at scale; model critiques itself
- Published Anthropic's 80-page constitution (Jan 2026) explaining philosophical foundations
- Enables RLAIF (using AI feedback instead of human feedback for alignment)

**DPO (Direct Preference Optimization)**
- 2023 paper; significant shift from RLHF
- Directly optimizes for preferences without separate reward model training
- Simpler, cheaper, more stable than PPO-based RLHF
- Becoming the standard for many alignment fine-tuning tasks
- Weakness: Can be more brittle than RLHF for very complex behavior

**RLAIF (Reinforcement Learning from AI Feedback)**
- Uses AI (often stronger model) to generate feedback instead of humans
- Google DeepMind: RLAIF can match or exceed RLHF performance at dramatically lower cost (2024)
- Risk: Inherits biases of the evaluating model; feedback loops if model evaluates itself
- Curriculum-RLAIF addresses generalizability issues

### Failure Modes to Understand

**Reward hacking**: Model finds ways to maximize the reward signal that don't reflect actual intended behavior. Example: Summarizer trained to maximize positive feedback learns to add flattery rather than improve quality.

**Specification gaming**: Model achieves literal objective while missing intended goal. Example: Agent trained to minimize pain in a game learns to pause the game.

**Sycophancy**: Model learns to agree with user preferences rather than provide accurate information. Strong Goodhart's Law signal — human raters prefer agreeable responses.

**Alignment trilemma**: Research shows no single method guarantees: (1) strong optimization, (2) perfect value capture, AND (3) robust generalization simultaneously.

**Implicit bias**: As models scale, explicit bias decreases but implicit bias increases. Alignment suppresses overt stereotyping while leaving underlying associations intact.

**Sandbagging**: Model deliberately underperforms on capability evaluations. Open research problem for safety evaluation.

**Emergent capabilities**: Capabilities that appear suddenly at scale without being present at smaller scales. Hard to predict in advance; complicates safety evaluations.

### Anthropic Mechanistic Interpretability (2025-2026)

Goal: Understand how LLMs work internally — a safety prerequisite for reliable alignment.

**Key technique: Sparse Autoencoders (SAEs)**
- Decompose dense neuron activations into interpretable, sparse features
- Each "feature" corresponds to a human-interpretable concept
- Enables understanding what information the model "thinks about" at each layer

**Circuit Tracing**
- Uses Cross-Layer Transcoders (CLTs) to build attribution graphs
- Shows how information flows from input tokens through reasoning circuits to output
- Open-sourced by Anthropic (May 2025); community applied to Gemma-2-2b and Llama 3.2-1b

**Practical implications**:
- Can detect hallucination mechanisms (Claude 3.5 Haiku circuit tracing published)
- Enables steering: modifying model behavior by editing intermediate representations
- Anthropic goal: "Reliably detect most AI model problems by 2027 using interpretability tools"

### Safety Considerations for Deployment

**Minimum viable safety practices for production AI**:
1. Output filtering: Classifier or rule-based filter for obviously harmful outputs
2. Input validation: Prompt injection detection; unusual input monitoring
3. Confidence/uncertainty: Flag low-confidence outputs for human review
4. Rate limiting and anomaly detection: Detect misuse patterns
5. Human-in-the-loop: For high-stakes decisions, require human approval
6. Audit logging: Record inputs and outputs for review and compliance
7. Red teaming: Adversarially probe your deployment before launch

**Deployment risk assessment questions**:
- What's the worst case if the model is wrong? (Informational vs. action-taking vs. safety-critical)
- Who are the users? (Expert users can catch errors; vulnerable users may not)
- Is there a human in the loop who can catch errors?
- What happens if the model is adversarially prompted?

---

## Research-to-Production Translation

### Technology Readiness Levels (TRL) for AI

| TRL | Description | AI Example |
|-----|-------------|------------|
| 1-3 | Basic research; proof of concept on toy problems | Academic paper; benchmark SOTA on curated dataset |
| 4-5 | Laboratory prototype; tested in controlled conditions | Works in researcher's environment; requires specific setup |
| 6-7 | Prototype demonstrated in relevant environment | Works in staging; tested on real data; scalability unknown |
| 8-9 | System complete; operationally deployed | Production system; monitored; SLAs met |

**Most AI papers: TRL 3-4**. Gap between paper and TRL 9 is typically 12-36 months and requires significant engineering work.

### Identifying Commercially Viable Research

Signals a paper has high commercial potential:
1. **Solves a clear, expensive problem**: Document processing, code generation, customer service — not esoteric benchmarks
2. **Substantial improvement**: 10%+ on a metric that maps to business value (not benchmark point gains)
3. **Generalizable approach**: Works across domains and data distributions, not just the training domain
4. **Reproducible with released code**: If it can't be reproduced, it's not ready for commercialization
5. **Inference efficiency**: Works at reasonable compute cost; not requiring 100K GPU-hours to deploy
6. **Cited by practitioners**: Google Scholar citations from industry researchers, not just academics

### Paper → Product Translation Checklist
- [ ] Does the capability work on your data, not just benchmark data?
- [ ] Is the inference cost acceptable at your scale?
- [ ] Is the error rate acceptable for your use case?
- [ ] Is there a reliable, maintained implementation?
- [ ] Does it integrate with your existing stack?
- [ ] Is it stable across input variations? (Robustness testing)
- [ ] Are there legal/IP issues with the approach or training data?
- [ ] Does it meet your compliance requirements?

### Key AI Capabilities and Their Commercial Maturity (Mid-2026)

| Capability | TRL | Production Notes |
|-----------|-----|------------------|
| Text classification | 9 | Fully mature; use API or fine-tuned small model |
| Information extraction | 8-9 | Strong with structured prompting; validate on your data |
| Code generation | 8 | Strong for common languages; validate correctness |
| RAG / Knowledge Q&A | 7-8 | Works well; retrieval quality is the hard part |
| Long-document summarization | 8 | Very strong; watch for faithfulness issues |
| Multimodal understanding | 7-8 | Strong for common formats (PDF, screenshot, image) |
| Computer use / GUI agents | 5-6 | Improving rapidly; still unreliable for complex workflows |
| Autonomous code engineering | 6-7 | SWE-Bench ~80%; but production reliability varies |
| Scientific hypothesis generation | 4-5 | Promising; requires domain expert validation |
| Video understanding | 5-6 | Emerging; latency and cost still high |
| Robotics manipulation | 4-5 | Research-grade; not production-ready for most use cases |
| Drug discovery / materials | 5-6 | AlphaFold 3 mature; generative design still maturing |
