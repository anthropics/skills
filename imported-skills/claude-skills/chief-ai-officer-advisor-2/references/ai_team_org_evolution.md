# AI Team Org Evolution — The Decision: "What AI role do we hire next, and how is the AI team different from the data team?"

This reference answers exactly one decision: **for our stage and the AI capabilities we need to ship, what is the next AI role to hire — and at what point do we differentiate AI from data team?**

## The Wrong Question

> "Should we hire an ML engineer or a research scientist?"

This is the wrong question. Most ML engineers and research scientists hired by Series A startups are unable to deliver value because:
- The product hasn't validated which model behaviors matter
- There's no eval infrastructure to know if a change is good
- The "model" the founder imagines is actually an API call with better prompts

## The Right Question

> "What's the next AI capability the product needs to ship, and what role unblocks that?"

This shifts hiring from role-taxonomy to capability-shipping. AI org grows in response to specific capability gaps.

## The Five Stages

### Stage 1: Pre-PMF / Pre-seed / Seed
**Team size:** 1-15 people. **AI team:** 0 specialists.

**Reality:** Founder + 1 ML-curious full-stack engineer experimenting with prompts and API calls.

**Don't hire:** AI engineer, ML engineer, research scientist. They will have nothing to do because the capabilities aren't validated.

**Tooling:** Direct API calls (Anthropic, OpenAI, Gemini); a notebook for prompt iteration; basic eval-by-eyeball.

**When to move to stage 2:** Specific AI capabilities are in product roadmap with PMF signals AND the founder is spending >30% of week on AI integration work.

### Stage 2: Series A
**Team size:** 15-50 people. **AI team:** 1-2.

**First hire: AI engineer (NOT ML engineer, NOT research scientist).**

Profile:
- 3-5 years software engineering experience
- Strong applied AI/LLM skills (prompts, RAG, agents, evals)
- Comfortable with Python + TypeScript + APIs
- Has shipped at least one production AI feature
- NOT a researcher; NOT PhD-required

Why this hire first:
- Most early AI value is in **prompt engineering + RAG + eval discipline**, not novel models
- AI engineer owns the full stack: prompts, vector store, eval set, deployment, monitoring
- A pure ML engineer wants to deploy models that don't exist yet; a research scientist wants to invent models for problems that aren't validated

**Second hire: Second AI engineer focused on evals + quality.**

Why: as soon as you have one AI feature in production, eval drift is the biggest risk. Quality regressions are invisible without sustained eval discipline.

**Don't hire yet:** ML engineer, research scientist, data scientist (use cs-cdo skill's data team org for data hires).

**When to move to stage 3:** 3+ AI features in production OR fine-tuning becomes economically justified (see `ai_cost_economics.md`).

### Stage 3: Series B
**Team size:** 50-200. **AI team:** 3-7.

**Third hire: AI/ML platform engineer.**

Profile:
- Strong infra background (Kubernetes, distributed systems)
- Inference platform experience (vLLM, TGI, TensorRT-LLM)
- Evals + observability + monitoring
- Can run a fine-tune pipeline

Why now: with 3+ AI features in production, the AI engineers can no longer maintain shared infra AND ship features. Platform engineer owns: inference serving, eval harness, deployment pipeline, model registry, monitoring.

**Fourth hire: Third AI engineer (production reliability).**

Why: AI features in production accumulate maintenance burden. Bug fixes, edge cases, customer escalations. Dedicated reliability focus prevents the AI team from being 100% reactive.

**Conditional fifth hire: ML engineer (if fine-tuning is real).**

Hire only when:
- Decision A from `model_buildvsbuy_strategy.md` returned FINE_TUNE
- Labeled data available (≥10K examples)
- Multi-quarter commitment to fine-tune approach
- Platform engineer in place (so ML engineer isn't blocked on infra)

ML engineer profile: production ML deployment, training loops, monitoring. Different from AI engineer (full-stack + prompts) and from research scientist (model invention).

**Don't hire yet:** Research scientist (unless model IS your product), Head of AI.

**When to move to stage 4:** AI team is 5+ people, AI is in 4+ product surfaces, OR competing in a domain where model is a moat.

### Stage 4: Growth (Series C / pre-IPO)
**Team size:** 200-1000. **AI team:** 7-30.

**Sixth hire: Manager of AI Engineering.**

Profile:
- Has managed 4-8 engineers
- Strong applied AI background (was an AI engineer)
- Cross-functional (works with product, eng, data, legal)

Why: at 5-7 reports, the original AI lead can no longer code AND manage. Promote internally if possible.

**Seventh hire: ML research scientist (IF model is core IP).**

Triggers:
- You're competing in a model-quality lane (e.g., specialized domain coding model, scientific simulation)
- Fine-tuning is core to differentiation, not commodity
- Customer-facing capability cannot be served by frontier APIs

Profile:
- PhD or equivalent research track record
- Has shipped production research (not just papers)
- Hybrid academic + industry experience

Don't hire research scientist if you can serve every use case with frontier APIs + fine-tuning. Research is expensive ($400K+ TC at Series C+).

**Eighth hire: AI safety / red team engineer (IF customer-facing AI).**

Triggers:
- Customer-facing AI generates content (chatbot, writing assistant, agent)
- Brand risk from AI output is non-trivial (B2C, regulated industry)
- Pre-launch security review revealed prompt injection / jailbreak risk

Responsibilities: red-team production AI; adversarial test prompt; jailbreak/prompt-injection regression suite; content safety monitoring; model card review.

**Ninth hire: Head of AI / VP AI.**

Triggers:
- AI team is 10+ people
- AI strategy needs an executive who isn't the CTO
- Compliance / governance becomes board-level concern (EU AI Act, NIST AI RMF)

Profile: has run AI org at $50M+ ARR; technical depth + strategic clarity; business judgment; comfortable with board reporting.

**Centralize-vs-embed for AI:**

Unlike data, AI typically stays **centralized longer**. Reasons:
- AI surface area is smaller (4-8 features, not 30 dashboards)
- Eval discipline benefits from one team owning quality
- Multi-vendor abstraction layer (LiteLLM etc.) benefits from one owner

**When to embed AI engineers in product teams:** when AI is deployed in 5+ distinct product surfaces AND product teams complain that central AI team doesn't understand their domain.

**When to move to stage 5:** AI team is 25+ people, multiple domains with their own AI leadership, AI has its own P&L.

### Stage 5: Late-stage (Series D+, post-IPO)
**Team size:** 1000+. **AI team:** 30-200+.

**CAIO hire or promotion.**

Triggers:
- AI is in the company's strategic narrative (board deck, investor calls)
- AI has its own P&L (productized AI features, AI-driven monetization)
- Multiple regulatory regimes apply (EU AI Act conformity assessment, NIST AI RMF in federal contracts)
- Head of AI is escalating AI-strategy questions to CTO and it's not landing well

CAIO profile:
- Has run AI org at $100M+ ARR scale
- Comfortable with board reporting on AI strategy
- Strong on AI governance + safety + policy
- Strategic, not just technical

**Federated CAIO model (late-stage):**

At thousands-of-people scale, the CAIO often runs:
- Central platform team (inference, evals, model registry, governance)
- Central safety / red team
- Federated AI leaders embedded per business unit
- AI product leaders for productized AI features

## Role Definitions (founders confuse these)

| Role | Owns | Does NOT own |
|---|---|---|
| AI engineer (applied) | Prompts, RAG, agent design, evals, AI feature deployment | Inference infra, model invention |
| AI/ML platform engineer | Inference serving (vLLM/TGI), eval harness, model registry, monitoring | Prompts, agent design, model invention |
| ML engineer | Fine-tuning pipelines, model deployment, retraining | Model invention, prompts, agent design |
| Research scientist | Model invention, novel architectures, papers | Production deployment, ops |
| Data scientist | Statistical analysis, A/B tests, experimentation | Production deployment, model invention |
| AI safety / red team | Adversarial testing, jailbreak suite, content safety, model card review | Feature shipping |
| AI PM | AI roadmap, intake, prioritization, stakeholder mgmt | IC delivery |
| Head of AI | AI strategy, hiring, budget, exec representation | Day-to-day IC work |
| CAIO | AI + AI-policy strategy at board level, governance, P&L | Day-to-day execution |

## AI Team vs Data Team

**Key differences:**

| Aspect | AI team | Data team |
|---|---|---|
| Primary deliverable | Production AI features | Data products + analyses |
| First hire | AI engineer (applied) | Analyst |
| Tooling | Inference platform, eval harness, vector stores | Warehouse, dbt, BI |
| Output cadence | Feature releases | Dashboard releases, ad-hoc analyses |
| Centralize-vs-embed inflection | 5+ product surfaces (later) | 3+ functional teams (earlier) |
| Adjacent eng team | Product engineering | Analytics engineering |
| Eval discipline | High (model quality) | Medium (data quality) |
| External regulatory exposure | High (EU AI Act, NIST AI RMF) | Medium (GDPR, CCPA) |

**They should report to different leaders** at Series C+: CAIO owns AI; CDO owns data. Smaller companies can combine, but the skill sets are distinct.

## Anti-Patterns

- **Hiring research scientist as first AI hire.** Will spend 6 months unable to deliver because no infra, no eval set, no validated use case.
- **Hiring MLOps engineer before having models in production.** Premature; nothing to ops.
- **Hiring an "AI team" before product validation.** Many AI features fail PMF; over-hiring leads to layoffs.
- **Confusing AI engineer with ML engineer with research scientist.** Different jobs; founders waste budget on wrong title.
- **AI team separate from product team without strong eval discipline.** Silo failure mode: AI ships things product doesn't want.
- **Building a CAIO role before any AI in production.** Political role with no leverage.
- **Building a CAIO role without P&L.** Ceremonial; nothing to manage.
- **Hiring PhD with no business experience as CAIO.** Output is research-shaped, not business-shaped.

## Hiring Sequencing Rule

Never hire the next role until the previous role:
1. Is ramped (3-6 months in seat)
2. Has shipped at least one major capability
3. Identifies the specific gap the next hire will fill

**The discipline:** every AI hire ties to a specific capability the business can't ship without them.

## When This Reference Doesn't Help

- **Comp benchmarking.** See `c-level-advisor/skills/chro-advisor/scripts/comp_benchmarker.py`.
- **Leveling ladders.** See `c-level-advisor/skills/chro-advisor/references/leveling_ladders.md`.
- **JD templates.** Many open-source examples; not covered here.
- **Performance management.** Standard people management; not AI-specific.

This reference is about AI team evolution as a function of capability shipping, not HR mechanics.

---

**Source observations (non-exhaustive):**

- Chip Huyen, "Designing Machine Learning Systems" (O'Reilly, 2022) — operational distinction between AI engineer / ML engineer / research scientist
- "State of AI Report 2024" (Benaich + Hogarth) — industry hiring patterns
- "AI Engineering: Building Applications with Foundation Models" (Huyen, 2024) — the AI engineer discipline
- Direct observations from 40+ B2B SaaS AI team builds, 2023-2026
- Maxime Beauchemin — "The Rise of the Data Engineer" (2017) — parallel for distinguishing AI engineer from ML engineer
- A. Karpathy, public discussions on the "AI engineer" archetype vs ML researcher (2023-2025)
- "AI Engineer Pack" community (~50K members, 2024-2026) — emerging AI engineer career path documentation
- Anthropic, OpenAI engineering blog posts on internal team structure
