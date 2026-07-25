---
name: "caio-review"
description: "/cs:caio-review <plan> — Eval-demanding Chief AI Officer interrogation of any plan that involves AI: model selection, risk classification, cost economics, or AI hiring. Use when shipping an AI feature without an eval set, choosing between API, fine-tune, and self-hosted, or classifying a use case under the EU AI Act."
---

# /cs:caio-review — CAIO Forcing Questions

**Command:** `/cs:caio-review <plan>`

The eval-demanding CAIO pressure-tests any plan that involves AI. Six questions before any AI feature ships, any multi-year vendor commitment, or any AI team expansion.

## When to Run

- Before shipping any new AI-powered feature
- Before signing a multi-year AI vendor contract (API or self-hosted infra)
- Before EU launch of any AI feature
- Before a major AI team hire (especially ML engineer or research scientist)
- Before a fine-tuning project commitment
- Before adopting AI in a regulated domain (employment, credit, healthcare, education, etc.)
- When the founder uses the word "AI" near "competitive advantage" or "moat"

## The Six CAIO Questions

### 1. What does this AI need to be good at, and how would you measure it?
**No eval set = no ship.** Before any AI feature deploys, define the eval criteria.
- 50-100 representative inputs minimum
- Expected outputs OR rubric for grading
- Edge cases: ambiguous, adversarial, format-edge
- If you can't write down what "good" looks like, you don't have a feature; you have a vibe.

### 2. What's the SLO on hallucination / error rate, and what's the fallback?
**Every AI feature has a failure mode. Plan for it.**
- Quantified SLO: "<5% hallucination on factual queries"
- Detection mechanism: monitoring, sampling, customer feedback loop
- Fallback: human-in-loop review, lower-risk default response, refuse-to-answer
- Blast radius if SLO breached: how many users affected, what is the cost?

### 3. What's the risk tier under EU AI Act, and is conformity assessment required?
**Run `ai_risk_classifier.py` if any EU residents are affected OR domain is regulated.**
- PROHIBITED → cannot launch in EU; re-scope
- HIGH → conformity assessment + EU DB registration + 10 Articles of obligations (3-12 months, $50-200K)
- LIMITED → transparency obligations (chatbot disclosure, AI-generated content marking)
- MINIMAL → no specific obligations; NIST AI RMF voluntary

### 4. API, fine-tune, or build?
**Run `model_buildvsbuy_calculator.py` for the specific use case.**
- 80% of B2B SaaS use cases: API
- 15%: fine-tune (when domain-specific behavior + labeled data + ML team + high volume)
- <1%: build from scratch
- Decision must consider economic breakeven AND practical feasibility (data, team, compliance)

### 5. What's the 12-month cost trajectory at expected scale?
**Run `ai_cost_economics.py` for the workload.**
- API: variable, scales linearly
- Self-hosted: mostly fixed, breakeven typically 1-10B tokens/month for 70B-class
- Hidden costs of self-hosted: ops, monitoring, model updates, capacity, failover, security
- Hidden costs of API: vendor lock-in, capability drift, rate limits, data residency
- Prompt caching is the most underrated lever; check provider support

### 6. What role unblocks this — and have we hired prerequisites first?
**Map AI capability to specific role. Founders confuse AI engineer / ML engineer / research scientist.**
- AI engineer: applied + full-stack + prompts + evals + deployment (most startups need this)
- ML engineer: fine-tuning + retraining infra (only after platform engineer + labeled data)
- Research scientist: model invention (only if model IS the product)
- Don't hire research scientist as first AI hire — they need infrastructure to be productive

## Workflow

```bash
# 1. Model selection check
python ../../../skills/chief-ai-officer-advisor/scripts/model_buildvsbuy_calculator.py use_case.json

# 2. Regulatory classification
python ../../../skills/chief-ai-officer-advisor/scripts/ai_risk_classifier.py use_case.json

# 3. Cost projection
python ../../../skills/chief-ai-officer-advisor/scripts/ai_cost_economics.py workload.json
```

## Output Format

```markdown
# CAIO Review: <plan>
**Date:** YYYY-MM-DD

## The Decision Being Made
[one sentence — which CAIO decision: model selection | risk classification | economics | next hire]

## Eval Discipline
- Eval set committed: yes/no
- SLO defined: <metric> < <threshold>
- Fallback behavior: <one line>

## Model Selection (if applicable)
- Recommended: API / FINE_TUNE / BUILD
- 3-year TCO: $X (chosen path) vs $Y (alternatives)
- Breakeven: <volume>

## Risk Classification (if applicable)
- EU AI Act tier: PROHIBITED / HIGH / LIMITED / MINIMAL
- Conformity assessment required: yes/no
- US state triggers: [list]
- Required controls open: N

## Cost Economics (if applicable)
- Monthly cost at current volume: $X
- Breakeven for self-hosted migration: <volume>
- Migration cost if applicable: $X (3-6 months)

## Org (if applicable)
- Next hire: <role>
- Why this, not the alternative: <one line>
- Prerequisite hires in place: yes/no

## Verdict
🟢 SHIP | 🟡 SHARPEN | 🔴 BLOCK

## Next Steps
[3 concrete actions]
```

## Routing

- `/cs:cdo-review` — for any training-data implications
- `/cs:gc-review` — for AI vendor contracts, output liability, training-data licensing
- `/cs:ciso-review` — for prompt injection / jailbreak / training-data poisoning threat model
- `/cs:cfo-review` — for multi-year vendor or GPU commitment TCO
- `cs-chro-advisor` agent — for AI team hires (comp, ladder, leveling)
- `/cs:decide` — log the verdict
- `/cs:freeze 60` — on multi-year AI commitments

## Related

- Agent: [`cs-caio-advisor`](../../agents/cs-caio-advisor.md)
- Skill: [`chief-ai-officer-advisor`](../../../skills/chief-ai-officer-advisor/SKILL.md)
- Adjacent: `../../../skills/chief-data-officer-advisor/` (training data rights, data strategy)

---

**Version:** 1.0.0
