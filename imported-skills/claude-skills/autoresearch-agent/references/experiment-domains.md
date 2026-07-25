# Experiment Domains Guide

## Domain: Engineering

### Code Speed Optimization

```bash
python scripts/setup_experiment.py \
  --domain engineering \
  --name api-speed \
  --target src/api/search.py \
  --eval "python -m pytest tests/bench_search.py --tb=no -q" \
  --metric p50_ms \
  --direction lower \
  --evaluator benchmark_speed
```

**What the agent optimizes:** Algorithm, data structures, caching, query patterns, I/O.
**Cost:** Free — just runs benchmarks.
**Speed:** ~5 min/experiment, ~12/hour, ~100 overnight.

### Bundle Size Reduction

```bash
python scripts/setup_experiment.py \
  --domain engineering \
  --name bundle-size \
  --target webpack.config.js \
  --eval "npm run build && python .autoresearch/engineering/bundle-size/evaluate.py" \
  --metric size_bytes \
  --direction lower \
  --evaluator benchmark_size
```

Edit `evaluate.py` to set `TARGET_FILE = "dist/main.js"` and add `BUILD_CMD = "npm run build"`.

### Test Pass Rate

```bash
python scripts/setup_experiment.py \
  --domain engineering \
  --name fix-flaky-tests \
  --target src/utils/parser.py \
  --eval "python .autoresearch/engineering/fix-flaky-tests/evaluate.py" \
  --metric pass_rate \
  --direction higher \
  --evaluator test_pass_rate
```

### Docker Build Speed

```bash
python scripts/setup_experiment.py \
  --domain engineering \
  --name docker-build \
  --target Dockerfile \
  --eval "python .autoresearch/engineering/docker-build/evaluate.py" \
  --metric build_seconds \
  --direction lower \
  --evaluator build_speed
```

### Memory Optimization

```bash
python scripts/setup_experiment.py \
  --domain engineering \
  --name memory-usage \
  --target src/processor.py \
  --eval "python .autoresearch/engineering/memory-usage/evaluate.py" \
  --metric peak_mb \
  --direction lower \
  --evaluator memory_usage
```

### ML Training (Karpathy-style)

Requires NVIDIA GPU. See [autoresearch](https://github.com/karpathy/autoresearch).

```bash
python scripts/setup_experiment.py \
  --domain engineering \
  --name ml-training \
  --target train.py \
  --eval "uv run train.py" \
  --metric val_bpb \
  --direction lower \
  --time-budget 5
```

---

## Domain: Marketing

### Medium Article Headlines

```bash
python scripts/setup_experiment.py \
  --domain marketing \
  --name medium-ctr \
  --target content/titles.md \
  --eval "python .autoresearch/marketing/medium-ctr/evaluate.py" \
  --metric ctr_score \
  --direction higher \
  --evaluator llm_judge_content
```

Edit `evaluate.py`: set `TARGET_FILE = "content/titles.md"` and `CLI_TOOL = "claude"`.

**What the agent optimizes:** Title phrasing, curiosity gaps, specificity, emotional triggers.
**Cost:** Uses your CLI subscription (Claude Max = unlimited).
**Speed:** ~2 min/experiment, ~30/hour.

### Social Media Copy

```bash
python scripts/setup_experiment.py \
  --domain marketing \
  --name twitter-engagement \
  --target social/tweets.md \
  --eval "python .autoresearch/marketing/twitter-engagement/evaluate.py" \
  --metric engagement_score \
  --direction higher \
  --evaluator llm_judge_copy
```

Edit `evaluate.py`: set `PLATFORM = "twitter"` (or linkedin, instagram).

### Email Subject Lines

```bash
python scripts/setup_experiment.py \
  --domain marketing \
  --name email-open-rate \
  --target emails/subjects.md \
  --eval "python .autoresearch/marketing/email-open-rate/evaluate.py" \
  --metric engagement_score \
  --direction higher \
  --evaluator llm_judge_copy
```

Edit `evaluate.py`: set `PLATFORM = "email"`.

### Ad Copy

```bash
python scripts/setup_experiment.py \
  --domain marketing \
  --name ad-copy-q2 \
  --target ads/google-search.md \
  --eval "python .autoresearch/marketing/ad-copy-q2/evaluate.py" \
  --metric engagement_score \
  --direction higher \
  --evaluator llm_judge_copy
```

Edit `evaluate.py`: set `PLATFORM = "ad"`.

---

## Domain: Content

### Article Structure & Readability

```bash
python scripts/setup_experiment.py \
  --domain content \
  --name article-structure \
  --target drafts/my-article.md \
  --eval "python .autoresearch/content/article-structure/evaluate.py" \
  --metric ctr_score \
  --direction higher \
  --evaluator llm_judge_content
```

### SEO Descriptions

```bash
python scripts/setup_experiment.py \
  --domain content \
  --name seo-meta \
  --target seo/descriptions.md \
  --eval "python .autoresearch/content/seo-meta/evaluate.py" \
  --metric ctr_score \
  --direction higher \
  --evaluator llm_judge_content
```

---

## Domain: Prompts

### System Prompt Optimization

```bash
python scripts/setup_experiment.py \
  --domain prompts \
  --name support-bot \
  --target prompts/support-system.md \
  --eval "python .autoresearch/prompts/support-bot/evaluate.py" \
  --metric quality_score \
  --direction higher \
  --evaluator llm_judge_prompt
```

Requires `tests/cases.json` with test inputs and expected outputs:

```json
[
  {
    "input": "I can't log in to my account",
    "expected": "Ask for email, check account status, offer password reset"
  },
  {
    "input": "How do I cancel my subscription?",
    "expected": "Empathetic response, explain cancellation steps, offer retention"
  }
]
```

### Agent Skill Optimization

```bash
python scripts/setup_experiment.py \
  --domain prompts \
  --name skill-improvement \
  --target SKILL.md \
  --eval "python .autoresearch/prompts/skill-improvement/evaluate.py" \
  --metric quality_score \
  --direction higher \
  --evaluator llm_judge_prompt
```

---

## Choosing Your Domain

| I want to... | Domain | Evaluator | Cost |
|-------------|--------|-----------|------|
| Speed up my code | engineering | benchmark_speed | Free |
| Shrink my bundle | engineering | benchmark_size | Free |
| Fix flaky tests | engineering | test_pass_rate | Free |
| Speed up Docker builds | engineering | build_speed | Free |
| Reduce memory usage | engineering | memory_usage | Free |
| Train ML models | engineering | (custom) | Free + GPU |
| Write better headlines | marketing | llm_judge_content | Subscription |
| Improve social posts | marketing | llm_judge_copy | Subscription |
| Optimize email subjects | marketing | llm_judge_copy | Subscription |
| Improve ad copy | marketing | llm_judge_copy | Subscription |
| Optimize article structure | content | llm_judge_content | Subscription |
| Improve SEO descriptions | content | llm_judge_content | Subscription |
| Optimize system prompts | prompts | llm_judge_prompt | Subscription |
| Improve agent skills | prompts | llm_judge_prompt | Subscription |

**First time?** Start with an engineering experiment (free, fast, measurable). Once comfortable, try content/marketing with LLM judges.
