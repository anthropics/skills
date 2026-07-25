---
name: "rag-architect"
description: "Use when the user asks to design a RAG pipeline, choose a chunking strategy or embedding model, pick a vector database, or evaluate retrieval quality (precision@k, recall@k, NDCG). Examples: 'design a RAG system for our docs', 'what chunk size should I use for this corpus', 'evaluate my retriever against ground truth'. NOT for general LLM cost tuning (use llm-cost-optimizer) or agent loops over retrieval (use agenthub)."
---

# RAG Architect

Design, tune, and evaluate production RAG pipelines with three deterministic tools. Run the tools against the actual corpus and requirements — do not pick chunk sizes or databases by intuition.

## Hard rules

1. **Never present model names or vendor prices as current facts.** Embedding models and vector-DB pricing rot in months. Recommend a *tier* (see table below), name a current-generation candidate, and tell the user to verify against the provider's live pricing page.
2. **Every design ends with an evaluation run.** A RAG design without `retrieval_evaluator.py` numbers is a hypothesis, not a deliverable.
3. **Chunking is corpus-driven.** Run `chunking_optimizer.py` on the real documents before choosing a strategy.

## Embedding model tiers (pattern, not price list)

| Tier | Current-generation examples (verify before use) | When |
|---|---|---|
| Fast / self-hosted | `all-MiniLM-L6-v2`, `bge-small` | Cost-sensitive, small scale, real-time |
| Balanced open | `all-mpnet-base-v2`, `bge-large`, `e5-large` | Quality without API dependency |
| Quality API | `text-embedding-3-large`, `voyage-3-large` | Accuracy-priority general retrieval |
| Code | `voyage-code-3`, CodeBERT-family | Code search corpora |

**Pricing discipline:** build the cost model with a placeholder table — columns `model | $/1M tokens (verify) | dims | as-of date` — and have the user fill in live numbers. Same for vector DBs (Pinecone/Weaviate/Qdrant/Chroma/pgvector): the selection criteria (managed vs self-hosted, scale, filtering, existing Postgres) are durable; the dollar figures are not.

## Workflow

All paths relative to this skill folder. Outputs chain: corpus analysis → design → evaluation.

### 1. Analyze the corpus and pick chunking

```bash
python3 chunking_optimizer.py /path/to/docs --extensions .md .txt -o chunking.json
```

Emits `chunking.json` with `corpus_info`, per-strategy `strategy_results`, a `recommendation`, and `sample_chunks`. Use `recommendation.strategy` and its config; show the user 2-3 `sample_chunks` so they can sanity-check boundaries.

### 2. Design the pipeline from requirements

Write a requirements JSON with these keys (all required): `document_types[]`, `document_count`, `avg_document_size` (chars), `queries_per_day`, `query_patterns[]`, `latency_requirement`, `budget_monthly`, `accuracy_priority` (0-1), `cost_priority` (0-1), `maintenance_complexity`.

```bash
python3 rag_pipeline_designer.py requirements.json -o design.json
```

Emits `design.json` with `chunking`, `embedding`, `vector_db`, `retrieval`, `reranking`, `evaluation`, `total_cost`, `architecture_diagram` (mermaid), and `config_templates`. Present the diagram; label every `cost_monthly` figure as an estimate to verify (rule 1).

### 3. Evaluate retrieval quality

Prepare `queries.json` (list of `{id, text}` or `{"queries": [...]}`) and `ground_truth.json` (`{query_id: [relevant_doc_ids]}`), then:

```bash
python3 retrieval_evaluator.py queries.json /path/to/docs ground_truth.json --k-values 3 5 10 -o eval.json
```

Reports precision@k, recall@k, MRR, NDCG@k, plus `poor_precision_examples` / `poor_recall_examples` for failure analysis.

### 4. Verification loop

The design is done only when:

1. `eval.json` meets targets — typical floors: precision@5 ≥ 0.8, recall@10 ≥ 0.85 (set per use case with the user).
2. If below target: inspect the poor-example lists, then change **one** variable (chunking strategy → re-run step 1; embedding tier; add reranking; hybrid retrieval) and re-run step 3. Repeat.
3. Every recommended model/price in the deliverable carries a "verify current pricing/model availability" note with an as-of date.

## References

- `references/chunking_strategies_comparison.md` — strategy trade-offs the optimizer implements
- `references/embedding_model_benchmark.md` — benchmark *methodology* (dated snapshot; staleness warning at top)
- `references/rag_evaluation_framework.md` — metric definitions (faithfulness, relevance, precision/recall/NDCG)
