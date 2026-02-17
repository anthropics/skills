# LLMOps 特殊考量

> LLM 时代带来的新挑战：Prompt 管理、RAG 运维、LLM 评估、成本优化。

## 目录

- [LLMOps vs 传统 MLOps](#llmops-vs-传统-mlops)
- [Prompt 管理](#prompt-管理)
- [RAG 运维](#rag-运维)
- [LLM 评估](#llm-评估)
- [成本优化](#成本优化)

---

## LLMOps vs 传统 MLOps

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    LLMOps 特殊挑战                                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   传统 MLOps                           LLMOps                               │
│   ──────────                           ──────                               │
│   模型小，训练快                        模型大，训练慢、成本高                │
│   数据标注相对便宜                      RLHF 标注成本高                       │
│   明确的评估指标                        评估复杂（安全/幻觉/对齐）             │
│   输入输出固定格式                      自然语言，输出不确定                  │
│   模型即产品                            Prompt + 模型 + RAG = 产品           │
│                                                                             │
│   ────────────────────────────────────────────────────────────────────────  │
│                                                                             │
│   LLMOps 新增关注点:                                                        │
│   ┌───────────────┐  ┌───────────────┐  ┌───────────────┐  ┌───────────┐   │
│   │ Prompt 管理   │  │ RAG 运维      │  │ 安全与对齐    │  │ 成本管理  │   │
│   │ • 版本控制    │  │ • 向量库更新  │  │ • 内容审核    │  │ • Token   │   │
│   │ • A/B 测试    │  │ • 检索质量    │  │ • 越狱检测    │  │ • 缓存    │   │
│   │ • 模板库      │  │ • 知识库版本  │  │ • 幻觉检测    │  │ • 路由    │   │
│   └───────────────┘  └───────────────┘  └───────────────┘  └───────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Prompt 管理

### Prompt 版本控制

```python
# 使用 LangSmith 进行 Prompt 管理
from langsmith import Client
from langchain import hub

client = Client()

# 上传 Prompt
prompt_template = """
You are a helpful assistant. Answer the following question:

Question: {question}

Please provide a clear and concise answer.
"""

# 创建并推送 Prompt
prompt = hub.push(
    "my-org/qa-prompt:v1.0",
    prompt_template,
    tags=["production", "qa"]
)

# 拉取特定版本
prompt_v1 = hub.pull("my-org/qa-prompt:v1.0")
prompt_latest = hub.pull("my-org/qa-prompt")  # 最新版本
```

### Prompt A/B 测试

```python
import random
from langchain import hub

class PromptABTest:
    def __init__(self, variants: dict, weights: list = None):
        """
        variants: {"control": "prompt:v1", "treatment": "prompt:v2"}
        weights: [0.5, 0.5]
        """
        self.variants = variants
        self.weights = weights or [1/len(variants)] * len(variants)
        self.results = {k: [] for k in variants.keys()}
    
    def get_prompt(self, user_id: str = None):
        """获取 Prompt 变体"""
        # 确定性分配 (同一用户始终看到同一变体)
        if user_id:
            variant_idx = hash(user_id) % len(self.variants)
            variant_name = list(self.variants.keys())[variant_idx]
        else:
            variant_name = random.choices(
                list(self.variants.keys()),
                weights=self.weights
            )[0]
        
        prompt = hub.pull(self.variants[variant_name])
        return prompt, variant_name
    
    def log_result(self, variant: str, metrics: dict):
        """记录结果"""
        self.results[variant].append(metrics)
    
    def analyze(self) -> dict:
        """分析 A/B 测试结果"""
        analysis = {}
        for variant, results in self.results.items():
            if results:
                analysis[variant] = {
                    "count": len(results),
                    "avg_score": sum(r.get("score", 0) for r in results) / len(results),
                    "avg_latency": sum(r.get("latency", 0) for r in results) / len(results)
                }
        return analysis

# 使用
ab_test = PromptABTest({
    "control": "my-org/qa-prompt:v1.0",
    "treatment": "my-org/qa-prompt:v2.0"
})

prompt, variant = ab_test.get_prompt(user_id="user123")
# 执行并记录结果
ab_test.log_result(variant, {"score": 0.9, "latency": 150})
```

---

## RAG 运维

### RAG 系统监控

```python
from dataclasses import dataclass
from typing import List

@dataclass
class RAGMetrics:
    """RAG 系统关键指标"""
    retrieval_latency_ms: float
    generation_latency_ms: float
    total_latency_ms: float
    num_chunks_retrieved: int
    relevance_score: float
    answer_faithfulness: float

class RAGMonitor:
    def __init__(self):
        self.metrics_history = []
    
    def log_query(self, query: str, context: List[str], answer: str, metrics: RAGMetrics):
        """记录 RAG 查询"""
        self.metrics_history.append({
            "query": query,
            "context_length": sum(len(c) for c in context),
            "answer_length": len(answer),
            **metrics.__dict__
        })
    
    def check_retrieval_quality(self) -> dict:
        """检查检索质量"""
        recent = self.metrics_history[-100:]  # 最近 100 条
        
        return {
            "avg_relevance": sum(m["relevance_score"] for m in recent) / len(recent),
            "low_relevance_rate": sum(1 for m in recent if m["relevance_score"] < 0.5) / len(recent),
            "avg_chunks": sum(m["num_chunks_retrieved"] for m in recent) / len(recent)
        }
    
    def alert_if_needed(self):
        """检查是否需要告警"""
        quality = self.check_retrieval_quality()
        
        if quality["avg_relevance"] < 0.6:
            send_alert("RAG relevance score dropping!")
        
        if quality["low_relevance_rate"] > 0.3:
            send_alert("High rate of low-relevance retrievals!")
```

### 向量数据库更新策略

```python
from datetime import datetime
import hashlib

class VectorDBUpdater:
    def __init__(self, vector_store):
        self.vector_store = vector_store
        self.doc_hashes = {}  # 文档哈希缓存
    
    def update_documents(self, documents: List[dict]):
        """增量更新文档"""
        to_add = []
        to_update = []
        
        for doc in documents:
            doc_id = doc["id"]
            content_hash = hashlib.md5(doc["content"].encode()).hexdigest()
            
            if doc_id not in self.doc_hashes:
                to_add.append(doc)
            elif self.doc_hashes[doc_id] != content_hash:
                to_update.append(doc)
            
            self.doc_hashes[doc_id] = content_hash
        
        # 执行更新
        if to_add:
            self.vector_store.add_documents(to_add)
            print(f"Added {len(to_add)} new documents")
        
        if to_update:
            for doc in to_update:
                self.vector_store.update_document(doc["id"], doc)
            print(f"Updated {len(to_update)} documents")
    
    def rebuild_index(self):
        """完全重建索引"""
        self.vector_store.clear()
        all_docs = fetch_all_documents()
        self.vector_store.add_documents(all_docs)
        print(f"Rebuilt index with {len(all_docs)} documents")
```

---

## LLM 评估

### 使用 RAGAS 评估 RAG

```python
from ragas import evaluate
from ragas.metrics import (
    faithfulness,
    answer_relevancy,
    context_precision,
    context_recall
)

# 准备评估数据
eval_dataset = {
    "question": [
        "What is machine learning?",
        "How does RAG work?"
    ],
    "answer": [
        "Machine learning is...",
        "RAG works by..."
    ],
    "contexts": [
        ["ML is a subset of AI...", "It involves training models..."],
        ["RAG combines retrieval...", "It enhances LLM responses..."]
    ],
    "ground_truth": [
        "Machine learning is a subset of AI...",
        "RAG (Retrieval Augmented Generation)..."
    ]
}

# 运行评估
results = evaluate(
    eval_dataset,
    metrics=[
        faithfulness,       # 答案是否忠于上下文
        answer_relevancy,   # 答案是否相关
        context_precision,  # 检索精度
        context_recall      # 检索召回
    ]
)

print(results)
# {'faithfulness': 0.85, 'answer_relevancy': 0.92, ...}
```

### 幻觉检测

```python
from langchain.evaluation import load_evaluator

# 使用 LLM 作为评估器
evaluator = load_evaluator("labeled_score_string", criteria="correctness")

def check_hallucination(question: str, answer: str, reference: str) -> dict:
    """检测幻觉"""
    result = evaluator.evaluate_strings(
        input=question,
        prediction=answer,
        reference=reference
    )
    
    return {
        "score": result["score"],
        "reasoning": result["reasoning"],
        "is_hallucination": result["score"] < 0.5
    }

# 使用
result = check_hallucination(
    question="Who is the CEO of OpenAI?",
    answer="Elon Musk is the CEO of OpenAI.",
    reference="Sam Altman is the CEO of OpenAI."
)
print(result)
# {'score': 0.2, 'is_hallucination': True, ...}
```

---

## 成本优化

### 语义缓存

```python
from langchain.cache import RedisSemanticCache
from langchain.globals import set_llm_cache

# 设置语义缓存
set_llm_cache(RedisSemanticCache(
    redis_url="redis://localhost:6379",
    embedding=embeddings,
    score_threshold=0.95  # 相似度阈值
))

# 后续相似查询会命中缓存
response1 = llm("What is machine learning?")  # 调用 LLM
response2 = llm("What's ML?")  # 命中缓存，不调用 LLM
```

### 模型路由

```python
class ModelRouter:
    """智能模型路由 - 简单问题用小模型，复杂问题用大模型"""
    
    def __init__(self, small_model, large_model, classifier):
        self.small_model = small_model
        self.large_model = large_model
        self.classifier = classifier
    
    def route(self, query: str) -> str:
        """路由到合适的模型"""
        complexity = self.classifier.predict(query)
        
        if complexity == "simple":
            return self.small_model.generate(query)
        else:
            return self.large_model.generate(query)

# 简单的复杂度分类
def classify_complexity(query: str) -> str:
    """基于规则的复杂度分类"""
    simple_patterns = ["what is", "define", "who is", "when was"]
    
    query_lower = query.lower()
    if any(p in query_lower for p in simple_patterns):
        if len(query.split()) < 20:
            return "simple"
    
    return "complex"
```

### Token 使用监控

```python
from langchain.callbacks import get_openai_callback

class TokenMonitor:
    def __init__(self, daily_budget: float = 100.0):
        self.daily_budget = daily_budget
        self.daily_usage = 0.0
        self.usage_history = []
    
    def track_usage(self, func):
        """装饰器：追踪 Token 使用"""
        def wrapper(*args, **kwargs):
            with get_openai_callback() as cb:
                result = func(*args, **kwargs)
                
                self.daily_usage += cb.total_cost
                self.usage_history.append({
                    "tokens": cb.total_tokens,
                    "cost": cb.total_cost,
                    "timestamp": datetime.now()
                })
                
                # 预算告警
                if self.daily_usage > self.daily_budget * 0.8:
                    send_alert(f"Token budget 80% used: ${self.daily_usage:.2f}")
                
                return result
        return wrapper

# 使用
monitor = TokenMonitor(daily_budget=100.0)

@monitor.track_usage
def ask_llm(question: str):
    return llm(question)
```

---

## LLMOps 工具推荐

| 领域 | 工具 | 特点 |
|------|------|------|
| **Prompt 管理** | LangSmith | 版本控制、调试、评估 |
| **评估** | RAGAS | RAG 专用评估框架 |
| **监控** | Langfuse | 开源 LLM 可观测性 |
| **缓存** | GPTCache | 语义缓存 |
| **成本** | OpenAI Usage API | Token 监控 |

---

*下一篇：[09-工具生态](09-tool-ecosystem.md)*

*返回目录：[README](README.md)*
