# Token 节省策略

> 知识库不仅能提升回答质量，还能通过智能检索和缓存大幅降低 Token 消耗和 API 成本。

## 目录

- [Token 成本挑战](#token-成本挑战)
- [Context Window 管理](#context-window-管理)
- [知识库作为外部记忆](#知识库作为外部记忆)
- [Prompt Compression 技术](#prompt-compression-技术)
- [Semantic Caching（语义缓存）](#semantic-caching语义缓存)
- [混合检索降低冗余](#混合检索降低冗余)
- [模型路由策略](#模型路由策略)
- [成本监控与预算控制](#成本监控与预算控制)
- [实战练习](#实战练习)

---

## Token 成本挑战

### 为什么 Token 优化至关重要

```
┌─────────────────────────────────────────────────────────┐
│              Token 成本分析                               │
├─────────────────────────────────────────────────────────┤
│                                                         │
│  典型 RAG 请求的 Token 分布：                             │
│                                                         │
│  ┌──────────────────────────────────────────┐           │
│  │ System Prompt    │ 500 tokens  │  5%     │           │
│  ├──────────────────┼─────────────┼─────────┤           │
│  │ 检索到的上下文    │ 6000 tokens │  60%    │ ← 最大头  │
│  ├──────────────────┼─────────────┼─────────┤           │
│  │ 对话历史         │ 2500 tokens │  25%    │           │
│  ├──────────────────┼─────────────┼─────────┤           │
│  │ 用户查询         │ 100 tokens  │  1%     │           │
│  ├──────────────────┼─────────────┼─────────┤           │
│  │ 生成的回答       │ 900 tokens  │  9%     │           │
│  └──────────────────┴─────────────┴─────────┘           │
│                                                         │
│  总计：~10,000 tokens/请求                               │
│  日均 10,000 请求 → 1 亿 tokens/天                       │
│                                                         │
│  按 GPT-4o 价格 ($2.5/1M input + $10/1M output)：      │
│  日成本 ≈ $250 (input) + $90 (output) = $340/天         │
│  月成本 ≈ $10,200                                       │
└─────────────────────────────────────────────────────────┘
```

### 主流 LLM 价格对比

| 模型 | 输入价格 ($/1M tokens) | 输出价格 ($/1M tokens) | 上下文窗口 |
|------|----------------------|----------------------|-----------|
| GPT-4o | 2.50 | 10.00 | 128K |
| GPT-4o-mini | 0.15 | 0.60 | 128K |
| Claude 3.5 Sonnet | 3.00 | 15.00 | 200K |
| Claude 3.5 Haiku | 0.80 | 4.00 | 200K |
| Gemini 1.5 Pro | 1.25 | 5.00 | 2M |
| DeepSeek V3 | 0.27 | 1.10 | 64K |

### 优化维度全景

```
┌──────────────────────────────────────────────────────────┐
│              Token 节省策略全景                            │
├──────────────────────────────────────────────────────────┤
│                                                          │
│          ┌──────────────────────┐                        │
│          │   用户查询            │                        │
│          └──────────┬───────────┘                        │
│                     │                                    │
│          ┌──────────▼───────────┐                        │
│          │  ① 语义缓存          │  命中 → 直接返回       │
│          │  (Semantic Cache)    │  节省 100% tokens      │
│          └──────────┬───────────┘                        │
│                     │ 未命中                              │
│          ┌──────────▼───────────┐                        │
│          │  ② 模型路由          │  简单问题 → 小模型     │
│          │  (Model Router)     │  节省 50-90% 成本      │
│          └──────────┬───────────┘                        │
│                     │                                    │
│          ┌──────────▼───────────┐                        │
│          │  ③ 精准检索          │  减少无关文档          │
│          │  (Smart Retrieval)  │  节省 30-50% tokens    │
│          └──────────┬───────────┘                        │
│                     │                                    │
│          ┌──────────▼───────────┐                        │
│          │  ④ Prompt 压缩       │  压缩上下文文本        │
│          │  (Compression)      │  节省 40-70% tokens    │
│          └──────────┬───────────┘                        │
│                     │                                    │
│          ┌──────────▼───────────┐                        │
│          │  ⑤ 对话历史管理       │  滑动窗口/摘要        │
│          │  (History Mgmt)     │  节省 20-40% tokens    │
│          └──────────┬───────────┘                        │
│                     │                                    │
│          ┌──────────▼───────────┐                        │
│          │  LLM 生成回答        │                        │
│          └──────────────────────┘                        │
└──────────────────────────────────────────────────────────┘
```

---

## Context Window 管理

### 上下文窗口分配策略

```python
class ContextWindowManager:
    """上下文窗口管理器"""
    
    def __init__(self, max_tokens: int = 128000, model: str = "gpt-4o"):
        self.max_tokens = max_tokens
        self.model = model
        # 预留分配
        self.reserved = {
            "system_prompt": 500,
            "output": 2000,
            "safety_margin": 500,
        }
        self.available = max_tokens - sum(self.reserved.values())
    
    def allocate(self, query_tokens: int, history_tokens: int,
                 context_chunks: list) -> dict:
        """动态分配上下文窗口"""
        remaining = self.available - query_tokens
        
        # 历史占 30%，检索上下文占 70%
        history_budget = min(history_tokens, int(remaining * 0.3))
        context_budget = remaining - history_budget
        
        # 选择最相关的上下文块，直到用完预算
        selected_chunks = []
        used_tokens = 0
        for chunk in context_chunks:  # 已按相关性排序
            chunk_tokens = self._count_tokens(chunk["content"])
            if used_tokens + chunk_tokens <= context_budget:
                selected_chunks.append(chunk)
                used_tokens += chunk_tokens
            else:
                break
        
        return {
            "history_tokens": history_budget,
            "context_tokens": used_tokens,
            "selected_chunks": len(selected_chunks),
            "total_chunks": len(context_chunks),
            "utilization": (query_tokens + history_budget + used_tokens) / self.available
        }
    
    def _count_tokens(self, text: str) -> int:
        import tiktoken
        enc = tiktoken.encoding_for_model(self.model)
        return len(enc.encode(text))
```

### 对话历史管理：滑动窗口 + 自动摘要

```python
class ConversationManager:
    """对话历史管理器"""
    
    def __init__(self, max_history_tokens: int = 3000):
        self.messages = []
        self.max_tokens = max_history_tokens
        self.summary = ""
    
    def add_message(self, role: str, content: str):
        self.messages.append({"role": role, "content": content})
        self._trim_history()
    
    def _trim_history(self):
        """当历史过长时，将早期消息压缩为摘要"""
        import tiktoken
        enc = tiktoken.encoding_for_model("gpt-4o")
        total = sum(len(enc.encode(m["content"])) for m in self.messages)
        
        if total <= self.max_tokens:
            return
        
        keep_recent = 4  # 保留最近 2 轮对话
        if len(self.messages) > keep_recent:
            old = self.messages[:-keep_recent]
            self.messages = self.messages[-keep_recent:]
            self.summary = self._summarize(old)
    
    def _summarize(self, messages: list) -> str:
        """用小模型将历史消息压缩为摘要"""
        from openai import OpenAI
        client = OpenAI()
        history_text = "\n".join(f"{m['role']}: {m['content']}" for m in messages)
        
        resp = client.chat.completions.create(
            model="gpt-4o-mini",
            messages=[{"role": "user",
                       "content": f"用2-3句话概括以下对话要点：\n\n{history_text}"}],
            max_tokens=200
        )
        return resp.choices[0].message.content
    
    def get_context(self) -> list:
        ctx = []
        if self.summary:
            ctx.append({"role": "system", "content": f"对话摘要：{self.summary}"})
        ctx.extend(self.messages)
        return ctx
```

---

## 知识库作为外部记忆

### 核心思路

将原本需要写进 Prompt 的大量背景信息存储到知识库中，按需检索：

```
传统方式（全量 Prompt）：
┌─────────────────────────────────────┐
│ System Prompt (10,000 tokens)       │
│ ├── 公司背景 (2,000 tokens)        │
│ ├── 产品手册全文 (5,000 tokens)    │
│ ├── FAQ 列表 (2,000 tokens)        │
│ └── 回答规范 (1,000 tokens)        │
│ 每次请求都发送全量 = 10,000 tokens   │
└─────────────────────────────────────┘

知识库方式（按需检索）：
┌─────────────────────────────────────┐
│ System Prompt (500 tokens)          │
│ └── 角色定义 + 回答规范             │
│ 检索到的相关上下文 (1,500 tokens)    │
│ └── 仅包含与查询相关的 3 个片段     │
│ 每次请求 = 2,000 tokens             │
│ 节省 80%!                           │
└─────────────────────────────────────┘
```

### 实现示例

```python
class ExternalMemoryRAG:
    """知识库作为外部记忆的 RAG 系统"""
    
    # 精简的 System Prompt（节省 Token）
    SYSTEM_PROMPT = """你是企业客服助手。
要求：1. 基于上下文回答 2. 不确定时说"我不确定" 3. 引用来源"""
    
    def __init__(self, vector_store, llm_client):
        self.vector_store = vector_store
        self.llm = llm_client
    
    def answer(self, query: str, conversation: ConversationManager) -> str:
        # 仅检索最相关的 3 个片段
        chunks = self.vector_store.search(query, top_k=3)
        context = "\n\n".join(c.content for c in chunks)
        
        messages = [
            {"role": "system", "content": self.SYSTEM_PROMPT},
            *conversation.get_context(),
            {"role": "user", "content": f"上下文：\n{context}\n\n问题：{query}"}
        ]
        
        response = self.llm.chat.completions.create(
            model="gpt-4o-mini",
            messages=messages,
            max_tokens=500
        )
        return response.choices[0].message.content
```

---

## Prompt Compression 技术

### LLMLingua / LongLLMLingua

微软开源的 Prompt 压缩工具，通过小模型评估每个 Token 的重要性，去除冗余：

```
原始文本（100 tokens）：
"特斯拉公司是一家美国的电动汽车和清洁能源公司，由马丁·艾伯哈德和
马克·塔彭宁于2003年创立，后来埃隆·马斯克加入并成为最大股东和CEO。
公司总部位于德克萨斯州奥斯汀。主要产品包括电动汽车（Model S/3/X/Y）、
储能产品和太阳能板。"

LLMLingua 压缩后（40 tokens，压缩率 60%）：
"特斯拉 美国电动汽车清洁能源 2003年创立 马斯克CEO 总部德克萨斯
产品 Model S 3 X Y 储能 太阳能"
```

```python
from llmlingua import PromptCompressor

class CompressedRAG:
    """使用 Prompt 压缩的 RAG 系统"""
    
    def __init__(self):
        self.compressor = PromptCompressor(
            model_name="microsoft/llmlingua-2-bert-base-multilingual-cased-meetingbank",
            use_llmlingua2=True,
        )
    
    def compress_context(self, contexts: list[str], query: str,
                         target_ratio: float = 0.5) -> str:
        full_context = "\n\n---\n\n".join(contexts)
        
        compressed = self.compressor.compress_prompt(
            context=[full_context],
            question=query,
            target_token=int(len(full_context.split()) * target_ratio),
            rank_method="longllmlingua",
            use_sentence_level_filter=True,
        )
        return compressed["compressed_prompt"]
    
    def answer_with_compression(self, query: str, contexts: list[str]) -> dict:
        import tiktoken
        enc = tiktoken.encoding_for_model("gpt-4o")
        original_tokens = sum(len(enc.encode(c)) for c in contexts)
        
        compressed = self.compress_context(contexts, query)
        compressed_tokens = len(enc.encode(compressed))
        
        return {
            "compressed_context": compressed,
            "original_tokens": original_tokens,
            "compressed_tokens": compressed_tokens,
            "compression_ratio": 1 - compressed_tokens / original_tokens,
        }
```

### Prompt 压缩方法对比

| 方法 | 原理 | 压缩率 | 质量损失 | 延迟影响 |
|------|------|--------|---------|---------|
| LLMLingua | Token 重要性评分 | 40-70% | 低 | +50ms |
| LongLLMLingua | 长上下文优化压缩 | 50-80% | 低 | +100ms |
| Selective Context | 信息熵句子选择 | 30-50% | 中 | +30ms |
| RECOMP | 训练专用压缩模型 | 50-70% | 低 | +100ms |
| 手工截断 | 只取前 N Token | 可控 | 高 | 0ms |

---

## Semantic Caching（语义缓存）

### 核心思路

传统缓存基于精确匹配，语义缓存基于语义相似度——即使问法不同但含义相近也能命中：

```
传统缓存：
  "特斯拉股价"       → Hit ✓
  "TSLA 的价格"      → Miss ✗  （字面不同）

语义缓存：
  "特斯拉股价"       → Hit ✓
  "TSLA 的价格"      → Hit ✓  （语义相同）
  "特斯拉今天股价多少" → Hit ✓  （语义相似）
```

### 实现方案

```python
import numpy as np
from datetime import datetime, timedelta
from typing import Optional

class SemanticCache:
    """基于向量相似度的语义缓存"""
    
    def __init__(self, embedding_model, threshold: float = 0.92,
                 ttl_seconds: int = 3600):
        self.embedding_model = embedding_model
        self.threshold = threshold
        self.ttl = ttl_seconds
        self.cache_embeddings = []
        self.cache_entries = []
    
    def get(self, query: str) -> Optional[str]:
        if not self.cache_embeddings:
            return None
        
        query_emb = self.embedding_model.encode(query)
        sims = [self._cosine_sim(query_emb, c) for c in self.cache_embeddings]
        max_idx = np.argmax(sims)
        
        if sims[max_idx] >= self.threshold:
            entry = self.cache_entries[max_idx]
            if datetime.now() - entry["timestamp"] < timedelta(seconds=self.ttl):
                entry["hit_count"] += 1
                return entry["answer"]
            else:
                self._remove(max_idx)
        return None
    
    def set(self, query: str, answer: str):
        self.cache_embeddings.append(self.embedding_model.encode(query))
        self.cache_entries.append({
            "query": query, "answer": answer,
            "timestamp": datetime.now(), "hit_count": 0,
        })
    
    def _cosine_sim(self, a, b):
        return np.dot(a, b) / (np.linalg.norm(a) * np.linalg.norm(b))
    
    def _remove(self, idx):
        self.cache_embeddings.pop(idx)
        self.cache_entries.pop(idx)
```

### 生产级方案：Redis + 向量搜索

```python
class RedisSemanticCache:
    """基于 Redis 的生产级语义缓存"""
    
    def __init__(self, redis_client, embedding_model,
                 index_name="sem_cache", threshold=0.92, ttl=3600):
        self.redis = redis_client
        self.embedding_model = embedding_model
        self.index_name = index_name
        self.threshold = threshold
        self.ttl = ttl
        self._create_index()
    
    def _create_index(self):
        from redis.commands.search.field import VectorField, TextField
        from redis.commands.search.indexDefinition import IndexDefinition, IndexType
        try:
            self.redis.ft(self.index_name).info()
        except:
            schema = (
                TextField("query"), TextField("answer"),
                VectorField("embedding", "HNSW", {
                    "TYPE": "FLOAT32", "DIM": 1024,
                    "DISTANCE_METRIC": "COSINE"
                }),
            )
            self.redis.ft(self.index_name).create_index(
                schema, definition=IndexDefinition(prefix=["cache:"], index_type=IndexType.HASH)
            )
    
    def get(self, query: str) -> Optional[str]:
        from redis.commands.search.query import Query
        emb = np.array(self.embedding_model.encode(query), dtype=np.float32).tobytes()
        q = Query("*=>[KNN 1 @embedding $vec AS score]").sort_by("score").return_fields("answer", "score").dialect(2)
        results = self.redis.ft(self.index_name).search(q, query_params={"vec": emb})
        if results.docs:
            sim = 1 - float(results.docs[0].score)
            if sim >= self.threshold:
                return results.docs[0].answer
        return None
    
    def set(self, query: str, answer: str):
        import uuid
        emb = np.array(self.embedding_model.encode(query), dtype=np.float32).tobytes()
        key = f"cache:{uuid.uuid4().hex}"
        self.redis.hset(key, mapping={"query": query, "answer": answer, "embedding": emb})
        self.redis.expire(key, self.ttl)
```

### 缓存命中率优化

| 策略 | 说明 | 效果 |
|------|------|------|
| 查询标准化 | 去标点、统一大小写、去停用词 | +10-15% 命中率 |
| 阈值调优 | 根据场景调整相似度阈值 | 平衡命中率与准确率 |
| 分层缓存 | 精确缓存 + 语义缓存双层 | +20-30% 命中率 |
| 预热缓存 | 高频问题预写入 | 冷启动 +50% 命中率 |

---

## 混合检索降低冗余

### 问题：检索冗余浪费 Token

```
Query: "如何部署 Milvus？"

检索结果（未去冗余）：
  [1] Milvus 单机部署指南...（0.95）
  [2] Milvus standalone 安装步骤...（0.93）← 与[1]高度重叠
  [3] Milvus Docker 部署...（0.91）← 与[1]部分重叠
  → [1][2][3] 内容重叠，浪费 Token
```

### MMR 多样性检索

```python
class DiverseRetriever:
    """MMR（Maximal Marginal Relevance）多样性检索"""
    
    def __init__(self, vector_store, embedding_model):
        self.vector_store = vector_store
        self.embedding_model = embedding_model
    
    def search_mmr(self, query: str, top_k: int = 5,
                   diversity: float = 0.7, initial_k: int = 20) -> list:
        candidates = self.vector_store.search(query, top_k=initial_k)
        if not candidates:
            return []
        
        query_emb = self.embedding_model.encode(query)
        cand_embs = [self.embedding_model.encode(c.content) for c in candidates]
        
        selected, sel_embs, remaining = [], [], list(range(len(candidates)))
        
        for _ in range(min(top_k, len(candidates))):
            scores = []
            for idx in remaining:
                relevance = self._cosine(query_emb, cand_embs[idx])
                redundancy = max(
                    (self._cosine(cand_embs[idx], e) for e in sel_embs), default=0
                )
                # MMR = λ * relevance - (1-λ) * redundancy
                scores.append((idx, diversity * relevance - (1-diversity) * redundancy))
            
            best_idx = max(scores, key=lambda x: x[1])[0]
            selected.append(candidates[best_idx])
            sel_embs.append(cand_embs[best_idx])
            remaining.remove(best_idx)
        
        return selected
    
    def _cosine(self, a, b):
        return np.dot(a, b) / (np.linalg.norm(a) * np.linalg.norm(b))
```

---

## 模型路由策略

### 核心思路

并非所有查询都需要最强模型。根据复杂度路由到不同模型，保质降本：

```
┌──────────────────────────────────────────────────────┐
│  查询复杂度        模型选择          成本               │
├──────────────────────────────────────────────────────┤
│  简单（闲聊/确认）  GPT-4o-mini     $0.15/1M          │
│  中等（知识问答）   GPT-4o-mini     $0.15/1M          │
│  复杂（推理/分析）  GPT-4o          $2.50/1M          │
│                                                      │
│  70% 简单/中等 + 30% 复杂 → 平均成本降低 ~60%         │
└──────────────────────────────────────────────────────┘
```

### 实现方案

```python
from enum import Enum

class QueryComplexity(Enum):
    SIMPLE = "simple"
    MODERATE = "moderate"
    COMPLEX = "complex"

class ModelRouter:
    """智能模型路由器"""
    
    MODEL_CONFIG = {
        QueryComplexity.SIMPLE: {"model": "gpt-4o-mini", "max_tokens": 300},
        QueryComplexity.MODERATE: {"model": "gpt-4o-mini", "max_tokens": 800},
        QueryComplexity.COMPLEX: {"model": "gpt-4o", "max_tokens": 2000},
    }
    
    # 复杂度判断关键词
    COMPLEX_KEYWORDS = ["分析", "对比", "推理", "为什么", "优化", "设计", "代码"]
    SIMPLE_KEYWORDS = ["你好", "谢谢", "是的", "不是", "好的"]
    
    def route(self, query: str) -> dict:
        complexity = self._classify(query)
        return self.MODEL_CONFIG[complexity]
    
    def _classify(self, query: str) -> QueryComplexity:
        if any(k in query for k in self.SIMPLE_KEYWORDS) and len(query) < 10:
            return QueryComplexity.SIMPLE
        if any(k in query for k in self.COMPLEX_KEYWORDS) or len(query) > 200:
            return QueryComplexity.COMPLEX
        return QueryComplexity.MODERATE


class CostAwareRAG:
    """成本感知的 RAG 系统"""
    
    def __init__(self, vector_store, router: ModelRouter, cache: SemanticCache):
        self.vector_store = vector_store
        self.router = router
        self.cache = cache
        self.total_cost = 0.0
    
    def answer(self, query: str) -> dict:
        # 1. 语义缓存检查
        cached = self.cache.get(query)
        if cached:
            return {"answer": cached, "cost": 0, "source": "cache"}
        
        # 2. 模型路由
        config = self.router.route(query)
        
        # 3. 检索 + 生成
        chunks = self.vector_store.search(query, top_k=3)
        context = "\n".join(c.content for c in chunks)
        
        from openai import OpenAI
        resp = OpenAI().chat.completions.create(
            model=config["model"],
            messages=[
                {"role": "system", "content": "基于上下文回答问题。"},
                {"role": "user", "content": f"上下文：{context}\n\n问题：{query}"}
            ],
            max_tokens=config["max_tokens"]
        )
        
        answer = resp.choices[0].message.content
        cost = self._calc_cost(resp.usage, config["model"])
        self.total_cost += cost
        
        # 4. 写入缓存
        self.cache.set(query, answer)
        
        return {"answer": answer, "cost": cost, "model": config["model"]}
    
    def _calc_cost(self, usage, model: str) -> float:
        prices = {
            "gpt-4o": (2.5, 10.0),
            "gpt-4o-mini": (0.15, 0.60),
        }
        input_price, output_price = prices.get(model, (2.5, 10.0))
        return (usage.prompt_tokens * input_price + usage.completion_tokens * output_price) / 1_000_000
```

---

## 成本监控与预算控制

### 监控指标

```python
from dataclasses import dataclass, field
from datetime import datetime
from collections import defaultdict

@dataclass
class CostTracker:
    """Token 成本追踪器"""
    
    daily_budget: float = 100.0  # 日预算（美元）
    alert_threshold: float = 0.8  # 80% 时告警
    
    total_tokens: int = 0
    total_cost: float = 0.0
    request_count: int = 0
    cache_hits: int = 0
    
    model_stats: dict = field(default_factory=lambda: defaultdict(lambda: {"tokens": 0, "cost": 0, "count": 0}))
    hourly_cost: dict = field(default_factory=lambda: defaultdict(float))
    
    def record(self, model: str, input_tokens: int, output_tokens: int, cost: float, cached: bool = False):
        """记录一次请求"""
        self.request_count += 1
        
        if cached:
            self.cache_hits += 1
            return
        
        self.total_tokens += input_tokens + output_tokens
        self.total_cost += cost
        
        self.model_stats[model]["tokens"] += input_tokens + output_tokens
        self.model_stats[model]["cost"] += cost
        self.model_stats[model]["count"] += 1
        
        hour = datetime.now().strftime("%Y-%m-%d %H:00")
        self.hourly_cost[hour] += cost
        
        # 预算检查
        if self.total_cost >= self.daily_budget * self.alert_threshold:
            self._alert(f"日预算已使用 {self.total_cost/self.daily_budget:.0%}")
    
    def report(self) -> dict:
        return {
            "total_requests": self.request_count,
            "cache_hit_rate": self.cache_hits / max(self.request_count, 1),
            "total_tokens": self.total_tokens,
            "total_cost": f"${self.total_cost:.4f}",
            "avg_cost_per_request": f"${self.total_cost / max(self.request_count - self.cache_hits, 1):.4f}",
            "budget_utilization": f"{self.total_cost / self.daily_budget:.1%}",
            "model_breakdown": dict(self.model_stats),
        }
    
    def _alert(self, message: str):
        print(f"[COST ALERT] {message}")
```

### 成本优化效果总结

| 策略 | Token 节省 | 成本降低 | 实施难度 | 质量影响 |
|------|-----------|---------|---------|---------|
| 语义缓存 | 100%（命中时） | 30-50%（整体） | 中 | 无 |
| 模型路由 | 0% | 50-70% | 低 | 低 |
| Prompt 压缩 | 40-70% | 30-50% | 中 | 低 |
| 知识库外部记忆 | 60-80% | 50-70% | 低 | 无 |
| MMR 去冗余 | 20-40% | 15-30% | 低 | 无（提升） |
| 对话历史摘要 | 30-50% | 20-35% | 中 | 低 |
| **组合使用** | — | **70-90%** | 中高 | 低 |

---

## 实战练习

### 练习 1：构建成本优化 RAG 系统

```
目标：构建一个集成所有 Token 节省策略的 RAG 系统
要求：
1. 语义缓存层（Redis + 向量搜索）
2. 模型路由（根据复杂度选模型）
3. Prompt 压缩（LLMLingua）
4. MMR 去冗余检索
5. 成本追踪和日报
评估：对比优化前后的 Token 消耗和成本
```

### 练习 2：实现对话历史智能管理

```
目标：实现一个能自动管理对话历史的助手
要求：
1. 滑动窗口保留最近 N 轮对话
2. 早期对话自动压缩为摘要
3. 关键信息永久保留（用户偏好/约束）
4. Token 预算动态分配
评估：对比固定窗口 vs 智能管理的回答质量和 Token 消耗
```

### 练习 3：语义缓存性能调优

```
目标：调优语义缓存的命中率和准确率
要求：
1. 收集 1000 个真实查询作为测试集
2. 测试不同相似度阈值（0.85/0.90/0.92/0.95）
3. 评估命中率、准确率和误命中率
4. 实现查询标准化（去停用词、同义词替换）
5. 对比使用不同 Embedding 模型的效果
评估：找到最优阈值和配置
```

---

## 本章小结

| 主题 | 关键要点 |
|------|---------|
| Token 成本 | 检索上下文占 60% Token，是优化的重点 |
| Context 管理 | 动态分配上下文窗口，历史占 30%、检索占 70% |
| 外部记忆 | 用知识库替代全量 Prompt，节省 80% Token |
| Prompt 压缩 | LLMLingua 可压缩 40-70%，质量损失小 |
| 语义缓存 | 相似查询直接命中，节省 100% Token |
| 去冗余检索 | MMR 算法确保检索结果多样性 |
| 模型路由 | 简单问题用小模型，成本降低 60% |
| 成本监控 | 实时追踪 Token 消耗，设置预算告警 |

---

*上一篇：[09-实时知识获取](09-realtime-knowledge.md)*

*下一篇：[11-Milvus 深度解析](11-milvus-deep-dive.md)*

*返回目录：[README](README.md)*
