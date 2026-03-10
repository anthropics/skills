# 向量数据库详解

> 向量数据库是知识库的"存储引擎"，支撑高效的语义检索。

## 目录

- [核心概念](#核心概念)
- [索引算法详解](#索引算法详解)
- [相似度计算](#相似度计算)
- [主流数据库选型对比](#主流数据库选型对比)
- [Milvus 深度实战](#milvus-深度实战)
- [混合搜索](#混合搜索)
- [生产部署最佳实践](#生产部署最佳实践)
- [性能调优](#性能调优)
- [实战练习](#实战练习)

---

## 核心概念

### 向量数据库 vs 传统数据库

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    向量数据库核心概念                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   传统数据库 (MySQL):                                                       │
│   ┌──────────────────────────────────────────┐                             │
│   │  SELECT * FROM docs WHERE title = 'RAG'   │                             │
│   │  精确匹配: title 字段 = "RAG"              │                             │
│   │  索引: B-Tree                               │                             │
│   └──────────────────────────────────────────┘                             │
│                                                                             │
│   向量数据库 (Milvus):                                                      │
│   ┌──────────────────────────────────────────┐                             │
│   │  search(query_vector, top_k=5)            │                             │
│   │  近似匹配: 找到最相似的 K 个向量           │                             │
│   │  索引: HNSW / IVF / PQ                     │                             │
│   └──────────────────────────────────────────┘                             │
│                                                                             │
│   关键区别:                                                                 │
│   • 传统: 精确匹配 (Exact Match) → O(log n)                                │
│   • 向量: 近似最近邻 (ANN) → O(log n) ~ O(1)                               │
│   • ANN 牺牲少量精度换取巨大性能提升                                        │
│                                                                             │
│   精确 KNN: 比较所有向量 → O(n×d)，百万级就不可用                          │
│   近似 ANN: 通过索引结构 → O(log n)，十亿级仍可用                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 索引算法详解

### HNSW (Hierarchical Navigable Small World)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         HNSW 算法详解                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   原理: 多层图结构，类似"高速公路 + 普通道路"                               │
│                                                                             │
│   Layer 3 (最稀疏):     A ─────────────────── B                            │
│                          │                     │                            │
│   Layer 2:              A ──── C ──── B ──── D                             │
│                          │     │     │     │                               │
│   Layer 1:              A ─ E ─ C ─ F ─ B ─ G ─ D                         │
│                          │ │ │ │ │ │ │ │ │ │ │                            │
│   Layer 0 (最稠密):     A E H C I F J B K G L D                           │
│                                                                             │
│   搜索过程 (找到最接近 query 的节点):                                       │
│   1. 从最高层的入口节点开始                                                 │
│   2. 在当前层贪心搜索最近邻 → 找到局部最优                                 │
│   3. 下降到下一层，继续搜索 → 逐层精细化                                   │
│   4. 在最底层找到最终结果                                                   │
│                                                                             │
│   关键参数:                                                                 │
│   • M: 每个节点的最大连接数 (推荐 16-64)                                   │
│   • efConstruction: 构建时搜索宽度 (推荐 128-512, 越大越准但越慢)          │
│   • ef: 搜索时搜索宽度 (推荐 64-256, 可动态调整)                           │
│                                                                             │
│   复杂度:                                                                   │
│   • 构建: O(n × log n)                                                     │
│   • 搜索: O(log n)                                                         │
│   • 内存: O(n × M × 层数) ← 较大                                          │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### IVF (Inverted File Index)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         IVF 算法详解                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   原理: 先将向量聚类，搜索时只检查最近的几个聚类                            │
│                                                                             │
│   训练阶段 (K-Means 聚类):                                                  │
│   ┌─────────────────────────────────────────────────────────────────┐       │
│   │                                                                 │       │
│   │    ○ ○ ○        △ △ △ △         □ □ □                          │       │
│   │   ○ ○ ○ ○      △ △ △          □ □ □ □                          │       │
│   │    ○ ○ ○        △ △ △ △         □ □ □                          │       │
│   │                                                                 │       │
│   │   聚类中心1     聚类中心2       聚类中心3                        │       │
│   │                                                                 │       │
│   └─────────────────────────────────────────────────────────────────┘       │
│                                                                             │
│   搜索阶段:                                                                 │
│   1. 计算 query 与所有聚类中心的距离                                        │
│   2. 选择最近的 nprobe 个聚类                                               │
│   3. 在选中的聚类内暴力搜索                                                 │
│                                                                             │
│   关键参数:                                                                 │
│   • nlist: 聚类数量 (推荐 sqrt(n) ~ 4*sqrt(n))                             │
│   • nprobe: 搜索时检查的聚类数 (推荐 nlist 的 5%-10%)                      │
│                                                                             │
│   复杂度:                                                                   │
│   • 构建: O(n × k × iterations) (K-Means 训练)                             │
│   • 搜索: O(nprobe × n/nlist × d)                                          │
│   • 内存: O(n × d) ← 可接受                                               │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### PQ (Product Quantization)

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         PQ 算法详解                                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   原理: 将高维向量切分为子空间，各子空间独立量化                            │
│                                                                             │
│   原始向量 (1024维):                                                        │
│   [0.12, -0.34, 0.56, ..., 0.78, -0.23, 0.45, ..., 0.89, -0.11, ...]     │
│   ├──── 子空间1 ────┤├──── 子空间2 ────┤├──── 子空间M ────┤               │
│                                                                             │
│   每个子空间:                                                               │
│   • 用 K-Means 训练 256 个聚类中心 (码本)                                  │
│   • 每个子向量量化为最近中心的编号 (1 byte)                                 │
│                                                                             │
│   压缩效果:                                                                 │
│   原始: 1024 维 × 4 bytes = 4096 bytes                                     │
│   PQ (M=128): 128 子空间 × 1 byte = 128 bytes                             │
│   压缩率: 32x                                                              │
│                                                                             │
│   常见组合:                                                                 │
│   • IVF + PQ: 先聚类后量化 (大规模标配)                                    │
│   • HNSW + PQ: 图导航 + 量化 (兼顾速度和存储)                              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 索引算法对比

| 算法 | 查询延迟 | 召回率 | 内存占用 | 构建时间 | 适用规模 |
|------|----------|--------|----------|----------|----------|
| **Flat (暴力)** | O(n) | 100% | 低 | 快 | < 10万 |
| **HNSW** | O(log n) | 99%+ | 高 | 慢 | < 1000万 |
| **IVF** | 中等 | 95-99% | 中 | 中 | 千万-亿 |
| **PQ** | 快 | 90-95% | 很低 | 中 | 亿-十亿 |
| **IVF+PQ** | 快 | 92-97% | 低 | 中 | 亿+ |
| **HNSW+PQ** | 快 | 95-99% | 中 | 慢 | 千万-亿 |

---

## 相似度计算

| 度量 | 说明 | 范围 | Milvus 参数 |
|------|------|------|-------------|
| **COSINE** | 余弦相似度 | [-1, 1] | `metric_type="COSINE"` |
| **IP** | 内积 (需归一化) | (-∞, +∞) | `metric_type="IP"` |
| **L2** | 欧氏距离 | [0, +∞) | `metric_type="L2"` |

**推荐**: 文本检索使用 `COSINE`（最直观），归一化后等价于 `IP`（最快）。

---

## Milvus 深度实战

### 完整 CRUD 示例

```python
from pymilvus import (
    connections, Collection, CollectionSchema,
    FieldSchema, DataType, utility
)
import numpy as np

# 1. 连接
connections.connect("default", host="localhost", port="19530")

# 2. 定义 Schema
fields = [
    FieldSchema(name="id", dtype=DataType.INT64, is_primary=True, auto_id=True),
    FieldSchema(name="text", dtype=DataType.VARCHAR, max_length=4096),
    FieldSchema(name="embedding", dtype=DataType.FLOAT_VECTOR, dim=1024),
    FieldSchema(name="source", dtype=DataType.VARCHAR, max_length=512),
    FieldSchema(name="timestamp", dtype=DataType.INT64),
]
schema = CollectionSchema(fields, description="AI Infra Knowledge Base")

# 3. 创建 Collection
if utility.has_collection("ai_infra_kb"):
    utility.drop_collection("ai_infra_kb")
collection = Collection("ai_infra_kb", schema)

# 4. 创建索引 (HNSW)
index_params = {
    "metric_type": "COSINE",
    "index_type": "HNSW",
    "params": {"M": 32, "efConstruction": 256}
}
collection.create_index("embedding", index_params)

# 5. 插入数据
import time
texts = ["ZeRO-3 将参数分片到所有 GPU", "HNSW 是一种图索引算法"]
embeddings = np.random.randn(2, 1024).tolist()  # 实际使用 Embedding 模型
sources = ["distributed-training.md", "vector-db.md"]
timestamps = [int(time.time())] * 2

collection.insert([texts, embeddings, sources, timestamps])
collection.flush()

# 6. 搜索
collection.load()
query_embedding = np.random.randn(1, 1024).tolist()

results = collection.search(
    data=query_embedding,
    anns_field="embedding",
    param={"metric_type": "COSINE", "params": {"ef": 128}},
    limit=5,
    output_fields=["text", "source"],
    expr='source == "distributed-training.md"'  # 元数据过滤
)

for hits in results:
    for hit in hits:
        print(f"  Score: {hit.score:.4f} | {hit.entity.get('text')[:80]}")

# 7. 删除
collection.delete(expr='source == "old-doc.md"')

# 8. 清理
collection.release()
connections.disconnect("default")
```

---

## 混合搜索

### 向量 + 关键词混合

```python
from pymilvus import Collection, AnnSearchRequest, RRFRanker

collection = Collection("knowledge_base")
collection.load()

# 1. 向量搜索请求
vector_req = AnnSearchRequest(
    data=[query_embedding],
    anns_field="dense_embedding",
    param={"metric_type": "COSINE", "params": {"ef": 128}},
    limit=20
)

# 2. 稀疏向量搜索请求 (BM25-like)
sparse_req = AnnSearchRequest(
    data=[sparse_query],
    anns_field="sparse_embedding",
    param={"metric_type": "IP"},
    limit=20
)

# 3. 混合搜索 + RRF 融合排序
results = collection.hybrid_search(
    reqs=[vector_req, sparse_req],
    ranker=RRFRanker(k=60),  # Reciprocal Rank Fusion
    limit=5,
    output_fields=["text", "source"]
)
```

### RRF (Reciprocal Rank Fusion) 原理

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    RRF 融合排序                                              │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   向量搜索结果:        关键词搜索结果:       RRF 融合结果:                  │
│   1. DocA (0.95)       1. DocC (12.3)       1. DocA  (1/61 + 1/63 = 0.032)│
│   2. DocB (0.91)       2. DocA (11.8)       2. DocC  (1/63 + 1/61 = 0.032)│
│   3. DocC (0.88)       3. DocD (10.5)       3. DocB  (1/62 + 1/65 = 0.031)│
│   4. DocD (0.85)       4. DocE (9.2)        4. DocD  (1/64 + 1/63 = 0.031)│
│   5. DocE (0.82)       5. DocB (8.7)        5. DocE  (1/65 + 1/64 = 0.031)│
│                                                                             │
│   RRF Score = Σ 1/(k + rank_i)，k 通常取 60                                │
│   优势: 不需要对不同检索方式的分数进行归一化                                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 生产部署最佳实践

### 部署架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Milvus 生产部署架构                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                         客户端 (SDK)                                 │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│   ┌───────────────────────────▼─────────────────────────────────────────┐   │
│   │                       Milvus Proxy                                   │   │
│   │                   (负载均衡 + 路由)                                   │   │
│   └────┬──────────┬──────────┬──────────┬───────────────────────────────┘   │
│        │          │          │          │                                   │
│   ┌────▼────┐ ┌───▼────┐ ┌──▼─────┐ ┌──▼─────┐                           │
│   │ Query   │ │ Data   │ │ Index  │ │ Coord  │                           │
│   │ Node    │ │ Node   │ │ Node   │ │ Nodes  │                           │
│   │ (搜索)  │ │ (写入) │ │ (索引) │ │ (协调) │                           │
│   └─────────┘ └────────┘ └────────┘ └────────┘                           │
│        │          │          │                                              │
│   ┌────▼──────────▼──────────▼──────────────────────────────────────────┐   │
│   │                      存储层                                          │   │
│   │   MinIO/S3 (对象存储)  │  etcd (元数据)  │  Pulsar/Kafka (日志)      │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Kubernetes 部署

```bash
# 使用 Helm 部署 Milvus 集群
helm repo add milvus https://zilliztech.github.io/milvus-helm/
helm repo update

helm install milvus milvus/milvus \
    --set cluster.enabled=true \
    --set queryNode.replicas=2 \
    --set dataNode.replicas=2 \
    --set indexNode.replicas=1 \
    --set proxy.replicas=2 \
    --namespace milvus \
    --create-namespace
```

---

## 性能调优

### 索引参数调优指南

| 参数 | 说明 | 推荐值 | 影响 |
|------|------|--------|------|
| **HNSW M** | 连接数 | 16-64 | 越大召回越高，内存越大 |
| **HNSW efConstruction** | 构建搜索宽度 | 128-512 | 越大索引越慢但质量越好 |
| **HNSW ef** | 查询搜索宽度 | 64-256 | 越大越准但越慢 |
| **IVF nlist** | 聚类数 | 4×√n | 越多分辨率越高 |
| **IVF nprobe** | 搜索聚类数 | nlist×5%-10% | 越多越准但越慢 |

### 调优策略

```python
# 性能测试与调优
import time

def benchmark_search_params(collection, query_emb, ground_truth, params_list):
    """测试不同参数下的延迟和召回率"""
    for params in params_list:
        latencies = []
        for _ in range(100):
            start = time.time()
            results = collection.search(
                data=[query_emb],
                anns_field="embedding",
                param={"metric_type": "COSINE", "params": params},
                limit=10
            )
            latencies.append(time.time() - start)
        
        # 计算召回率
        retrieved_ids = {hit.id for hits in results for hit in hits}
        recall = len(retrieved_ids & ground_truth) / len(ground_truth)
        
        avg_latency = sum(latencies) / len(latencies) * 1000
        p99_latency = sorted(latencies)[98] * 1000
        
        print(f"  params={params}")
        print(f"  Recall: {recall:.2%}, Avg: {avg_latency:.1f}ms, P99: {p99_latency:.1f}ms")

# 测试不同 ef 值
benchmark_search_params(collection, query_emb, truth, [
    {"ef": 64},
    {"ef": 128},
    {"ef": 256},
    {"ef": 512},
])
```

---

## 实战练习

### 练习 1：搭建本地 Milvus

```bash
# 使用 Docker Compose 启动 Milvus Standalone
wget https://github.com/milvus-io/milvus/releases/download/v2.4.0/milvus-standalone-docker-compose.yml -O docker-compose.yml
docker compose up -d

# 验证
python -c "
from pymilvus import connections, utility
connections.connect('default', host='localhost', port='19530')
print('Milvus version:', utility.get_server_version())
print('连接成功!')
"
```

### 练习 2：索引算法对比实验

```python
# index_comparison.py
from pymilvus import connections, Collection, CollectionSchema, FieldSchema, DataType
import numpy as np
import time

connections.connect("default", host="localhost", port="19530")

dim = 1024
num_vectors = 100000

# 生成测试数据
vectors = np.random.randn(num_vectors, dim).astype(np.float32)

# 测试不同索引
indexes = [
    {"type": "FLAT", "params": {}},
    {"type": "HNSW", "params": {"M": 16, "efConstruction": 256}},
    {"type": "IVF_FLAT", "params": {"nlist": 1024}},
    {"type": "IVF_PQ", "params": {"nlist": 1024, "m": 32, "nbits": 8}},
]

for idx_config in indexes:
    # 创建 collection, 插入数据, 创建索引, 搜索, 计时
    print(f"\n索引类型: {idx_config['type']}")
    # ... 实现对比逻辑 ...
```

---

*上一篇：[03-Embedding 模型](03-embedding-models.md)*

*下一篇：[05-从零构建知识库](05-build-from-scratch.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Milvus.** *Milvus Documentation.*  
   https://milvus.io/docs/

2. **Pinecone.** *Vector Database Docs.*  
   https://docs.pinecone.io/

3. **Weaviate.** *Vector Search Engine.*  
   https://weaviate.io/

4. **Johnson, J., Douze, M., & Jégou, H. (2019).** *Billion-scale similarity search with GPUs (FAISS).* IEEE Trans. Big Data.  
   https://arxiv.org/abs/1702.08734
