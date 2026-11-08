# 知识库（Knowledge Base）详解

> 让 LLM 获取外部知识，消除幻觉，回答实时问题，降低推理成本。

---

> 📚 **更详细的内容**: 本章节已扩展为独立的子文件夹，包含更深入的主题文档。
>
> 👉 **推荐阅读**: [07-knowledge-base/](./07-knowledge-base/README.md)
>
> | 主题 | 链接 |
> |------|------|
> | 什么是知识库 | [01-what-is-knowledge-base.md](./07-knowledge-base/01-what-is-knowledge-base.md) |
> | 技术栈详解 | [02-tech-stack.md](./07-knowledge-base/02-tech-stack.md) |
> | Embedding 模型 | [03-embedding-models.md](./07-knowledge-base/03-embedding-models.md) |
> | 向量数据库 | [04-vector-databases.md](./07-knowledge-base/04-vector-databases.md) |
> | 从零构建知识库 | [05-build-from-scratch.md](./07-knowledge-base/05-build-from-scratch.md) |
> | RAG 基础 | [06-rag-fundamentals.md](./07-knowledge-base/06-rag-fundamentals.md) |
> | 高级 RAG 技术 | [07-advanced-rag.md](./07-knowledge-base/07-advanced-rag.md) |
> | 消除幻觉与质量提升 | [08-eliminate-hallucination.md](./07-knowledge-base/08-eliminate-hallucination.md) |
> | 实时知识获取 | [09-realtime-knowledge.md](./07-knowledge-base/09-realtime-knowledge.md) |
> | Token 节省策略 | [10-token-optimization.md](./07-knowledge-base/10-token-optimization.md) |
> | Milvus 深度解析 | [11-milvus-deep-dive.md](./07-knowledge-base/11-milvus-deep-dive.md) |

---

## 目录

- [什么是知识库](#什么是知识库)
- [技术栈全景](#技术栈全景)
- [Embedding 模型](#embedding-模型)
- [向量数据库](#向量数据库)
- [从零构建知识库](#从零构建知识库)
- [RAG 基础架构](#rag-基础架构)
- [高级 RAG 技术](#高级-rag-技术)
- [消除幻觉与质量提升](#消除幻觉与质量提升)
- [实时知识获取](#实时知识获取)
- [Token 节省策略](#token-节省策略)
- [实战练习](#实战练习)

---

## 什么是知识库

### 定义

知识库（Knowledge Base）是 AI 系统中用于存储、检索和管理外部知识的结构化或半结构化数据系统，让 LLM 能够访问训练数据之外的信息。

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       知识库在 AI 系统中的角色                            │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────────┐                                                   │
│   │   用户提问       │                                                   │
│   │  "特斯拉今天     │                                                   │
│   │   股价多少？"    │                                                   │
│   └────────┬────────┘                                                   │
│            │                                                             │
│            ▼                                                             │
│   ┌─────────────────┐    ┌─────────────────────────────────────┐       │
│   │    检索系统      │───▶│         知识库 (Knowledge Base)      │       │
│   │  Query → Docs   │    │                                     │       │
│   └────────┬────────┘    │  • 公司文档、FAQ                     │       │
│            │              │  • 实时数据 (股票、天气)             │       │
│            ▼              │  • 行业知识、法规                    │       │
│   ┌─────────────────┐    │  • 产品手册、代码库                  │       │
│   │    LLM 生成      │    └─────────────────────────────────────┘       │
│   │  Context + Query │                                                   │
│   │  → 准确回答      │                                                   │
│   └─────────────────┘                                                   │
│                                                                         │
│   没有知识库: "我无法获取实时股票数据"（幻觉或拒答）                     │
│   有知识库:   "特斯拉 (TSLA) 当前股价为 $248.50，涨幅 2.3%"            │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 知识库分类

| 类型 | 描述 | 代表技术 | 适用场景 |
|------|------|----------|----------|
| **向量知识库** | 基于 Embedding 的语义检索 | Milvus, Pinecone, Chroma | 语义搜索、RAG |
| **图谱知识库** | 基于实体-关系的结构化知识 | Neo4j, ArangoDB | 推理、关系分析 |
| **全文知识库** | 基于关键词的传统检索 | Elasticsearch, OpenSearch | 精确匹配、日志搜索 |
| **混合知识库** | 多种检索方式组合 | Milvus + ES + Neo4j | 复杂问答、企业级应用 |

### 知识库 vs 传统数据库

| 维度 | 传统数据库 | AI 知识库 |
|------|-----------|-----------|
| **查询方式** | 精确查询 (SQL) | 语义相似度查询 |
| **数据形式** | 结构化行列 | 文本 + 向量 + 元数据 |
| **核心目标** | ACID 事务 | 高召回率 + 低延迟 |
| **索引方式** | B-Tree / Hash | HNSW / IVF / PQ |
| **典型延迟** | < 1ms | 10-100ms |

---

## 技术栈全景

### 知识库技术栈架构

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       知识库技术栈全景图                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                     应用层 (Application)                         │   │
│   │   LangChain │ LlamaIndex │ Haystack │ Dify │ FastGPT │ RAGFlow │   │
│   └───────────────────────────┬─────────────────────────────────────┘   │
│                               │                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                   检索编排层 (Retrieval Orchestration)           │   │
│   │   Query Rewriting │ HyDE │ Re-ranking │ Multi-hop │ Routing     │   │
│   └───────────────────────────┬─────────────────────────────────────┘   │
│                               │                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                     Embedding 层 (Encoding)                      │   │
│   │   OpenAI │ BGE │ E5 │ Cohere │ Jina │ Voyage │ GTE │ CLIP      │   │
│   └───────────────────────────┬─────────────────────────────────────┘   │
│                               │                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                     存储检索层 (Storage & Retrieval)              │   │
│   │                                                                   │   │
│   │   向量数据库              全文搜索              图数据库          │   │
│   │   Milvus                 Elasticsearch          Neo4j            │   │
│   │   Pinecone               OpenSearch              ArangoDB        │   │
│   │   Weaviate               MeiliSearch             Amazon Neptune  │   │
│   │   Qdrant                 Typesense                               │   │
│   │   Chroma                                                         │   │
│   └───────────────────────────┬─────────────────────────────────────┘   │
│                               │                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                     数据处理层 (Data Processing)                  │   │
│   │   Unstructured │ LlamaParse │ Docling │ Apache Tika │ Marker     │   │
│   │   文档解析 │ 分块 │ 清洗 │ 元数据提取 │ OCR │ 表格识别          │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 核心组件选型

| 组件 | 开源方案 | 商业方案 | 选型建议 |
|------|----------|----------|----------|
| **向量数据库** | Milvus, Qdrant, Chroma | Pinecone, Zilliz | 生产用 Milvus/Qdrant，原型用 Chroma |
| **Embedding** | BGE, E5, GTE | OpenAI, Cohere, Voyage | 中文用 BGE，英文用 E5/OpenAI |
| **文档解析** | Unstructured, Docling | LlamaParse | 通用用 Unstructured，PDF 用 LlamaParse |
| **编排框架** | LangChain, LlamaIndex | — | 灵活性用 LangChain，RAG 专精用 LlamaIndex |
| **全文搜索** | Elasticsearch, OpenSearch | Algolia | 企业用 ES，轻量用 MeiliSearch |
| **图数据库** | Neo4j Community | Neo4j Enterprise | 知识图谱场景 |

---

## Embedding 模型

### 文本 Embedding 原理

```
┌─────────────────────────────────────────────────────────────────────────┐
│                     文本 Embedding 演进                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   第一代: 稀疏表示                                                      │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   TF-IDF / BM25                                                 │   │
│   │   "我喜欢机器学习" → [0, 0, 0.3, 0, 0, 0.5, 0, ...]           │   │
│   │   维度: 词汇表大小 (数万维)，大部分为零                          │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   第二代: 静态词向量                                                    │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   Word2Vec / GloVe / FastText                                    │   │
│   │   "机器" → [0.12, -0.34, 0.56, ...]  (300 维)                   │   │
│   │   问题: 一词一义，无法处理多义词                                  │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   第三代: 上下文相关 Embedding ⭐                                       │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   BERT / Sentence-BERT / BGE / E5 / OpenAI Embedding           │   │
│   │   "我喜欢机器学习" → [0.023, -0.156, ..., 0.089]  (768/1536维)  │   │
│   │   整句语义编码，上下文感知，支持语义相似度计算                    │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 主流 Embedding 模型对比

| 模型 | 维度 | MTEB 排名 | 最大长度 | 特点 |
|------|------|-----------|----------|------|
| **OpenAI text-embedding-3-large** | 3072 | 前列 | 8191 | 商业最佳，支持降维 |
| **BGE-M3** | 1024 | 前列 | 8192 | 中文最佳，多语言，开源 |
| **E5-Mistral-7B** | 4096 | 顶级 | 32768 | 超长上下文，大模型级别 |
| **Cohere embed-v3** | 1024 | 前列 | 512 | 商业，支持多语言 |
| **Jina-embeddings-v3** | 1024 | 前列 | 8192 | 开源，多任务 |
| **GTE-Qwen2** | 1536 | 前列 | 32768 | 阿里开源，长文本 |

### Embedding 使用示例

```python
# OpenAI Embedding
from openai import OpenAI
client = OpenAI()

response = client.embeddings.create(
    model="text-embedding-3-large",
    input=["机器学习是人工智能的子领域"],
    dimensions=1024  # 支持降维节省存储
)
embedding = response.data[0].embedding  # [0.023, -0.156, ..., 0.089]

# 开源 BGE 模型
from sentence_transformers import SentenceTransformer

model = SentenceTransformer("BAAI/bge-m3")
texts = ["机器学习是人工智能的子领域", "深度学习使用神经网络"]
embeddings = model.encode(texts, normalize_embeddings=True)

# 计算相似度
from numpy import dot
similarity = dot(embeddings[0], embeddings[1])
print(f"相似度: {similarity:.4f}")  # 0.85+
```

---

## 向量数据库

### 核心索引算法

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       向量索引算法对比                                    │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   1. HNSW (Hierarchical Navigable Small World)                          │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   原理: 多层图结构，上层稀疏导航，下层精确搜索                    │   │
│   │   优点: 检索速度快，召回率高                                     │   │
│   │   缺点: 内存占用大（需要存储图结构）                             │   │
│   │   适用: 中小规模 (<1000万向量)，对延迟敏感                       │   │
│   │                                                                   │   │
│   │   Layer 2:  A ──── B                                             │   │
│   │             │      │                                              │   │
│   │   Layer 1:  A ── C ── B ── D                                     │   │
│   │             │    │    │    │                                      │   │
│   │   Layer 0:  A-E-C-F-B-G-D-H  (全部节点)                         │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   2. IVF (Inverted File Index)                                          │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   原理: 先聚类，查询时只搜索最近的几个聚类中心                    │   │
│   │   优点: 内存效率好，支持大规模数据                                │   │
│   │   缺点: 需要训练聚类中心，边界向量可能漏检                       │   │
│   │   适用: 大规模数据 (>1000万向量)                                 │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   3. PQ (Product Quantization)                                          │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   原理: 将高维向量切分为子空间，每个子空间独立量化                 │   │
│   │   优点: 极大压缩存储空间 (32x-64x)                               │   │
│   │   缺点: 有损压缩，精度下降                                       │   │
│   │   适用: 超大规模 (>10亿向量)，存储受限                           │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   实际使用: 通常组合使用，如 HNSW + PQ (兼顾速度和存储)                 │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 索引算法深入解析

#### 1. HNSW 深入：从 Skip List 到多层图导航

**核心思想**：HNSW 的灵感来自 **跳表（Skip List）** —— 在高层用少量"快速公路"节点做粗粒度导航，逐层下沉到底层做精确搜索。

**生活类比**：想象你在一个陌生城市找一家餐厅：
- **Layer 2（高速公路）**：先沿高速开到目标城区（只有几个大节点/出口）
- **Layer 1（主干道）**：在城区内沿主路找到目标街道
- **Layer 0（小巷）**：在街道上精确定位到那家餐厅

```
HNSW 搜索过程详解（查找与 Query 最近的节点）

Layer 2:  [A] ─────────────── [B]           ← 只有 2 个节点
           │                    │              从 A 出发，计算 dist(A,Q), dist(B,Q)
           │                    │              B 更近 → 移动到 B
           ↓                    ↓
Layer 1:  [A] ── [C] ── [B] ── [D]          ← 4 个节点
                          │                    从 B 出发，检查邻居 C, D
                          │                    C 更近 → 移动到 C
                          ↓
Layer 0:  [A]-[E]-[C]-[F]-[B]-[G]-[D]-[H]   ← 全部 8 个节点
                    │                          从 C 出发，检查邻居 E, F
                    ↓                          F 最近 → 返回 F 作为结果
               Result: F
```

**关键参数详解**：

| 参数 | 含义 | 推荐值 | 影响 |
|------|------|--------|------|
| `M` | 每个节点的最大邻居数 | 16-64 | M↑ → 召回率↑，内存↑，构建时间↑ |
| `efConstruction` | 构建时的搜索宽度 | 128-256 | 值↑ → 图质量↑，构建速度↓ |
| `ef` (搜索时) | 查询时的搜索宽度 | 64-256 | 值↑ → 召回率↑，延迟↑ |
| `max_level` | 最大层数（自动） | log(N) | N=100万时约 4-5 层 |

**复杂度分析**：

```
构建复杂度:  O(N × log(N) × M × efConstruction)
  - 100万条 768维向量，M=16, efConstruction=256
  - 构建时间 ≈ 2-5 分钟（单线程），支持多线程加速

搜索复杂度:  O(log(N) × ef × M)
  - 100万条向量，ef=128
  - 单次查询 ≈ 0.5-2ms（取决于维度和硬件）

内存占用:    O(N × M × 4 bytes)  +  O(N × dim × 4 bytes)
  - 100万条 768维向量，M=16:
    图结构: 1M × 16 × 2(双向) × 4B ≈ 128MB
    原始向量: 1M × 768 × 4B ≈ 3GB
    总计 ≈ 3.1GB
```

**M 值对性能的影响**（100 万条 768 维向量，ef=128）：

| M | 召回率@10 | 查询延迟 | 内存占用 | 构建时间 |
|---|-----------|----------|----------|----------|
| 8 | 92% | 0.3ms | 2.8GB | 1.5min |
| 16 | 97% | 0.6ms | 3.1GB | 3min |
| 32 | 99% | 1.2ms | 3.5GB | 6min |
| 64 | 99.5% | 2.5ms | 4.3GB | 12min |

> **实践建议**：大多数场景 M=16 是最佳平衡点。如果召回率要求极高（如医疗/法律），可以升到 32。

#### 2. IVF 深入：聚类 + 倒排的大规模检索

**核心思想**：先用 K-Means 将向量空间划分为 `nlist` 个聚类（Voronoi 分区），查询时只搜索最近的 `nprobe` 个分区，大幅减少计算量。

```
IVF 工作原理

Step 1: 训练阶段 —— K-Means 聚类
┌──────────────────────────────────────────────┐
│                                              │
│    C1 ●          C2 ●         C3 ●           │
│      / \           |           / \           │
│     · · ·        · · ·       · · ·          │
│    · · · ·      · · · ·     · · · ·         │
│   (分区 1)      (分区 2)     (分区 3)         │
│                                              │
│  nlist = 3 个聚类中心                          │
│  每个分区内维护一个向量列表（倒排表）            │
└──────────────────────────────────────────────┘

Step 2: 查询阶段 —— 只搜索最近的 nprobe 个分区
┌──────────────────────────────────────────────┐
│                                              │
│    C1 ●          C2 ●         C3 ●           │
│      / \           |           / \           │
│   [跳过]     Q→ [搜索!]      [搜索!]         │
│                                              │
│  nprobe = 2: 只搜索 C2, C3 两个分区            │
│  计算量减少到 2/3                              │
└──────────────────────────────────────────────┘
```

**关键参数详解**：

| 参数 | 含义 | 推荐值 | 影响 |
|------|------|--------|------|
| `nlist` | 聚类中心数量 | √N ~ 4√N | nlist↑ → 每个分区更小，搜索更快，但边界损失↑ |
| `nprobe` | 查询时搜索的分区数 | nlist × 1%~10% | nprobe↑ → 召回率↑，延迟↑ |

**nlist 与 nprobe 的搭配**（1000 万条 768 维向量）：

| nlist | nprobe | 召回率@10 | 查询延迟 | 训练时间 |
|-------|--------|-----------|----------|----------|
| 1024 | 8 | 85% | 2ms | 5min |
| 1024 | 32 | 95% | 6ms | 5min |
| 1024 | 128 | 99% | 20ms | 5min |
| 4096 | 32 | 90% | 3ms | 15min |
| 4096 | 128 | 98% | 10ms | 15min |

> **经验公式**：`nlist ≈ 4 × √N`，`nprobe ≈ nlist × 5%`。1000 万向量 → nlist≈4096, nprobe≈200。

**边界问题与缓解**：

```
边界问题: 查询点恰好在两个分区交界处

         C1 ●                    ● C2
        / | \                  / | \
       · ·|· ·              · · |· ·
      · · | · ·     Q ●   · · ·|· ·
       · ·|· ·        ↑     · ·|· ·
          |          最近邻     |
          |          实际在 C1  |
      分区 1         但 Q 离 C2 更近
                    → 如果 nprobe=1 只搜 C2，会漏掉！

解决方案:
  1. 增大 nprobe（推荐）
  2. 使用 IVF-HNSW（用 HNSW 加速聚类中心搜索）
  3. Multi-probe LSH（搜索相邻分区）
```

#### 3. PQ 深入：乘积量化的压缩魔法

**核心思想**：将高维向量切分为 `m` 个子空间，每个子空间用 K-Means 聚类得到 `k` 个码本（codebook），用码本 ID（通常 1 字节）代替原始浮点数。

**生活类比**：好比描述一个人的长相 —— 不用精确到每个像素，而是用"鹅蛋脸 + 大眼睛 + 高鼻梁 + 薄嘴唇"这样的模板组合来近似描述。每个特征只需要从有限模板中选一个编号。

```
PQ 编码过程（以 768 维向量, m=8 为例）

原始向量 (768 维, 3072 bytes):
┌──────────┬──────────┬──────────┬───┬──────────┐
│ dim 1-96 │dim 97-192│dim193-288│...│dim673-768│
│ (子空间1) │ (子空间2) │ (子空间3) │   │ (子空间8) │
└────┬─────┴────┬─────┴────┬─────┴───┴────┬─────┘
     │          │          │              │
     ↓          ↓          ↓              ↓
  K-Means    K-Means    K-Means        K-Means
  (256类)    (256类)    (256类)        (256类)
     │          │          │              │
     ↓          ↓          ↓              ↓
  码本ID=42   ID=187     ID=3          ID=95
     │          │          │              │
     ↓          ↓          ↓              ↓
编码结果 (8 bytes):
┌────┬────┬────┬────┬────┬────┬────┬────┐
│ 42 │187 │ 3  │ 71 │205 │ 18 │156 │ 95 │  ← 每个 1 byte
└────┴────┴────┴────┴────┴────┴────┴────┘

压缩比: 3072 / 8 = 384x !!!
```

**距离计算优化 —— ADC（Asymmetric Distance Computation）**：

```python
# PQ 距离计算不需要解码！
# 预计算查询向量到每个子空间所有码本中心的距离表

def pq_search(query, codebooks, encoded_db):
    """
    query: 原始查询向量 (768,)
    codebooks: m 个码本, 每个 (256, sub_dim)
    encoded_db: 编码后的数据库 (N, m), dtype=uint8
    """
    m = len(codebooks)
    sub_dim = len(query) // m
    
    # Step 1: 预计算距离表 (m × 256)
    # 查询向量的每个子空间到 256 个码本中心的距离
    dist_table = np.zeros((m, 256))
    for i in range(m):
        query_sub = query[i * sub_dim : (i + 1) * sub_dim]
        for j in range(256):
            dist_table[i][j] = np.sum((query_sub - codebooks[i][j]) ** 2)
    
    # Step 2: 查表累加（极快！只需要 m 次查表 + 累加）
    distances = np.zeros(len(encoded_db))
    for n in range(len(encoded_db)):
        for i in range(m):
            code = encoded_db[n][i]          # uint8 码本ID
            distances[n] += dist_table[i][code]  # 查表！
    
    # Step 3: 返回最近的 top-k
    return np.argsort(distances)[:10]

# 计算量对比:
# 暴力搜索: N × 768 次浮点乘加 = N × 1536 FLOPs
# PQ 查表:  N × 8 次整数查表 + 加法 ≈ N × 16 FLOPs
# 加速比 ≈ 96x（且缓存友好，实际更快）
```

**PQ 参数选择指南**：

| 参数 | 含义 | 推荐范围 | 权衡 |
|------|------|----------|------|
| `m` (子空间数) | 向量切分段数 | 8-64 | m↑ → 精度↑，编码后体积↑ |
| `nbits` (码本位数) | 每个子空间的量化位数 | 8 (256类) | 几乎固定为 8 |
| 子空间维度 | dim / m | 4-96 | 太小精度差，太大码本训练慢 |

**不同 m 值的效果**（1000 万条 768 维向量）：

| m | 编码大小 | 压缩比 | 召回率@10 | 内存占用 |
|---|----------|--------|-----------|----------|
| 8 | 8B | 384x | 60% | 80MB |
| 16 | 16B | 192x | 75% | 160MB |
| 32 | 32B | 96x | 88% | 320MB |
| 64 | 64B | 48x | 95% | 640MB |
| 原始 | 3072B | 1x | 100% | 30GB |

> **注意**：PQ 单独使用召回率不够高，生产中几乎总是与 IVF 或 HNSW 组合使用。

#### 4. 组合索引：生产级方案

单一索引往往无法同时满足速度、精度和内存的需求，实际部署中通常**组合使用**：

```
常见组合索引

┌─────────────────────────────────────────────────────────────────────┐
│                                                                     │
│  IVF + PQ (IVF-PQ)                   最常用的大规模方案             │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │  先用 IVF 缩小搜索范围 → 再用 PQ 压缩存储 + 快速距离计算     │   │
│  │  适用: 1亿+ 向量，内存有限                                    │   │
│  │  召回率: ~90% (nprobe=64, m=32)                               │   │
│  │  内存: 原始的 1/50~1/100                                      │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  HNSW + PQ (HNSW-PQ)                 高性能 + 压缩                 │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │  用 PQ 压缩向量存储 → HNSW 图上做导航 → 最终用原始向量重排   │   │
│  │  适用: 千万级向量，要求低延迟                                 │   │
│  │  召回率: ~95% (M=32, m=32, rerank top-100)                   │   │
│  │  内存: 原始的 1/30~1/50 + 图结构开销                          │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  IVF + HNSW + PQ                     极端大规模方案               │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │  IVF 分区 → HNSW 加速聚类中心搜索 → PQ 压缩分区内向量       │   │
│  │  适用: 10亿+ 向量                                             │   │
│  │  代表: Faiss 的 IVF_HNSW + PQ                                │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  IVF + SQ8 (标量量化)                轻量替代 PQ                   │
│  ┌──────────────────────────────────────────────────────────────┐   │
│  │  将每个维度从 FP32 量化为 INT8（4x 压缩）                    │   │
│  │  适用: 对精度要求高，但需要一定压缩                           │   │
│  │  召回率: ~98%（几乎无损）                                     │   │
│  │  内存: 原始的 1/4                                             │   │
│  └──────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

**如何选择索引？—— 决策流程图**：

```
                    你有多少向量？
                         │
          ┌──────────────┼──────────────┐
          │              │              │
      < 100万       100万~1亿       > 1亿
          │              │              │
      用 HNSW        内存够吗？       IVF + PQ
     (简单高效)          │           (或 IVF_HNSW+PQ)
          │         ┌────┴────┐
          │        够        不够
          │         │         │
          │      HNSW      IVF + PQ
          │    (最佳召回)  (压缩存储)
          │
      延迟要求？
     ┌────┴────┐
  < 1ms     1-10ms
     │         │
   HNSW      IVF
  M=16     nprobe 调小
  ef=64
```

**Faiss 中的索引组合代码示例**：

```python
import faiss
import numpy as np

dim = 768
N = 10_000_000  # 1000 万条向量

# 生成示例数据
data = np.random.random((N, dim)).astype('float32')
query = np.random.random((1, dim)).astype('float32')

# ============================================
# 方案 1: 纯 HNSW（适合 < 500万，追求召回率）
# ============================================
index_hnsw = faiss.IndexHNSWFlat(dim, 32)  # M=32
index_hnsw.hnsw.efConstruction = 256
index_hnsw.add(data)
index_hnsw.hnsw.efSearch = 128  # 搜索时的 ef
D, I = index_hnsw.search(query, 10)
# 内存 ≈ 30GB + 2.5GB(图) ≈ 32.5GB

# ============================================
# 方案 2: IVF + PQ（适合 > 1000万，内存受限）
# ============================================
nlist = 4096
m = 32  # PQ 子空间数
quantizer = faiss.IndexFlatL2(dim)  # 聚类中心用精确搜索
index_ivfpq = faiss.IndexIVFPQ(quantizer, dim, nlist, m, 8)
index_ivfpq.train(data[:500_000])  # 用子集训练
index_ivfpq.add(data)
index_ivfpq.nprobe = 128  # 搜索 128 个分区
D, I = index_ivfpq.search(query, 10)
# 内存 ≈ 320MB (压缩后) + 12MB (聚类中心) ≈ 332MB  🎉

# ============================================
# 方案 3: IVF + SQ8（精度优先的压缩方案）
# ============================================
index_ivfsq = faiss.IndexIVFScalarQuantizer(
    quantizer, dim, nlist, faiss.ScalarQuantizer.QT_8bit
)
index_ivfsq.train(data[:500_000])
index_ivfsq.add(data)
index_ivfsq.nprobe = 64
D, I = index_ivfsq.search(query, 10)
# 内存 ≈ 7.5GB (4x压缩) + 12MB ≈ 7.5GB

# ============================================
# 方案 4: OPQ + IVF + PQ（旋转优化 + 量化，最佳性价比）
# ============================================
index_opq = faiss.index_factory(dim, "OPQ32_128,IVF4096,PQ32")
# OPQ32_128: 先做 32 段旋转优化，投影到 128 维
# IVF4096:   4096 个聚类
# PQ32:      32 子空间量化
index_opq.train(data[:500_000])
index_opq.add(data)
faiss.ParameterSpace().set_index_parameter(index_opq, "nprobe", 128)
D, I = index_opq.search(query, 10)
# 内存 ≈ 320MB，召回率比纯 PQ 高 3-5%
```

#### 5. 综合性能对比

| 方案 | 内存 (1000万×768维) | 查询延迟 | 召回率@10 | 构建时间 | 适用规模 |
|------|---------------------|----------|-----------|----------|----------|
| Flat (暴力) | 30GB | 50ms | 100% | 0 | < 10万 |
| HNSW (M=16) | 33GB | 0.6ms | 97% | 3min | < 500万 |
| IVF (nlist=4096) | 30GB | 5ms | 95% | 15min | < 5000万 |
| IVF + PQ (m=32) | 332MB | 3ms | 88% | 20min | > 1000万 |
| IVF + SQ8 | 7.5GB | 4ms | 98% | 18min | > 1000万 |
| OPQ + IVF + PQ | 332MB | 3.5ms | 91% | 25min | > 1000万 |
| HNSW + PQ (m=32) | 2.8GB | 1.2ms | 93% | 10min | < 5000万 |

> **总结**：没有银弹，选择索引时需要在**内存**、**延迟**、**召回率**和**构建时间**之间权衡。先确定约束条件（通常是内存），再优化其他指标。

### 向量数据库选型

| 数据库 | 类型 | 规模支持 | 特点 | 适用场景 |
|--------|------|----------|------|----------|
| **Milvus** | 开源/云 | 10亿+ | 分布式，GPU加速，生产成熟 | 企业级生产环境 |
| **Pinecone** | 全托管 | 数亿 | 零运维，开箱即用 | 快速上线，不想运维 |
| **Qdrant** | 开源/云 | 数亿 | Rust 实现，高性能 | 性能敏感场景 |
| **Weaviate** | 开源/云 | 数亿 | 内置向量化，GraphQL | 快速原型开发 |
| **Chroma** | 开源 | 百万级 | 轻量，API 简洁 | 本地开发，小型项目 |
| **pgvector** | 扩展 | 千万级 | PostgreSQL 生态 | 已有 PG 基础设施 |

### Milvus 使用示例

```python
from pymilvus import connections, Collection, FieldSchema, CollectionSchema, DataType

# 连接
connections.connect("default", host="localhost", port="19530")

# 定义 Schema
fields = [
    FieldSchema(name="id", dtype=DataType.INT64, is_primary=True, auto_id=True),
    FieldSchema(name="text", dtype=DataType.VARCHAR, max_length=2000),
    FieldSchema(name="embedding", dtype=DataType.FLOAT_VECTOR, dim=1024),
    FieldSchema(name="source", dtype=DataType.VARCHAR, max_length=500),
]
schema = CollectionSchema(fields, description="knowledge_base")

# 创建 Collection
collection = Collection("knowledge_base", schema)

# 创建索引
index_params = {
    "metric_type": "COSINE",
    "index_type": "HNSW",
    "params": {"M": 16, "efConstruction": 256}
}
collection.create_index("embedding", index_params)

# 插入数据
collection.insert([texts, embeddings, sources])

# 搜索
collection.load()
results = collection.search(
    data=[query_embedding],
    anns_field="embedding",
    param={"metric_type": "COSINE", "params": {"ef": 128}},
    limit=5,
    output_fields=["text", "source"]
)
```

---

## 从零构建知识库

### 端到端 Pipeline

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    知识库构建完整 Pipeline                                │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   ┌─────────────┐   ┌─────────────┐   ┌─────────────┐                 │
│   │  数据采集    │ → │  文档解析    │ → │  文本清洗    │                 │
│   │  PDF/HTML/   │   │  PDF → Text  │   │  去噪/格式化 │                 │
│   │  Docs/API    │   │  表格/图片   │   │  编码统一    │                 │
│   └─────────────┘   └─────────────┘   └──────┬──────┘                 │
│                                               │                         │
│                                               ▼                         │
│   ┌─────────────┐   ┌─────────────┐   ┌─────────────┐                 │
│   │  索引存储    │ ← │  Embedding  │ ← │  文本分块    │                 │
│   │  向量数据库  │   │  向量化      │   │  Chunking   │                 │
│   │  + 元数据    │   │  批量处理    │   │  策略选择    │                 │
│   └──────┬──────┘   └─────────────┘   └─────────────┘                 │
│          │                                                               │
│          ▼                                                               │
│   ┌─────────────┐   ┌─────────────┐                                    │
│   │  检索服务    │ → │  质量评估    │                                    │
│   │  API 接口    │   │  召回率/精度  │                                    │
│   └─────────────┘   └─────────────┘                                    │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 分块策略（Chunking）

分块是知识库构建中最关键的步骤之一，直接影响检索质量。

| 策略 | 描述 | 优点 | 缺点 |
|------|------|------|------|
| **固定大小** | 按字符/token 数切分 | 简单，可控 | 可能切断语义 |
| **递归分块** | 按分隔符层层递归 | 保留结构 | 需要调参 |
| **语义分块** | 按语义相似度断句 | 语义完整 | 计算成本高 |
| **文档结构** | 按标题/段落 | 保留文档逻辑 | 依赖格式 |
| **滑动窗口** | 重叠切分 | 减少边界丢失 | 冗余存储 |

```python
from langchain.text_splitter import RecursiveCharacterTextSplitter

# 递归分块 (最常用)
splitter = RecursiveCharacterTextSplitter(
    chunk_size=512,
    chunk_overlap=64,
    separators=["\n\n", "\n", "。", "！", "？", "；", " "],
    length_function=len,
)

chunks = splitter.split_text(document_text)

# 语义分块
from langchain_experimental.text_splitter import SemanticChunker
from langchain_openai import OpenAIEmbeddings

semantic_splitter = SemanticChunker(
    OpenAIEmbeddings(),
    breakpoint_threshold_type="percentile",
    breakpoint_threshold_amount=95
)
semantic_chunks = semantic_splitter.split_text(document_text)
```

### 完整构建示例

```python
from langchain_community.document_loaders import (
    PyPDFLoader, UnstructuredHTMLLoader, TextLoader
)
from langchain.text_splitter import RecursiveCharacterTextSplitter
from langchain_openai import OpenAIEmbeddings
from langchain_community.vectorstores import Milvus

# 1. 数据加载
loaders = [
    PyPDFLoader("docs/manual.pdf"),
    UnstructuredHTMLLoader("docs/faq.html"),
    TextLoader("docs/guide.txt"),
]
documents = []
for loader in loaders:
    documents.extend(loader.load())

# 2. 文本分块
splitter = RecursiveCharacterTextSplitter(
    chunk_size=512, chunk_overlap=64
)
chunks = splitter.split_documents(documents)

# 3. 添加元数据
for chunk in chunks:
    chunk.metadata["indexed_at"] = datetime.now().isoformat()

# 4. 向量化 + 存储
embeddings = OpenAIEmbeddings(model="text-embedding-3-large")
vectorstore = Milvus.from_documents(
    chunks,
    embeddings,
    connection_args={"host": "localhost", "port": "19530"},
    collection_name="my_knowledge_base"
)

# 5. 检索测试
results = vectorstore.similarity_search("如何部署模型？", k=3)
for doc in results:
    print(f"[{doc.metadata['source']}] {doc.page_content[:100]}...")
```

---

## RAG 基础架构

### RAG（Retrieval-Augmented Generation）核心流程

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       RAG 核心架构                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   用户提问: "DeepSpeed ZeRO-3 的显存优化原理是什么？"                    │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ Step 1: Query Embedding                                          │   │
│   │   "DeepSpeed ZeRO-3..." → [0.12, -0.45, ..., 0.33] (1024维)    │   │
│   └───────────────────────────────┬─────────────────────────────────┘   │
│                                   │                                     │
│                                   ▼                                     │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ Step 2: Retrieval (向量相似度搜索)                               │   │
│   │                                                                   │   │
│   │   Query Vector ──搜索──▶ 知识库 (向量数据库)                      │   │
│   │                                                                   │   │
│   │   Top-K 结果:                                                     │   │
│   │   [Doc1] ZeRO-3 将优化器状态、梯度和参数全部分片... (score: 0.92) │   │
│   │   [Doc2] ZeRO 分三个阶段渐进优化内存... (score: 0.87)            │   │
│   │   [Doc3] DeepSpeed 支持 ZeRO-Offload 将数据卸载到 CPU (0.82)    │   │
│   └───────────────────────────────┬─────────────────────────────────┘   │
│                                   │                                     │
│                                   ▼                                     │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │ Step 3: Augmented Generation (增强生成)                          │   │
│   │                                                                   │   │
│   │   Prompt = System + Context(Doc1+Doc2+Doc3) + User Question     │   │
│   │                                                                   │   │
│   │   "基于以下参考资料回答问题：                                     │   │
│   │    [参考1] ZeRO-3 将优化器状态、梯度和参数全部分片...             │   │
│   │    [参考2] ZeRO 分三个阶段渐进优化内存...                         │   │
│   │    [参考3] DeepSpeed 支持 ZeRO-Offload...                        │   │
│   │                                                                   │   │
│   │    问题: DeepSpeed ZeRO-3 的显存优化原理是什么？"                 │   │
│   │                                                                   │   │
│   │   → LLM 基于检索到的上下文生成准确、有依据的回答                  │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### RAG vs Fine-tuning

| 维度 | RAG | Fine-tuning |
|------|-----|-------------|
| **知识更新** | 实时，更新知识库即可 | 需要重新训练 |
| **成本** | 低，只需维护知识库 | 高，需要 GPU 训练 |
| **幻觉控制** | 好，回答基于检索文档 | 一般，仍可能产生幻觉 |
| **定制性** | 中等 | 高，可改变模型行为 |
| **适用场景** | 知识密集型 QA | 风格/格式定制 |
| **延迟** | 增加检索延迟 | 无额外延迟 |
| **可解释性** | 高，可追溯来源 | 低，黑盒 |

### LangChain RAG 实现

```python
from langchain_openai import ChatOpenAI, OpenAIEmbeddings
from langchain_community.vectorstores import Milvus
from langchain.chains import RetrievalQA
from langchain.prompts import PromptTemplate

# 初始化组件
llm = ChatOpenAI(model="gpt-4o", temperature=0)
embeddings = OpenAIEmbeddings(model="text-embedding-3-large")

# 连接知识库
vectorstore = Milvus(
    embedding_function=embeddings,
    connection_args={"host": "localhost", "port": "19530"},
    collection_name="ai_infra_docs"
)

# 自定义 Prompt
prompt_template = """基于以下参考资料回答问题。如果资料中没有相关信息，请明确说明"根据现有资料无法回答"。

参考资料：
{context}

问题：{question}

请提供准确、详细的回答，并标注信息来源。"""

prompt = PromptTemplate(
    template=prompt_template,
    input_variables=["context", "question"]
)

# 构建 RAG Chain
qa_chain = RetrievalQA.from_chain_type(
    llm=llm,
    chain_type="stuff",
    retriever=vectorstore.as_retriever(search_kwargs={"k": 5}),
    chain_type_kwargs={"prompt": prompt},
    return_source_documents=True
)

# 查询
result = qa_chain.invoke({"query": "ZeRO-3 如何优化显存？"})
print(result["result"])
for doc in result["source_documents"]:
    print(f"  来源: {doc.metadata['source']}")
```

---

## 高级 RAG 技术

### 高级 RAG 技术全景

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    高级 RAG 技术全景                                      │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   Pre-Retrieval (检索前优化)                                            │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   • Query Rewriting: 改写用户查询提高召回                       │   │
│   │   • HyDE: 生成假设文档用于检索                                   │   │
│   │   • Query Decomposition: 复杂问题拆解为子问题                   │   │
│   │   • Query Routing: 根据问题类型选择检索策略                     │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Retrieval (检索优化)                                                  │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   • Hybrid Search: 向量 + 关键词混合搜索                         │   │
│   │   • Multi-hop Retrieval: 多步检索，链式推理                     │   │
│   │   • Parent-Child Retrieval: 检索子块，返回父块                  │   │
│   │   • Graph RAG: 基于知识图谱的结构化检索                         │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   Post-Retrieval (检索后优化)                                           │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   • Re-ranking: 重排序，提升相关性排名                           │   │
│   │   • Contextual Compression: 压缩上下文，减少噪声                │   │
│   │   • Self-RAG: 模型自判断是否需要检索                             │   │
│   │   • Corrective RAG: 检索质量不够时自动修正                      │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### HyDE（Hypothetical Document Embedding）

```python
from langchain_openai import ChatOpenAI, OpenAIEmbeddings
from langchain.prompts import PromptTemplate

llm = ChatOpenAI(model="gpt-4o")

# 1. 用 LLM 生成假设文档
hyde_prompt = PromptTemplate(
    template="请写一段文档来回答以下问题：\n{question}\n\n文档内容：",
    input_variables=["question"]
)

question = "HNSW 索引的时间复杂度是多少？"
hypothetical_doc = llm.invoke(hyde_prompt.format(question=question))

# 2. 用假设文档的 embedding 检索（比原始问题更精准）
embeddings = OpenAIEmbeddings()
hyde_embedding = embeddings.embed_query(hypothetical_doc.content)
results = vectorstore.similarity_search_by_vector(hyde_embedding, k=5)
```

### Re-ranking

```python
# 使用 Cross-Encoder 重排序
from sentence_transformers import CrossEncoder

reranker = CrossEncoder("BAAI/bge-reranker-v2-m3")

# 初始检索 (召回 20 条)
candidates = vectorstore.similarity_search(query, k=20)

# Re-ranking (精排为 Top-5)
pairs = [(query, doc.page_content) for doc in candidates]
scores = reranker.predict(pairs)

reranked = sorted(zip(candidates, scores), key=lambda x: x[1], reverse=True)
top_5 = [doc for doc, score in reranked[:5]]
```

---

## 消除幻觉与质量提升

### 幻觉分类

```
┌─────────────────────────────────────────────────────────────────────────┐
│                       LLM 幻觉分类与成因                                 │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   1. 事实性幻觉 (Factual Hallucination)                                 │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   模型编造不存在的事实                                           │   │
│   │   例: "GPT-4 是 2025 年 1 月发布的" (错误日期)                   │   │
│   │   例: "Milvus 是 Facebook 开发的" (错误归属)                     │   │
│   │                                                                   │   │
│   │   成因:                                                          │   │
│   │   • 训练数据中的错误信息                                         │   │
│   │   • 模型对低频知识的泛化错误                                     │   │
│   │   • 知识截止日期后的信息缺失                                     │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   2. 忠实性幻觉 (Faithfulness Hallucination)                            │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   模型的回答与提供的上下文不一致                                  │   │
│   │   例: 上下文说"A100 有 80GB 显存"，模型回答"A100 有 40GB 显存"   │   │
│   │                                                                   │   │
│   │   成因:                                                          │   │
│   │   • 上下文过长，模型注意力分散                                   │   │
│   │   • 模型参数知识与上下文冲突                                     │   │
│   │   • Prompt 设计不当                                              │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   3. 指令幻觉 (Instruction Hallucination)                               │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   模型不遵循指令格式或约束                                       │   │
│   │   例: 要求输出 JSON，结果输出了 Markdown                          │   │
│   │   例: 要求"只基于上下文回答"，结果引入了外部知识                   │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### 知识库消除幻觉的核心策略

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    知识库消除幻觉五大策略                                  │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   策略1: Grounding (事实锚定)                                           │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   强制模型基于检索文档回答，而非依赖参数知识                     │   │
│   │   Prompt: "仅根据以下文档内容回答。如果文档中没有，回答'未知'"   │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   策略2: 引用溯源 (Citation)                                            │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   要求模型标注每个论断的来源文档                                  │   │
│   │   Prompt: "回答时用 [1][2] 标注引用来源"                         │   │
│   │   效果: 用户可验证，模型更谨慎                                   │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   策略3: 置信度评估 (Confidence Assessment)                              │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   检索结果质量不够时，主动拒答                                   │   │
│   │   • 检索相似度分数 < 阈值 → "信息不足，无法回答"                 │   │
│   │   • 多个文档内容矛盾 → "信息存在冲突，请人工确认"               │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   策略4: 事实验证 (Fact Verification)                                    │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   生成后用另一个模型/检索验证答案的事实性                        │   │
│   │   Pipeline: 生成 → 提取声明 → 逐条检索验证 → 修正/拒绝          │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   策略5: Guardrails (护栏)                                               │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   设置输出约束和安全检查                                         │   │
│   │   • 检查输出是否包含知识库中不存在的实体                         │   │
│   │   • 检查数值是否在合理范围内                                     │   │
│   │   • 使用 NLI 模型验证输出与上下文的一致性                        │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### RAGAS 评估框架

```python
from ragas import evaluate
from ragas.metrics import (
    faithfulness,         # 忠实性: 答案是否基于上下文
    answer_relevancy,     # 相关性: 答案是否切题
    context_precision,    # 精度: 检索结果是否相关
    context_recall        # 召回: 是否检索到了必要信息
)
from datasets import Dataset

eval_data = Dataset.from_dict({
    "question": ["ZeRO-3 如何优化显存？"],
    "answer": ["ZeRO-3 将优化器状态、梯度和模型参数全部在数据并行维度分片..."],
    "contexts": [["ZeRO-3 对优化器状态(O)、梯度(G)和参数(P)进行分片..."]],
    "ground_truth": ["ZeRO Stage 3 将优化器状态、梯度和模型参数分片到所有 GPU..."]
})

result = evaluate(eval_data, metrics=[
    faithfulness, answer_relevancy, context_precision, context_recall
])
print(result)
# {'faithfulness': 0.95, 'answer_relevancy': 0.91,
#  'context_precision': 0.88, 'context_recall': 0.90}
```

---

## 实时知识获取

### 实时数据场景

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    实时知识获取架构                                       │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   场景: "特斯拉 (TSLA) 今天股价多少？"                                  │
│                                                                         │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │                     LLM Agent                                    │   │
│   │                                                                   │   │
│   │   1. 意图识别: 需要实时数据 → 走 Tool/Function Calling            │   │
│   │   2. 选择工具: get_stock_price(symbol="TSLA")                    │   │
│   │   3. 调用 API: → 金融数据 API → 返回实时价格                      │   │
│   │   4. 整合回答: "特斯拉当前股价为 $248.50，涨幅 2.3%"             │   │
│   │                                                                   │   │
│   └───────────────────────────────┬─────────────────────────────────┘   │
│                                   │                                     │
│              ┌────────────────────┼────────────────────┐               │
│              │                    │                    │               │
│              ▼                    ▼                    ▼               │
│   ┌──────────────┐    ┌──────────────┐    ┌──────────────┐           │
│   │  离线知识库   │    │  实时 API    │    │  流式数据     │           │
│   │  (向量数据库) │    │  (Tool Use)  │    │  (CDC/Stream) │           │
│   │              │    │              │    │              │           │
│   │  • 文档      │    │  • 股票 API  │    │  • Kafka     │           │
│   │  • FAQ       │    │  • 天气 API  │    │  • 数据库CDC │           │
│   │  • 知识图谱  │    │  • 搜索 API  │    │  • 日志流    │           │
│   └──────────────┘    └──────────────┘    └──────────────┘           │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Function Calling + 知识库联合

```python
from openai import OpenAI
import json

client = OpenAI()

# 定义工具
tools = [
    {
        "type": "function",
        "function": {
            "name": "search_knowledge_base",
            "description": "搜索内部知识库获取公司文档、技术资料等离线知识",
            "parameters": {
                "type": "object",
                "properties": {
                    "query": {"type": "string", "description": "搜索查询"}
                },
                "required": ["query"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "get_stock_price",
            "description": "获取股票实时价格",
            "parameters": {
                "type": "object",
                "properties": {
                    "symbol": {"type": "string", "description": "股票代码，如 TSLA"}
                },
                "required": ["symbol"]
            }
        }
    },
    {
        "type": "function",
        "function": {
            "name": "web_search",
            "description": "搜索互联网获取最新信息",
            "parameters": {
                "type": "object",
                "properties": {
                    "query": {"type": "string", "description": "搜索关键词"}
                },
                "required": ["query"]
            }
        }
    }
]

# LLM 自动选择使用哪个工具
response = client.chat.completions.create(
    model="gpt-4o",
    messages=[{"role": "user", "content": "特斯拉今天股价多少？最近有什么重大新闻？"}],
    tools=tools,
    tool_choice="auto"
)

# 处理工具调用
for tool_call in response.choices[0].message.tool_calls:
    name = tool_call.function.name
    args = json.loads(tool_call.function.arguments)
    
    if name == "get_stock_price":
        result = fetch_stock_price(args["symbol"])  # 调用实际 API
    elif name == "web_search":
        result = search_web(args["query"])
    elif name == "search_knowledge_base":
        result = search_kb(args["query"])
```

### 时效性数据管理

| 数据类型 | 更新频率 | 接入方式 | 示例 |
|----------|----------|----------|------|
| **实时数据** | 秒级 | Function Calling / API | 股票价格、天气 |
| **近实时** | 分钟-小时级 | CDC / 流式更新 | 新闻、社交媒体 |
| **定期更新** | 天-周级 | 批量索引更新 | 产品目录、法规 |
| **静态知识** | 月-年级 | 初始索引 | 教材、百科 |

---

## Token 节省策略

### 知识库如何节省 Token

```
┌─────────────────────────────────────────────────────────────────────────┐
│                    知识库 Token 节省策略                                   │
├─────────────────────────────────────────────────────────────────────────┤
│                                                                         │
│   传统方式 (无知识库):                                                   │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   System Prompt: 2000 tokens (包含所有背景知识)                   │   │
│   │   Few-shot 示例: 1500 tokens                                     │   │
│   │   用户问题: 100 tokens                                           │   │
│   │   ─────────────────────────                                      │   │
│   │   总计: ~3600 tokens / 每次请求                                   │   │
│   │                                                                   │   │
│   │   问题: 大量 token 浪费在"以防万一"的知识上                       │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
│   知识库方式 (RAG):                                                      │
│   ┌─────────────────────────────────────────────────────────────────┐   │
│   │   System Prompt: 200 tokens (精简指令)                            │   │
│   │   检索上下文: 500 tokens (只检索相关内容)                         │   │
│   │   用户问题: 100 tokens                                           │   │
│   │   ─────────────────────────                                      │   │
│   │   总计: ~800 tokens / 每次请求                                    │   │
│   │                                                                   │   │
│   │   节省: 78% Token 用量                                            │   │
│   └─────────────────────────────────────────────────────────────────┘   │
│                                                                         │
└─────────────────────────────────────────────────────────────────────────┘
```

### Semantic Caching（语义缓存）

```python
from langchain.cache import RedisSemanticCache
from langchain.globals import set_llm_cache
from langchain_openai import OpenAIEmbeddings

# 设置语义缓存
set_llm_cache(RedisSemanticCache(
    redis_url="redis://localhost:6379",
    embedding=OpenAIEmbeddings(),
    score_threshold=0.95  # 相似度 > 95% 直接返回缓存
))

# 第一次查询: 调用 LLM（~500ms, ~1000 tokens）
result1 = llm.invoke("什么是 RAG？")

# 第二次查询（语义相似）: 命中缓存（~5ms, 0 tokens）
result2 = llm.invoke("RAG 是什么意思？")  # 语义相似，命中缓存
```

### Prompt Compression（上下文压缩）

```python
# 使用 LLMLingua 压缩上下文
from llmlingua import PromptCompressor

compressor = PromptCompressor(
    model_name="microsoft/llmlingua-2-bert-base-multilingual-cased-meetingbank",
    device_map="cpu"
)

# 原始上下文 (2000 tokens)
original_context = """
ZeRO-3 是 DeepSpeed 框架中最激进的内存优化策略。它将优化器状态、
梯度和模型参数全部在数据并行维度上进行分片。每个 GPU 只保存
模型参数的 1/N（N 为 GPU 数量）。在前向传播时，需要通过 
AllGather 操作收集完整参数；反向传播完成后，参数再次释放...
[更多详细内容...]
"""

# 压缩后 (~600 tokens, 保留关键信息)
compressed = compressor.compress_prompt(
    original_context,
    rate=0.3,  # 压缩到 30%
    force_tokens=["ZeRO-3", "DeepSpeed", "分片", "AllGather"]
)

print(f"原始: {compressed['origin_tokens']} tokens")
print(f"压缩后: {compressed['compressed_tokens']} tokens")
print(f"节省: {compressed['saving']}%")
```

### 模型路由（按复杂度选模型）

```python
class ModelRouter:
    """根据问题复杂度选择模型，节省 Token 成本"""
    
    def __init__(self):
        self.models = {
            "simple": {"name": "gpt-4o-mini", "cost_per_1k": 0.00015},
            "medium": {"name": "gpt-4o", "cost_per_1k": 0.005},
            "complex": {"name": "gpt-4o", "cost_per_1k": 0.005},
        }
    
    def classify_complexity(self, query: str, retrieved_docs: list) -> str:
        """判断问题复杂度"""
        # 简单: 知识库中有直接答案，检索分数高
        if retrieved_docs and retrieved_docs[0].score > 0.95:
            return "simple"
        # 复杂: 需要多文档推理，或检索分数低
        if len(retrieved_docs) < 2 or retrieved_docs[0].score < 0.7:
            return "complex"
        return "medium"
    
    def route(self, query: str, retrieved_docs: list) -> str:
        complexity = self.classify_complexity(query, retrieved_docs)
        model = self.models[complexity]
        return model["name"]

router = ModelRouter()
model_name = router.route(query, retrieved_docs)
# 简单问题用 gpt-4o-mini (成本降低 97%)
# 复杂问题用 gpt-4o (保证质量)
```

### Token 节省策略汇总

| 策略 | 节省比例 | 实现复杂度 | 适用场景 |
|------|----------|-----------|----------|
| **RAG 替代长 Prompt** | 50-80% | 中 | 知识密集型应用 |
| **语义缓存** | 30-70% | 低 | 高频重复查询 |
| **Prompt 压缩** | 40-70% | 中 | 长文档上下文 |
| **模型路由** | 60-90% | 中 | 混合复杂度场景 |
| **混合检索精排** | 20-40% | 高 | 大规模知识库 |
| **增量对话摘要** | 30-50% | 中 | 多轮对话 |

---

## 实战练习

### 练习 1：构建简易知识库

```python
# simple_kb.py - 从零构建一个本地知识库
from langchain_community.document_loaders import DirectoryLoader, TextLoader
from langchain.text_splitter import RecursiveCharacterTextSplitter
from langchain_community.vectorstores import Chroma
from langchain_openai import OpenAIEmbeddings, ChatOpenAI
from langchain.chains import RetrievalQA

# 1. 加载文档
loader = DirectoryLoader("./docs", glob="**/*.md", loader_cls=TextLoader)
docs = loader.load()
print(f"加载了 {len(docs)} 个文档")

# 2. 分块
splitter = RecursiveCharacterTextSplitter(chunk_size=500, chunk_overlap=50)
chunks = splitter.split_documents(docs)
print(f"切分为 {len(chunks)} 个块")

# 3. 创建向量知识库
vectorstore = Chroma.from_documents(
    chunks,
    OpenAIEmbeddings(),
    persist_directory="./chroma_db"
)

# 4. RAG 问答
qa = RetrievalQA.from_chain_type(
    llm=ChatOpenAI(model="gpt-4o-mini"),
    retriever=vectorstore.as_retriever(search_kwargs={"k": 3})
)

# 5. 测试
answer = qa.invoke({"query": "如何配置分布式训练？"})
print(answer["result"])
```

### 练习 2：实现 Re-ranking Pipeline

```python
# reranking_pipeline.py
from sentence_transformers import CrossEncoder
from langchain_community.vectorstores import Chroma
from langchain_openai import OpenAIEmbeddings

# 初始化
embeddings = OpenAIEmbeddings()
vectorstore = Chroma(persist_directory="./chroma_db", embedding_function=embeddings)
reranker = CrossEncoder("BAAI/bge-reranker-v2-m3")

def rag_with_reranking(query: str, initial_k: int = 20, final_k: int = 5):
    # Stage 1: 粗召回
    candidates = vectorstore.similarity_search(query, k=initial_k)
    
    # Stage 2: 精排
    pairs = [(query, doc.page_content) for doc in candidates]
    scores = reranker.predict(pairs)
    
    # 按分数排序
    ranked = sorted(zip(candidates, scores), key=lambda x: x[1], reverse=True)
    top_docs = [doc for doc, _ in ranked[:final_k]]
    
    return top_docs

results = rag_with_reranking("HNSW 和 IVF 哪个更快？")
for doc in results:
    print(f"  {doc.page_content[:100]}...")
```

### 练习 3：实现语义缓存

```python
# semantic_cache.py
import numpy as np
from langchain_openai import OpenAIEmbeddings

class SemanticCache:
    def __init__(self, threshold=0.95):
        self.cache = {}  # {query_text: (embedding, response)}
        self.embeddings = OpenAIEmbeddings()
        self.threshold = threshold
    
    def get(self, query: str):
        query_emb = self.embeddings.embed_query(query)
        
        for cached_query, (cached_emb, response) in self.cache.items():
            similarity = np.dot(query_emb, cached_emb)
            if similarity >= self.threshold:
                print(f"Cache HIT (similarity={similarity:.3f})")
                return response
        
        return None
    
    def set(self, query: str, response: str):
        embedding = self.embeddings.embed_query(query)
        self.cache[query] = (embedding, response)

# 使用
cache = SemanticCache(threshold=0.95)
cache.set("什么是 RAG？", "RAG 是检索增强生成技术...")

# 语义相似查询命中缓存
result = cache.get("RAG 是什么意思？")  # Cache HIT
```

---

## 参考资料与引用

### 推荐论文

1. Lewis, P., et al. (2020). *Retrieval-Augmented Generation for Knowledge-Intensive NLP Tasks*. NeurIPS 2020. arXiv:2005.11401. https://arxiv.org/abs/2005.11401
2. Asai, A., et al. (2023). *Self-RAG: Learning to Retrieve, Generate, and Critique through Self-Reflection*. arXiv:2310.11511. https://arxiv.org/abs/2310.11511
3. Yan, S., et al. (2024). *Corrective Retrieval Augmented Generation*. arXiv:2401.15884. https://arxiv.org/abs/2401.15884
4. Sarthi, P., et al. (2024). *RAPTOR: Recursive Abstractive Processing for Tree-Organized Retrieval*. arXiv:2401.18059. https://arxiv.org/abs/2401.18059
5. Edge, D., et al. (2024). *From Local to Global: A Graph RAG Approach to Query-Focused Summarization*. arXiv:2404.16130. https://arxiv.org/abs/2404.16130

### 推荐资源

- [LangChain Documentation](https://python.langchain.com/docs/). LangChain.
- [LlamaIndex Documentation](https://docs.llamaindex.ai/). LlamaIndex.
- [Milvus Vector Database Documentation](https://milvus.io/docs). Zilliz.
- [RAGAS Evaluation Framework](https://docs.ragas.io/).
- [Awesome RAG - Curated List](https://github.com/frutik/Awesome-RAG).

### 推荐课程

- [LangChain & LlamaIndex RAG Courses](https://www.deeplearning.ai/short-courses/). DeepLearning.AI.
- [Building RAG Agents with LLMs](https://learn.nvidia.com/). NVIDIA DLI.

---

*下一篇：无（本章为最后一章）*

*上一篇：[06-learning-roadmap.md](06-learning-roadmap.md) - 学习路线图*
