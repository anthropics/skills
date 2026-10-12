# Milvus 深度解析

> 从核心概念到生产实战，以一个"企业技术文档智能问答系统"案例贯穿全篇，带你深入理解 Milvus 的设计哲学与最佳实践。

**前置阅读**：[04-向量数据库](04-vector-databases.md)（索引算法原理、基础 CRUD、选型对比）

---

## 目录

- [贯穿案例介绍](#贯穿案例介绍)
- [核心概念体系](#核心概念体系)
- [存储计算分离架构](#存储计算分离架构)
- [部署模式](#部署模式)
- [案例实战 Part 1：Schema 设计与数据导入](#案例实战-part-1schema-设计与数据导入)
- [索引策略深度配置](#索引策略深度配置)
- [多租户方案](#多租户方案)
- [一致性级别](#一致性级别)
- [案例实战 Part 2：搜索优化与混合检索](#案例实战-part-2搜索优化与混合检索)
- [运维监控](#运维监控)
- [性能调优](#性能调优)
- [常见踩坑与注意事项](#常见踩坑与注意事项)
- [案例实战 Part 3：生产部署与完整代码](#案例实战-part-3生产部署与完整代码)
- [总结](#总结)

---

## 贯穿案例介绍

本文以一个**企业内部技术文档智能问答系统**作为贯穿案例。每讲完一个技术点，立即用案例代码演示。

### 业务场景

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    企业技术文档智能问答系统                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   痛点:                                                                    │
│   • 技术文档散落在 Confluence、Git Wiki、飞书文档等多个平台                  │
│   • 新人找文档靠"问老同事"，效率极低                                        │
│   • 搜索只支持关键词，无法理解语义（搜"怎么发布服务"找不到"部署指南"）        │
│                                                                             │
│   目标:                                                                    │
│   • 将所有技术文档导入 Milvus，支持语义搜索                                 │
│   • 按部门隔离数据（多租户），各团队只看到自己的文档                         │
│   • 支持混合搜索（语义 + 关键词 + 标量过滤）                                │
│   • 对接 LLM 做 RAG 问答                                                   │
│                                                                             │
│   规模:                                                                    │
│   • 50 万篇文档，平均每篇 3 个分块 → 约 150 万向量                         │
│   • 10 个部门，50+ 并发用户                                                │
│   • 搜索延迟 < 100ms，可用性 > 99.9%                                       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 技术选型

| 组件 | 选型 | 理由 |
|------|------|------|
| 向量数据库 | Milvus 2.4+ (Distributed) | 150 万向量 + 多租户 + 高可用 |
| Embedding | BGE-M3 (1024 维) | 支持中英文 + 稀疏向量 + ColBERT |
| LLM | GPT-4o-mini / 通义千问 | RAG 问答生成 |
| 编排框架 | LangChain | 快速构建 RAG Pipeline |

---

## 核心概念体系

### 概念层次图

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                        Milvus 核心概念层次                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Database (数据库)                                                         │
│   └── Collection (集合) ← 类似 MySQL 的 "表"                               │
│       ├── Schema (模式)                                                    │
│       │   ├── Primary Key Field (主键字段)                                 │
│       │   ├── Vector Field (向量字段，可多个)                               │
│       │   ├── Scalar Field (标量字段: VARCHAR/INT/BOOL/JSON...)            │
│       │   └── Dynamic Field (动态字段，无需预定义)                          │
│       ├── Partition (分区) ← 物理数据隔离                                  │
│       │   └── Segment (段) ← 数据存储最小单元                              │
│       │       ├── Growing Segment (正在写入的段)                           │
│       │       └── Sealed Segment (已密封的段，不可修改)                     │
│       └── Index (索引) ← 加速搜索                                         │
│           ├── Vector Index (HNSW / IVF_FLAT / IVF_PQ / ...)               │
│           └── Scalar Index (倒排索引 / Bitmap / ...)                       │
│                                                                             │
│   Channel (通道) ← 数据写入的逻辑管道                                      │
│   ├── DML Channel (Insert/Delete 操作)                                     │
│   └── Delta Channel (删除日志)                                             │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 核心概念详解

#### Collection：数据的逻辑容器

Collection 是 Milvus 中最核心的概念，等价于关系型数据库中的"表"。每个 Collection 有严格的 Schema 定义。

```
Collection 与 MySQL Table 的对比

┌──────────────────┬───────────────────────────────────────────────┐
│     MySQL Table   │          Milvus Collection                    │
├──────────────────┼───────────────────────────────────────────────┤
│  Schema (DDL)    │  Schema (FieldSchema + CollectionSchema)      │
│  Row             │  Entity                                       │
│  Column          │  Field                                        │
│  Primary Key     │  Primary Key (INT64 / VARCHAR)                │
│  Index (B+Tree)  │  Vector Index (HNSW/IVF) + Scalar Index      │
│  Partition       │  Partition / Partition Key                     │
│  Database        │  Database                                     │
│  —               │  Dynamic Field (Schema-free JSON)             │
│  —               │  Multiple Vector Fields (多向量列)             │
└──────────────────┴───────────────────────────────────────────────┘
```

**关键限制**（Milvus 2.4）：

| 限制项 | 值 | 说明 |
|--------|-----|------|
| 单 Collection 最大字段数 | 64 | 含主键和向量字段 |
| 向量维度上限 | 32,768 | 通常 768-1536 |
| VARCHAR 最大长度 | 65,535 bytes | UTF-8 编码 |
| Collection 名长度 | 255 字符 | 字母开头，字母/数字/下划线 |
| 单次插入推荐行数 | 10,000-50,000 | 过大可能超时 |
| Partition 数量上限 | 1,024 | 每个 Collection |

#### Partition：物理数据分区

Partition 将 Collection 中的数据物理隔离，搜索时可指定分区以缩小搜索范围。

```
Collection: tech_docs
┌─────────────────────────────────────────────────────────────────┐
│                                                                 │
│   Partition: "infra"          Partition: "backend"              │
│   ┌───────────────────┐      ┌───────────────────┐             │
│   │ K8s 部署指南       │      │ Java 开发规范      │             │
│   │ 监控配置文档       │      │ API 设计指南       │             │
│   │ CI/CD Pipeline    │      │ 微服务架构文档      │             │
│   │ ...共 20 万条     │      │ ...共 30 万条     │             │
│   └───────────────────┘      └───────────────────┘             │
│                                                                 │
│   搜索时: collection.search(partition_names=["infra"])          │
│   → 只搜索 infra 分区的 20 万条，速度提升 ~7x                   │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

#### Segment：存储最小单元

Segment 是 Milvus 实际存储和索引数据的最小物理单元。理解 Segment 对性能调优至关重要。

```
Segment 生命周期

         Insert 数据
              │
              ▼
    ┌──────────────────┐
    │  Growing Segment  │  ← 内存中，接收写入
    │  (可变，未密封)    │     大小持续增长
    └────────┬─────────┘
             │  触发条件:
             │  1. 达到 segment 大小阈值 (默认 512MB)
             │  2. 手动调用 flush()
             ▼
    ┌──────────────────┐
    │  Sealed Segment   │  ← 不可变，等待构建索引
    │  (密封，只读)      │     数据写入对象存储 (S3/MinIO)
    └────────┬─────────┘
             │  IndexNode 异步构建索引
             ▼
    ┌──────────────────┐
    │  Indexed Segment  │  ← 索引已构建，加载到 QueryNode 可搜索
    └──────────────────┘

    ⚠️ Growing Segment 搜索是暴力扫描，性能极差！
    → 生产中务必确保数据 flush + 索引构建完成后再搜索。
```

#### Channel：写入的逻辑管道

```
    Client Insert
         │
         ▼
    ┌─────────┐  按主键 Hash 分配到不同 Channel
    │  Proxy   │
    └────┬────┘
    ┌────┼────┐
    ▼    ▼    ▼
  DML  DML  DML    ← DML Channel (基于 Pulsar/Kafka)
  Ch0  Ch1  Ch2
    │    │    │
    ▼    ▼    ▼
  Data Data Data    ← DataNode 消费并写入 Segment
  N0   N1   N2

  Channel 数 = Shard 数 (默认 1，创建 Collection 时指定)
```

---

## 存储计算分离架构

Milvus 2.x 采用**存储计算分离**的云原生架构，这是它区别于 Qdrant、Chroma 等单机向量数据库的核心设计。

### 四层架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Milvus 存储计算分离架构                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌───────────────────────────────────────────────────────────────────────┐  │
│  │                    Access Layer (接入层)                               │  │
│  │   ┌───────────┐  ┌───────────┐  ┌───────────┐                       │  │
│  │   │  Proxy 0  │  │  Proxy 1  │  │  Proxy 2  │  ← 无状态，水平扩展  │  │
│  │   └─────┬─────┘  └─────┬─────┘  └─────┬─────┘    负载均衡 + 鉴权    │  │
│  └─────────┼──────────────┼──────────────┼───────────────────────────────┘  │
│            └──────────────┼──────────────┘                                  │
│  ┌────────────────────────┼──────────────────────────────────────────────┐  │
│  │              Coordinator Layer (协调层)                                │  │
│  │   ┌──────────────┐  ┌─┴────────────┐  ┌──────────────┐              │  │
│  │   │  RootCoord   │  │  QueryCoord  │  │  DataCoord   │              │  │
│  │   │  元数据/DDL   │  │  查询调度     │  │  数据调度     │              │  │
│  │   │  时间戳分配   │  │  Segment分配  │  │  Compaction  │              │  │
│  │   └──────────────┘  └──────────────┘  └──────────────┘              │  │
│  │   每种 Coord 只有 1 个 Active (HA 通过 etcd 选主)                    │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │              Worker Layer (工作层)                                     │  │
│  │   ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │  │
│  │   │  QueryNode   │  │  DataNode    │  │  IndexNode   │              │  │
│  │   │  执行ANN搜索  │  │  消费Channel │  │  异步构建索引 │              │  │
│  │   │  加载Segment  │  │  写入存储     │  │  写回存储     │              │  │
│  │   └──────────────┘  └──────────────┘  └──────────────┘              │  │
│  │   无状态，水平扩展。QueryNode 是搜索的核心                           │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
│                                                                             │
│  ┌──────────────────────────────────────────────────────────────────────┐  │
│  │              Storage Layer (存储层)                                    │  │
│  │   ┌──────────────┐  ┌──────────────┐  ┌──────────────┐              │  │
│  │   │    etcd       │  │  MinIO / S3  │  │ Pulsar/Kafka │              │  │
│  │   │  元数据       │  │  数据+索引    │  │  WAL日志     │              │  │
│  │   └──────────────┘  └──────────────┘  └──────────────┘              │  │
│  │   持久化存储，独立扩展。数据永不丢失。                               │  │
│  └──────────────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 数据写入链路

```
Client Insert → Proxy (校验+分配时间戳+写MQ) → DataNode (攒批写Growing Segment)
  → 达阈值 flush → Sealed Segment (MinIO/S3) → IndexNode 构建索引
  → QueryNode 加载 Segment+索引 → 可搜索
```

### 搜索查询链路

```
Client Search → Proxy (解析请求) → Fan-out 到多个 QueryNode
  → 各 QueryNode 搜索本地 Segment，返回 Top-K
  → Proxy Merge 合并 → 全局 Top-K → 返回 Client
```

### 存储计算分离的核心优势

| 传统架构 | Milvus 存储计算分离 |
|----------|---------------------|
| 搜索和存储绑定 | QueryNode 和存储独立扩展 |
| 节点宕机 → 数据丢失 | 数据在 S3/MinIO，节点宕机不丢数据 |
| 扩容要数据迁移 | 新增 QueryNode 只需加载 Segment，秒级扩容 |
| 内存 = 存储上限 | 内存只放热数据，冷数据存 S3 |
| 索引构建占搜索资源 | IndexNode 独立，不影响搜索 |

---

## 部署模式

### 四种模式对比

| | Milvus Lite | Standalone | Distributed | Zilliz Cloud |
|---|---|---|---|---|
| 运行方式 | pip 包 | Docker 单机 | K8s 集群 | 云服务 |
| 向量规模 | < 100万 | < 1000万 | 10亿+ | 10亿+ |
| 高可用 | ✗ | ✗ | ✓ | ✓ |
| 水平扩展 | ✗ | ✗ | ✓ | ✓ (自动) |
| 适用场景 | 原型/Notebook | 开发测试 | 生产环境 | 免运维生产 |

```python
# Milvus Lite: pip install pymilvus 即可
from pymilvus import MilvusClient
client = MilvusClient("./milvus_demo.db")  # 本地文件存储

# Standalone: Docker
# docker compose up -d (使用官方 docker-compose.yml)

# Distributed: K8s + Helm
# helm install milvus milvus/milvus --set cluster.enabled=true
```

### 选择决策树

```
         向量数量？
    ┌────────┼────────┐
  < 10万   10万~1000万  > 1000万
    │        │          │
 Milvus    Standalone  有 K8s？
  Lite     (Docker)    ┌──┴──┐
                      有    无
                       │     │
                   Distributed  Zilliz Cloud
```

---

## 案例实战 Part 1：Schema 设计与数据导入

### Schema 设计

```python
from pymilvus import MilvusClient, CollectionSchema, FieldSchema, DataType

fields = [
    # 主键: VARCHAR 类型，存储文档分块 ID
    FieldSchema(name="chunk_id", dtype=DataType.VARCHAR,
                is_primary=True, max_length=128),
    # 标题向量 (BGE-M3, 1024 维)
    FieldSchema(name="title_vec", dtype=DataType.FLOAT_VECTOR, dim=1024),
    # 内容向量
    FieldSchema(name="content_vec", dtype=DataType.FLOAT_VECTOR, dim=1024),
    # 稀疏向量 (BM25, 用于混合搜索)
    FieldSchema(name="sparse_vec", dtype=DataType.SPARSE_FLOAT_VECTOR),
    # 部门 — Partition Key，自动按部门分区
    FieldSchema(name="department", dtype=DataType.VARCHAR,
                max_length=64, is_partition_key=True),
    # 标量字段
    FieldSchema(name="title", dtype=DataType.VARCHAR, max_length=512),
    FieldSchema(name="content", dtype=DataType.VARCHAR, max_length=8192),
    FieldSchema(name="author", dtype=DataType.VARCHAR, max_length=128),
    FieldSchema(name="source", dtype=DataType.VARCHAR, max_length=256),
    FieldSchema(name="created_at", dtype=DataType.INT64),
    FieldSchema(name="tags", dtype=DataType.ARRAY,
                element_type=DataType.VARCHAR, max_length=64, max_capacity=20),
]

schema = CollectionSchema(fields, enable_dynamic_field=True,
                          description="企业技术文档智能问答系统")

client = MilvusClient(uri="http://localhost:19530")
client.create_collection(collection_name="tech_docs", schema=schema, num_shards=2)
```

### Schema 设计最佳实践

| 设计点 | 推荐做法 | 原因 |
|--------|----------|------|
| 主键类型 | VARCHAR（业务 ID） | 方便关联外部系统 |
| 多向量列 | 标题向量 + 内容向量分开 | 可选择性搜索，提高精度 |
| Partition Key | 区分度适中的字段 (10-100 值) | 太多分区反而降低性能 |
| Dynamic Field | 开启 | 灵活存储非固定元信息 |
| VARCHAR 长度 | 按实际最大值设置 | 影响内存分配 |

### 数据导入

```python
from FlagEmbedding import BGEM3FlagModel
import time

model = BGEM3FlagModel("BAAI/bge-m3", use_fp16=True)

# 模拟文档
documents = [
    {
        "chunk_id": "k8s_deploy_001_chunk_0",
        "title": "Kubernetes 服务部署指南",
        "content": "本文介绍如何在 K8s 集群中部署微服务...",
        "department": "infra",
        "author": "张三",
        "source": "confluence",
        "created_at": int(time.time()),
        "tags": ["kubernetes", "部署", "devops"],
        "confluence_page_id": "12345"  # Dynamic Field
    },
]

# 生成向量
title_out = model.encode([d["title"] for d in documents], return_dense=True)
content_out = model.encode([d["content"] for d in documents],
                           return_dense=True, return_sparse=True)

# 组装数据
for i, doc in enumerate(documents):
    doc["title_vec"] = title_out["dense_vecs"][i].tolist()
    doc["content_vec"] = content_out["dense_vecs"][i].tolist()
    doc["sparse_vec"] = content_out["lexical_weights"][i]

# 批量插入（推荐每批 10,000-50,000）
BATCH_SIZE = 10000
for i in range(0, len(documents), BATCH_SIZE):
    client.insert("tech_docs", documents[i:i+BATCH_SIZE])

client.flush("tech_docs")  # 刷盘！不 flush 搜索性能极差
```

---

## 索引策略深度配置

### 索引类型全景

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Milvus 索引类型                                            │
├─────────────────────────────────────────────────────────────────────────────┤
│  向量索引:                                                                  │
│   HNSW          ← 推荐！均衡性能              IVF_FLAT     ← 大规模数据    │
│   IVF_SQ8       ← 内存受限                    IVF_PQ       ← 极致压缩      │
│   FLAT          ← 小数据精确搜索              DISKANN      ← 超大规模      │
│   GPU_IVF_FLAT  ← GPU 环境                    AUTOINDEX    ← 自动选择      │
│                                                                             │
│  标量索引:                                                                  │
│   STL_SORT ← 数值    INVERTED ← VARCHAR    BITMAP ← 低基数枚举           │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 索引选择指南

| 数据规模 | 推荐索引 | 参数建议 |
|----------|----------|----------|
| < 10 万 | FLAT | 无需参数 |
| 10-500 万 | **HNSW** | M=16, efConstruction=256 |
| 500 万-5000 万 | HNSW 或 IVF_FLAT | HNSW: M=32; IVF: nlist=4096 |
| > 5000 万 | IVF_PQ 或 DISKANN | nlist=4096, m=32 |

### 案例索引配置

```python
# 标题向量索引
client.create_index("tech_docs", "title_vec", {
    "index_type": "HNSW", "metric_type": "COSINE",
    "params": {"M": 16, "efConstruction": 256}
})

# 内容向量索引（精度更重要，M 值更高）
client.create_index("tech_docs", "content_vec", {
    "index_type": "HNSW", "metric_type": "COSINE",
    "params": {"M": 32, "efConstruction": 256}
})

# 稀疏向量索引
client.create_index("tech_docs", "sparse_vec", {
    "index_type": "SPARSE_INVERTED_INDEX", "metric_type": "IP"
})

# 标量索引
client.create_index("tech_docs", "department", {"index_type": "BITMAP"})
client.create_index("tech_docs", "created_at", {"index_type": "STL_SORT"})
client.create_index("tech_docs", "source", {"index_type": "INVERTED"})

client.load_collection("tech_docs")  # 加载到内存，搜索前必须!
```

> **踩坑警告**：`create_index()` 是异步的！返回不代表索引构建完成。需等待 `load_collection()` 成功才能正常搜索。

---

## 多租户方案

### 三种方案对比

```
┌─────────────────────────────────────────────────────────────────────────────┐
│  方案 1: Database 级      方案 2: Collection 级      方案 3: Partition Key  │
│  ┌─────┐ ┌─────┐         ┌──────────────────┐       ┌──────────────────┐  │
│  │DB:  │ │DB:  │         │ Collection:      │       │ Collection:      │  │
│  │infra│ │back │         │ docs_infra       │       │ tech_docs        │  │
│  │┌───┐│ │┌───┐│         │ docs_backend     │       │ PK: department   │  │
│  ││doc││ ││doc││         │ docs_frontend    │       │ [infra|back|...] │  │
│  │└───┘│ │└───┘│         └──────────────────┘       └──────────────────┘  │
│  └─────┘ └─────┘                                                          │
│  隔离: ★★★★★             隔离: ★★★★                 隔离: ★★★              │
│  复杂度: 高               复杂度: 中                  复杂度: 低 ← 推荐！   │
│  租户数: < 10             租户数: 10-100              租户数: 10-1000       │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 案例选择：Partition Key

```python
# 已在 Schema 中设置: is_partition_key=True

# 搜索时自动路由到对应分区
results = client.search(
    collection_name="tech_docs",
    data=[query_vec],
    anns_field="content_vec",
    filter='department == "infra"',  # ← 自动路由到 infra 分区
    limit=10,
    output_fields=["title", "content", "author"]
)
```

---

## 一致性级别

### 四级一致性

| 级别 | 写入可见延迟 | 搜索延迟 | 适用场景 |
|------|-------------|----------|----------|
| **Strong** | 0（立即可见） | 最高 (+50-200ms) | 金融、医疗 |
| **Bounded** | ≤ t 秒（可配） | 中等 | 需要较新数据 |
| **Session** | 同 Session 立即 | 低 | **大部分场景（推荐）** |
| **Eventually** | 不保证（1-10s） | 最低 | 离线分析 |

```python
# 文档刚上传 → 强一致（确保搜到）
results = client.search(..., consistency_level="Strong")

# 日常搜索 → 会话一致
results = client.search(..., consistency_level="Session")

# 报表分析 → 最终一致（最快）
results = client.search(..., consistency_level="Eventually")
```

---

## 案例实战 Part 2：搜索优化与混合检索

### 语义搜索

```python
def semantic_search(query_text, department=None, top_k=10):
    query_output = model.encode([query_text], return_dense=True)
    query_vec = query_output["dense_vecs"][0].tolist()

    filter_expr = f'department == "{department}"' if department else ""

    return client.search(
        collection_name="tech_docs",
        data=[query_vec],
        anns_field="content_vec",
        search_params={"metric_type": "COSINE", "params": {"ef": 128}},
        filter=filter_expr,
        limit=top_k,
        output_fields=["title", "content", "department", "author"]
    )

results = semantic_search("怎么发布服务到 K8s", department="infra")
```

### 混合搜索（语义 + 关键词 + RRF 融合）

```python
from pymilvus import Collection, AnnSearchRequest, RRFRanker

def hybrid_search(query_text, department=None, top_k=10):
    query_out = model.encode([query_text], return_dense=True, return_sparse=True)
    dense_vec = query_out["dense_vecs"][0].tolist()
    sparse_vec = query_out["lexical_weights"][0]

    filter_expr = f'department == "{department}"' if department else ""

    dense_req = AnnSearchRequest(
        data=[dense_vec], anns_field="content_vec",
        param={"metric_type": "COSINE", "params": {"ef": 128}},
        limit=top_k * 2, expr=filter_expr
    )
    sparse_req = AnnSearchRequest(
        data=[sparse_vec], anns_field="sparse_vec",
        param={"metric_type": "IP"}, limit=top_k * 2, expr=filter_expr
    )

    collection = Collection("tech_docs")
    return collection.hybrid_search(
        reqs=[dense_req, sparse_req],
        ranker=RRFRanker(k=60),
        limit=top_k,
        output_fields=["title", "content", "department"]
    )

# "gRPC 超时配置" — 语义匹配 "RPC 调用超时设置"，关键词精确匹配 "gRPC"
results = hybrid_search("gRPC 超时配置", department="backend")
```

### 搜索参数调优

```
ef 值对性能的影响（150 万向量, HNSW M=32）

│ ef  │  延迟    │ 召回率@10│ 说明              │
├─────┼──────────┼──────────┼───────────────────┤
│  32 │  0.8ms   │  90%     │ 低延迟场景         │
│  64 │  1.2ms   │  95%     │ 常规场景           │
│ 128 │  2.5ms   │  98%     │ ← 案例推荐值       │
│ 256 │  5.0ms   │  99%     │ 高精度需求         │

经验: ef ≥ limit × 10，如 limit=10 则 ef=128
```

---

## 运维监控

### Prometheus + Grafana 监控

```
Grafana Dashboard → Prometheus → Milvus 各组件 :9091/metrics
```

### 关键监控指标

| 类别 | 指标 | 告警阈值 |
|------|------|----------|
| 搜索延迟 | `milvus_proxy_sq_latency_bucket` | P99 > 200ms |
| 写入延迟 | `milvus_proxy_mutation_latency` | P99 > 500ms |
| 内存占用 | `milvus_querynode_collection_memory_size` | > 80% 物理内存 |
| Growing Segment | `milvus_datacoord_growing_segment_count` | > 50 (需 flush) |
| 搜索错误率 | `milvus_proxy_sq_req_count{status="fail"}` | > 1% |

### 告警规则示例

```yaml
# prometheus-alerts.yml
groups:
  - name: milvus-alerts
    rules:
      - alert: MilvusSearchLatencyHigh
        expr: histogram_quantile(0.99, rate(milvus_proxy_sq_latency_bucket[5m])) > 0.2
        for: 5m
        annotations:
          summary: "搜索 P99 > 200ms"

      - alert: MilvusGrowingSegmentPileup
        expr: milvus_datacoord_growing_segment_count > 50
        for: 15m
        annotations:
          summary: "Growing Segment 堆积，需检查 flush"
```

---

## 性能调优

### 写入优化

```python
# ❌ 逐条插入
for doc in documents:
    client.insert("tech_docs", [doc])

# ✓ 批量插入（10,000-50,000 条/批）
for i in range(0, len(documents), 10000):
    client.insert("tech_docs", documents[i:i+10000])
client.flush("tech_docs")  # 全部写完统一 flush，避免产生大量小 Segment

# ✓ 并行写入
import concurrent.futures
def insert_batch(batch):
    local_client = MilvusClient(uri="http://localhost:19530")
    return local_client.insert("tech_docs", batch)

batches = [documents[i:i+10000] for i in range(0, len(documents), 10000)]
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as executor:
    list(executor.map(insert_batch, batches))
```

### 搜索优化

```python
# 1. 预热（首次搜索加载索引到缓存）
import numpy as np
for _ in range(10):
    client.search("tech_docs", data=[np.random.randn(1024).tolist()],
                  anns_field="content_vec", limit=10)

# 2. 只返回需要的字段
results = client.search(..., output_fields=["title", "chunk_id"])  # 不要 ["*"]

# 3. 利用 Partition Key 缩小范围
results = client.search(..., filter='department == "infra"')  # 只搜 1/10 数据
```

### 资源规划（案例: 150 万 × 1024 维 × 双向量）

```
内存估算:
  content_vec: 150万 × 1024 × 4B × 1.5 (索引) ≈ 9.2GB
  title_vec:   150万 × 1024 × 4B × 1.5         ≈ 9.2GB
  sparse_vec + 标量:                             ≈ 3GB
  总计: ~21.4GB

  → 3 个 QueryNode × 8GB 内存
  → QueryCoord 自动均分 Segment
```

---

## 常见踩坑与注意事项

| # | 问题 | 现象 | 解决方案 |
|---|------|------|----------|
| 1 | 忘记 flush | insert 成功但 search 空 | `client.flush("collection")` |
| 2 | 忘记 load | search 报错 "not loaded" | `client.load_collection("col")` |
| 3 | limit > 16384 | 搜索报错 | 分批搜索或修改 `proxy.maxTopK` |
| 4 | 主键重复插入 | 数据重复 | 用 `upsert()` 替代 `insert()` |
| 5 | 频繁 flush | 大量小 Segment，搜索变慢 | 攒批 flush + `compact()` |
| 6 | 维度不匹配 | dimension mismatch | 确保 Embedding 输出维度 = Schema dim |
| 7 | 标量过滤慢 | 带 filter 搜索慢 5-10x | 为过滤字段创建标量索引 |
| 8 | 未 release | QueryNode OOM | 不用的 Collection 及时 release |
| 9 | 索引未完成 | 搜索延迟飙高 | 等索引构建完成再 load |
| 10 | 连接数耗尽 | 连接超时 | 使用 MilvusClient 单例 + 连接池 |

### 生产 Checklist

```
□ Schema: 主键/向量维度/Partition Key/标量索引
□ 索引: 向量索引参数已调优，构建已完成
□ 数据: 批量导入 + flush + Compaction
□ 搜索: P99 延迟达标，召回率验证
□ 监控: Prometheus + Grafana + 告警规则
□ 高可用: QueryNode ≥ 2，Proxy ≥ 2，etcd 3 节点
```

---

## 案例实战 Part 3：生产部署与完整代码

### 完整 RAG 问答服务

```python
"""企业技术文档智能问答系统 — 完整实现"""
from pymilvus import MilvusClient, Collection, AnnSearchRequest, RRFRanker
from FlagEmbedding import BGEM3FlagModel
from openai import OpenAI

MILVUS_URI = "http://milvus-proxy.milvus.svc:19530"
COLLECTION = "tech_docs"

milvus = MilvusClient(uri=MILVUS_URI)
embed = BGEM3FlagModel("BAAI/bge-m3", use_fp16=True)
llm = OpenAI()

class TechDocQA:
    """技术文档问答服务"""

    def search(self, query: str, department: str = None, top_k: int = 5):
        """混合搜索: dense + sparse + RRF"""
        out = embed.encode([query], return_dense=True, return_sparse=True)

        dense_req = AnnSearchRequest(
            data=[out["dense_vecs"][0].tolist()],
            anns_field="content_vec",
            param={"metric_type": "COSINE", "params": {"ef": 128}},
            limit=top_k * 3,
            expr=f'department == "{department}"' if department else ""
        )
        sparse_req = AnnSearchRequest(
            data=[out["lexical_weights"][0]],
            anns_field="sparse_vec",
            param={"metric_type": "IP"},
            limit=top_k * 3,
            expr=f'department == "{department}"' if department else ""
        )

        col = Collection(COLLECTION)
        results = col.hybrid_search(
            reqs=[dense_req, sparse_req],
            ranker=RRFRanker(k=60),
            limit=top_k,
            output_fields=["title", "content", "department", "source"]
        )
        return results

    def answer(self, query: str, department: str = None):
        """RAG 问答: 检索 + 生成"""
        results = self.search(query, department)

        # 构建上下文
        context_parts = []
        for hits in results:
            for i, hit in enumerate(hits):
                ctx = f"[文档{i+1}] {hit.entity.get('title')}\n{hit.entity.get('content')}"
                context_parts.append(ctx)
        context = "\n\n".join(context_parts)

        # LLM 生成
        response = llm.chat.completions.create(
            model="gpt-4o-mini",
            messages=[
                {"role": "system", "content":
                 "你是企业技术文档助手。基于提供的文档回答问题。"
                 "如果文档中没有相关信息，请明确说明。引用时标注[文档N]。"},
                {"role": "user", "content":
                 f"文档:\n{context}\n\n问题: {query}"}
            ]
        )
        return {
            "answer": response.choices[0].message.content,
            "sources": [hit.entity.get("source") for hits in results for hit in hits]
        }

# 使用
qa = TechDocQA()
result = qa.answer("K8s 部署时怎么配置资源限制？", department="infra")
print(result["answer"])
print("来源:", result["sources"])
```

### K8s 生产部署配置

```yaml
# milvus-values.yaml (Helm values)
cluster:
  enabled: true
proxy:
  replicas: 2
  resources:
    requests: { cpu: "2", memory: "4Gi" }
queryNode:
  replicas: 3
  resources:
    requests: { cpu: "4", memory: "8Gi" }
    limits: { cpu: "8", memory: "16Gi" }
dataNode:
  replicas: 2
  resources:
    requests: { cpu: "2", memory: "4Gi" }
indexNode:
  replicas: 1
  resources:
    requests: { cpu: "4", memory: "8Gi" }
etcd:
  replicaCount: 3
minio:
  mode: distributed
  replicas: 4
pulsar:
  enabled: true
```

```bash
helm install milvus milvus/milvus -f milvus-values.yaml -n milvus --create-namespace
```

---

## 总结

### 案例完整链路回顾

```
需求分析 → Schema 设计 → 创建 Collection → 数据导入 → 索引构建
    → 多租户 (Partition Key) → 一致性 (Session)
    → 语义搜索 → 混合搜索 (Dense+Sparse+RRF) → 对接 LLM (RAG)
    → K8s 部署 → 监控告警 → 性能调优

关键决策:
  • 双向量列 (title_vec + content_vec) → 提升不同长度查询的精度
  • Partition Key (department) → 零成本多租户
  • 混合搜索 (Dense + Sparse + RRF) → 兼顾语义和关键词
  • HNSW 索引 (M=32, ef=128) → 最佳性能均衡
  • 3 QueryNode × 8GB → 满足 21GB 内存需求
```

### 核心要点速查

| 主题 | 关键点 |
|------|--------|
| 架构 | 存储计算分离四层架构，Worker 无状态可水平扩展 |
| Schema | 多向量列 + Partition Key + Dynamic Field |
| 索引 | < 500 万用 HNSW，> 5000 万用 IVF_PQ/DISKANN |
| 多租户 | Partition Key 最简方案，10-1000 租户 |
| 一致性 | 默认 Session，写后即查用 Strong |
| 写入 | 批量 1 万+/次，统一 flush，避免小 Segment |
| 搜索 | ef ≥ limit × 10，预热，只返回必要字段 |
| 监控 | Prometheus + Grafana，关注 P99 延迟和内存 |

---

*上一篇：[10-Token 节省策略](10-token-optimization.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Milvus.** *Milvus Documentation.*  
   https://milvus.io/docs/

2. **Wang, J., et al. (2021).** *Milvus: A Purpose-Built Vector Data Management System.* SIGMOD 2021.  
   https://dl.acm.org/doi/10.1145/3448016.3457550

3. **Zilliz.** *Zilliz Cloud (Managed Milvus).*  
   https://zilliz.com/
