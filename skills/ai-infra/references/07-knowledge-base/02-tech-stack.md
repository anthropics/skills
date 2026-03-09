# 技术栈详解

> 知识库的技术栈涵盖数据处理、向量存储、语义编码、检索编排等多个层次。

## 目录

- [技术栈全景图](#技术栈全景图)
- [向量数据库](#向量数据库)
- [Embedding 模型](#embedding-模型)
- [文档处理工具链](#文档处理工具链)
- [图数据库](#图数据库)
- [全文搜索引擎](#全文搜索引擎)
- [编排框架](#编排框架)
- [RAG 平台](#rag-平台)
- [技术选型决策树](#技术选型决策树)
- [实战练习](#实战练习)

---

## 技术栈全景图

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      知识库技术栈全景图                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                   应用层 (Application Layer)                         │   │
│   │                                                                     │   │
│   │   低代码平台           自定义应用           Agent 框架              │   │
│   │   Dify, FastGPT       Web/API              AutoGPT, CrewAI        │   │
│   │   RAGFlow, Coze       企业集成             LangGraph              │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                   编排层 (Orchestration Layer)                        │   │
│   │                                                                     │   │
│   │   ┌─────────────────┐  ┌─────────────────┐  ┌─────────────────┐   │   │
│   │   │   LangChain      │  │   LlamaIndex    │  │   Haystack      │   │   │
│   │   │   通用编排框架   │  │   RAG专精框架   │  │   Pipeline框架  │   │   │
│   │   │   灵活、生态丰富 │  │   索引优化好    │  │   模块化设计    │   │   │
│   │   └─────────────────┘  └─────────────────┘  └─────────────────┘   │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                   检索增强层 (Retrieval Enhancement)                  │   │
│   │                                                                     │   │
│   │   Query Rewriting │ HyDE │ Re-ranking │ Hybrid Search │ Routing    │   │
│   │   Multi-hop │ Graph RAG │ Self-RAG │ Contextual Compression       │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                   Embedding 层 (Encoding Layer)                      │   │
│   │                                                                     │   │
│   │   文本 Embedding          多模态 Embedding         稀疏 Embedding   │   │
│   │   BGE-M3, E5, GTE        CLIP, ImageBind          SPLADE, BM25    │   │
│   │   OpenAI, Cohere, Jina   Nomic-embed-vision       ColBERT         │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                   存储检索层 (Storage & Retrieval Layer)              │   │
│   │                                                                     │   │
│   │   向量数据库           全文搜索              图数据库               │   │
│   │   ┌──────────────┐   ┌──────────────┐   ┌──────────────┐          │   │
│   │   │ Milvus       │   │ Elasticsearch│   │ Neo4j        │          │   │
│   │   │ Pinecone     │   │ OpenSearch   │   │ ArangoDB     │          │   │
│   │   │ Qdrant       │   │ MeiliSearch  │   │ Neptune      │          │   │
│   │   │ Weaviate     │   │ Typesense    │   │              │          │   │
│   │   │ Chroma       │   │              │   │              │          │   │
│   │   │ pgvector     │   │              │   │              │          │   │
│   │   └──────────────┘   └──────────────┘   └──────────────┘          │   │
│   └───────────────────────────┬─────────────────────────────────────────┘   │
│                               │                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                   数据处理层 (Data Processing Layer)                  │   │
│   │                                                                     │   │
│   │   文档解析             文本分块              数据清洗               │   │
│   │   Unstructured         LangChain Splitter    正则/NLP              │   │
│   │   LlamaParse           LlamaIndex Node       编码转换              │   │
│   │   Docling              Semantic Chunker      去重/去噪             │   │
│   │   Apache Tika          MarkdownHeader        元数据提取            │   │
│   │   Marker (PDF→MD)      RecursiveCharacter    格式统一              │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 向量数据库

### 主流向量数据库对比

| 特性 | Milvus | Pinecone | Qdrant | Weaviate | Chroma | pgvector |
|------|--------|----------|--------|----------|--------|----------|
| **类型** | 开源 | 全托管 | 开源 | 开源 | 开源 | 扩展 |
| **语言** | Go/C++ | — | Rust | Go | Python | C |
| **最大规模** | 10B+ | 数亿 | 数亿 | 数亿 | 百万级 | 千万级 |
| **分布式** | ✅ 原生 | ✅ 托管 | ✅ | ✅ | ❌ | ❌ |
| **GPU 加速** | ✅ | ❌ | ❌ | ❌ | ❌ | ❌ |
| **混合搜索** | ✅ | ✅ | ✅ | ✅ | ❌ | ✅ |
| **部署** | Docker/K8s | SaaS | Docker/K8s | Docker/K8s | pip | PG 扩展 |
| **适用** | 生产/大规模 | 快速上线 | 性能敏感 | 原型开发 | 本地/小型 | PG 生态 |

### 选型建议

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      向量数据库选型决策                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   你的场景是什么？                                                          │
│   │                                                                         │
│   ├── 本地开发/原型验证                                                     │
│   │   └── Chroma (pip install chromadb, 零配置)                            │
│   │                                                                         │
│   ├── 小型生产 (<100万向量)                                                │
│   │   ├── 已有 PostgreSQL → pgvector                                       │
│   │   └── 新项目 → Qdrant (性能好) 或 Weaviate (API 友好)                  │
│   │                                                                         │
│   ├── 中型生产 (100万-1亿向量)                                             │
│   │   ├── 不想运维 → Pinecone (全托管) 或 Zilliz Cloud                    │
│   │   └── 可以运维 → Milvus 或 Qdrant                                     │
│   │                                                                         │
│   └── 大型生产 (>1亿向量)                                                  │
│       └── Milvus (分布式, GPU 加速, 生产验证)                              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Embedding 模型

### 选型速查表

| 场景 | 推荐模型 | 理由 |
|------|----------|------|
| **中文 RAG** | BGE-M3, GTE-Qwen2 | 中文效果最佳，开源 |
| **英文 RAG** | E5-Mistral, OpenAI text-embedding-3 | MTEB 排名靠前 |
| **多语言** | BGE-M3, Cohere embed-v3 | 多语言支持好 |
| **低成本** | BGE-M3, E5-large-v2 | 开源，本地部署 |
| **长文本** | E5-Mistral-7B, GTE-Qwen2 | 支持 32K+ tokens |
| **多模态** | CLIP, Jina CLIP v2 | 文本+图片联合检索 |

### 部署示例

```python
# 本地部署 Embedding 模型（高性能推理）
from sentence_transformers import SentenceTransformer
import torch

# 加载模型 (首次会自动下载)
model = SentenceTransformer(
    "BAAI/bge-m3",
    device="cuda" if torch.cuda.is_available() else "cpu"
)

# 批量编码
texts = ["文本1", "文本2", "文本3"]
embeddings = model.encode(
    texts,
    normalize_embeddings=True,  # L2 归一化
    batch_size=32,              # 批量处理
    show_progress_bar=True
)

# 计算相似度 (归一化后, 内积 = 余弦相似度)
import numpy as np
similarity_matrix = np.dot(embeddings, embeddings.T)
```

---

## 文档处理工具链

### 文档解析工具对比

| 工具 | 支持格式 | 特点 | 适用场景 |
|------|----------|------|----------|
| **Unstructured** | PDF/HTML/DOCX/PPT/MD | 功能全面，社区活跃 | 通用场景 |
| **LlamaParse** | PDF/DOCX/PPT | AI 驱动解析，表格好 | 复杂 PDF |
| **Docling** | PDF/DOCX | IBM 开源，结构保留好 | 学术论文 |
| **Marker** | PDF | PDF → Markdown | PDF 转换 |
| **Apache Tika** | 1000+ 格式 | Java，格式最全 | 企业级 |

### 文档处理 Pipeline 示例

```python
from unstructured.partition.auto import partition
from unstructured.chunking.title import chunk_by_title

# 1. 自动识别格式并解析
elements = partition(filename="report.pdf")

# 2. 按标题结构分块
chunks = chunk_by_title(
    elements,
    max_characters=500,
    combine_text_under_n_chars=100
)

# 3. 提取元数据
for chunk in chunks:
    print(f"类型: {chunk.category}")
    print(f"内容: {chunk.text[:100]}...")
    print(f"元数据: {chunk.metadata.to_dict()}")
```

---

## 图数据库

### 知识图谱在 RAG 中的应用

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    知识图谱 + RAG = Graph RAG                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   传统向量 RAG:                                                             │
│   "谁是 NVIDIA CEO 的妻子？"                                               │
│   → 搜索可能找到 "NVIDIA CEO" 和 "Jensen Huang 的家庭" 两篇不相关文档     │
│   → 无法连接两跳关系                                                       │
│                                                                             │
│   Graph RAG:                                                                │
│   ┌──────────┐    CEO     ┌──────────────┐   妻子    ┌─────────────┐       │
│   │  NVIDIA   │ ────────▶ │ Jensen Huang │ ────────▶ │ Lori Huang  │       │
│   └──────────┘            └──────────────┘           └─────────────┘       │
│                                                                             │
│   → 图遍历直接找到: NVIDIA → CEO → Jensen Huang → 妻子 → Lori Huang       │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### Neo4j + LLM 示例

```python
from langchain_community.graphs import Neo4jGraph
from langchain.chains import GraphCypherQAChain
from langchain_openai import ChatOpenAI

# 连接 Neo4j
graph = Neo4jGraph(
    url="bolt://localhost:7687",
    username="neo4j",
    password="password"
)

# 自动将自然语言转为 Cypher 查询
chain = GraphCypherQAChain.from_llm(
    llm=ChatOpenAI(model="gpt-4o", temperature=0),
    graph=graph,
    verbose=True,
    allow_dangerous_requests=True
)

# 查询
result = chain.invoke({"query": "谁是 NVIDIA 的 CEO？他有哪些专利？"})
# LLM 自动生成 Cypher: MATCH (c:Company {name: 'NVIDIA'})-[:CEO]->(p:Person)...
print(result["result"])
```

---

## 全文搜索引擎

### Elasticsearch 在知识库中的角色

```python
from elasticsearch import Elasticsearch

es = Elasticsearch("http://localhost:9200")

# 创建索引（支持中文分词）
es.indices.create(index="knowledge", body={
    "settings": {
        "analysis": {
            "analyzer": {
                "ik_smart_analyzer": {
                    "type": "custom",
                    "tokenizer": "ik_smart"
                }
            }
        }
    },
    "mappings": {
        "properties": {
            "title": {"type": "text", "analyzer": "ik_smart_analyzer"},
            "content": {"type": "text", "analyzer": "ik_smart_analyzer"},
            "embedding": {"type": "dense_vector", "dims": 1024},
            "source": {"type": "keyword"},
            "timestamp": {"type": "date"}
        }
    }
})

# 混合搜索: BM25 + 向量
result = es.search(index="knowledge", body={
    "query": {
        "bool": {
            "should": [
                {"match": {"content": "ZeRO-3 显存优化"}},  # BM25
                {
                    "script_score": {
                        "query": {"match_all": {}},
                        "script": {
                            "source": "cosineSimilarity(params.query_vector, 'embedding') + 1.0",
                            "params": {"query_vector": query_embedding}
                        }
                    }
                }
            ]
        }
    }
})
```

---

## 编排框架

### LangChain vs LlamaIndex

| 维度 | LangChain | LlamaIndex |
|------|-----------|------------|
| **定位** | 通用 LLM 应用框架 | RAG 专精框架 |
| **生态** | 极其丰富 | RAG 相关丰富 |
| **灵活性** | 高，可组装任意 Chain | 中，主要围绕 Index |
| **学习曲线** | 较陡 | 较平 |
| **索引能力** | 依赖外部 | 内置多种索引结构 |
| **Agent** | 强（LangGraph） | 中 |
| **适用** | 复杂 AI 应用 | RAG 为核心的应用 |

```python
# LlamaIndex: 更简洁的 RAG 实现
from llama_index.core import VectorStoreIndex, SimpleDirectoryReader

# 3 行代码构建 RAG
documents = SimpleDirectoryReader("./docs").load_data()
index = VectorStoreIndex.from_documents(documents)
query_engine = index.as_query_engine()

response = query_engine.query("什么是 ZeRO-3？")
print(response)
```

---

## RAG 平台

### 低代码 RAG 平台对比

| 平台 | 类型 | 特点 | 适用场景 |
|------|------|------|----------|
| **Dify** | 开源 | LLM 应用开发平台，可视化编排 | 快速构建 AI 应用 |
| **FastGPT** | 开源 | 专注知识库问答 | 企业知识库 |
| **RAGFlow** | 开源 | 深度文档理解引擎 | 文档密集场景 |
| **Coze** | 商业 | 字节跳动，Bot 构建平台 | 快速原型 |
| **MaxKB** | 开源 | 面向企业的知识库问答 | 企业级部署 |

---

## 技术选型决策树

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                      技术选型决策树                                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   项目阶段？                                                                │
│   │                                                                         │
│   ├── POC / 原型验证                                                        │
│   │   ├── 向量库: Chroma (pip install, 零运维)                             │
│   │   ├── Embedding: OpenAI text-embedding-3-small (省事)                  │
│   │   ├── 框架: LlamaIndex (3 行代码 RAG)                                 │
│   │   └── 平台: Dify (可视化，不写代码)                                    │
│   │                                                                         │
│   ├── MVP / 小规模上线                                                      │
│   │   ├── 向量库: Qdrant 或 pgvector                                       │
│   │   ├── Embedding: BGE-M3 (开源本地部署)                                 │
│   │   ├── 搜索: 向量 + BM25 混合                                          │
│   │   ├── 框架: LangChain (灵活)                                          │
│   │   └── 评估: RAGAS                                                      │
│   │                                                                         │
│   └── 生产 / 大规模                                                         │
│       ├── 向量库: Milvus (分布式, GPU 加速)                                │
│       ├── Embedding: BGE-M3 自托管 + 微调                                  │
│       ├── 搜索: Milvus + Elasticsearch + Neo4j (混合)                     │
│       ├── 框架: LangChain + 自定义 Pipeline                               │
│       ├── Re-ranking: BGE-Reranker                                        │
│       ├── 评估: RAGAS + 自定义指标                                         │
│       └── 监控: LangSmith + Prometheus                                    │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 实战练习

### 练习 1：搭建本地开发环境

```bash
# 1. 安装核心依赖
pip install langchain langchain-openai langchain-community
pip install chromadb sentence-transformers pymilvus

# 2. 启动 Milvus (可选, 用于生产级开发)
docker compose up -d milvus

# 3. 启动 Elasticsearch (可选, 用于混合搜索)
docker run -d --name es -p 9200:9200 -e "discovery.type=single-node" \
    elasticsearch:8.11.0

# 4. 验证安装
python -c "import langchain, chromadb; print('环境就绪!')"
```

### 练习 2：对比不同向量数据库

```python
# benchmark_vectordb.py
import time
import numpy as np

def benchmark_insert(vectordb, vectors, num_vectors=10000):
    """测试插入性能"""
    start = time.time()
    vectordb.insert(vectors[:num_vectors])
    elapsed = time.time() - start
    print(f"插入 {num_vectors} 条: {elapsed:.2f}s ({num_vectors/elapsed:.0f} 条/秒)")

def benchmark_search(vectordb, query_vector, k=10, num_queries=100):
    """测试搜索性能"""
    start = time.time()
    for _ in range(num_queries):
        vectordb.search(query_vector, k=k)
    elapsed = time.time() - start
    avg_latency = elapsed / num_queries * 1000
    print(f"搜索延迟: {avg_latency:.1f}ms (QPS: {num_queries/elapsed:.0f})")

# 生成测试数据
dim = 1024
vectors = np.random.randn(10000, dim).astype(np.float32)
query = np.random.randn(1, dim).astype(np.float32)

# 分别测试 Chroma, Qdrant, Milvus...
```

---

*上一篇：[01-什么是知识库](01-what-is-knowledge-base.md)*

*下一篇：[03-Embedding 模型](03-embedding-models.md)*

*返回目录：[README](README.md)*
