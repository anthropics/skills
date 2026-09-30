# 高级 RAG 技术

> 从 Naive RAG 到生产级 RAG，需要在检索前、检索中、检索后全链路优化。

## 目录

- [高级 RAG 全景](#高级-rag-全景)
- [Pre-Retrieval 优化](#pre-retrieval-优化)
- [Retrieval 优化](#retrieval-优化)
- [Post-Retrieval 优化](#post-retrieval-优化)
- [Self-RAG](#self-rag)
- [Corrective RAG](#corrective-rag)
- [Graph RAG](#graph-rag)
- [Agentic RAG](#agentic-rag)
- [Modular RAG 架构](#modular-rag-架构)
- [实战练习](#实战练习)

---

## 高级 RAG 全景

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Naive RAG vs Advanced RAG                                  │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Naive RAG:                                                                │
│   Query → Embed → Search → Top-K → Stuff into Prompt → LLM → Answer       │
│                                                                             │
│   问题:                                                                     │
│   ❌ 用户查询质量差 → 检索不到相关文档                                      │
│   ❌ 检索返回噪声多 → LLM 被干扰                                           │
│   ❌ 不知道何时该检索 → 不需要检索时也检索                                  │
│   ❌ 单一检索策略 → 覆盖不全                                               │
│                                                                             │
│   Advanced RAG:                                                             │
│   ┌───────────────┐  ┌───────────────┐  ┌───────────────┐                 │
│   │ Pre-Retrieval │→│   Retrieval   │→│Post-Retrieval │→ LLM → Answer   │
│   │               │  │               │  │               │                 │
│   │ • Query改写   │  │ • 混合搜索    │  │ • Re-ranking  │                 │
│   │ • HyDE        │  │ • Multi-hop   │  │ • 压缩        │                 │
│   │ • 问题分解    │  │ • Graph RAG   │  │ • Self-RAG    │                 │
│   │ • 路由        │  │ • Parent-Child│  │ • 过滤        │                 │
│   └───────────────┘  └───────────────┘  └───────────────┘                 │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Pre-Retrieval 优化

### Query Rewriting（查询改写）

```python
from langchain_openai import ChatOpenAI
from langchain.prompts import PromptTemplate

llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)

# 查询改写: 将模糊查询转为更精确的搜索查询
rewrite_prompt = PromptTemplate(
    template="""将以下用户问题改写为更适合知识库检索的搜索查询。
生成 3 个不同角度的查询，每行一个。

用户问题: {question}

搜索查询:""",
    input_variables=["question"]
)

question = "显存不够怎么办？"
queries = llm.invoke(rewrite_prompt.format(question=question))
# 输出:
# 1. GPU 显存优化技术 ZeRO 内存优化
# 2. 大模型训练显存不足解决方案
# 3. 混合精度训练 梯度检查点 显存节省

# 多查询检索: 用每个改写后的查询分别搜索，合并结果去重
all_results = set()
for query in queries.content.strip().split("\n"):
    results = vectorstore.similarity_search(query.strip(), k=3)
    all_results.update([(r.page_content, r.metadata["source"]) for r in results])
```

### HyDE（Hypothetical Document Embedding）

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         HyDE 原理                                            │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   问题: 用户查询和文档的表达方式不同                                        │
│   用户: "显存不够怎么办？" (口语化)                                         │
│   文档: "ZeRO-3 将参数分片到所有 GPU，实现线性内存缩减" (技术化)            │
│   → 直接用查询搜索，可能召回率低                                           │
│                                                                             │
│   HyDE 解决方案:                                                            │
│   1. 让 LLM 生成一个"假设文档" (可能不准确，但表达方式接近真实文档)        │
│   2. 用假设文档的 Embedding 去检索 (而非原始查询)                           │
│                                                                             │
│   ┌────────────┐     ┌──────────────────────────┐     ┌────────────┐       │
│   │ 用户查询   │ ──▶ │ LLM 生成假设文档          │ ──▶ │ Embedding  │       │
│   │ "显存不够  │     │ "当 GPU 显存不足时，      │     │ 向量化     │       │
│   │  怎么办？" │     │  可以使用 ZeRO 优化策略..." │     │            │       │
│   └────────────┘     └──────────────────────────┘     └─────┬──────┘       │
│                                                               │             │
│                                                               ▼             │
│                                                     ┌────────────────┐     │
│                                                     │  向量相似搜索   │     │
│                                                     │  (比直接查询    │     │
│                                                     │   召回率更高)   │     │
│                                                     └────────────────┘     │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

```python
from langchain_openai import ChatOpenAI, OpenAIEmbeddings

llm = ChatOpenAI(model="gpt-4o-mini")
embeddings = OpenAIEmbeddings()

def hyde_retrieve(query: str, vectorstore, k: int = 5):
    # Step 1: 生成假设文档
    hypothesis = llm.invoke(
        f"请写一段技术文档来回答以下问题：\n{query}\n\n文档内容："
    )
    
    # Step 2: 用假设文档的 embedding 检索
    hyde_embedding = embeddings.embed_query(hypothesis.content)
    results = vectorstore.similarity_search_by_vector(hyde_embedding, k=k)
    
    return results
```

### Query Decomposition（问题分解）

```python
def decompose_query(question: str) -> list:
    """将复杂问题分解为多个子问题"""
    decompose_prompt = f"""将以下复杂问题分解为 2-4 个简单的子问题。

问题: {question}

子问题 (每行一个):"""
    
    result = llm.invoke(decompose_prompt)
    sub_questions = [q.strip() for q in result.content.strip().split("\n") if q.strip()]
    return sub_questions

# 示例
question = "比较 ZeRO-3 和 FSDP 在显存优化和通信开销方面的差异"
sub_questions = decompose_query(question)
# ["ZeRO-3 的显存优化原理是什么？",
#  "FSDP 的显存优化原理是什么？",
#  "ZeRO-3 的通信开销如何？",
#  "FSDP 的通信开销如何？"]

# 分别检索每个子问题，合并上下文
all_context = []
for sq in sub_questions:
    results = vectorstore.similarity_search(sq, k=2)
    all_context.extend([r.page_content for r in results])
```

---

## Retrieval 优化

### Hybrid Search（混合搜索）

```python
# 向量搜索 + BM25 关键词搜索 + RRF 融合
from langchain.retrievers import EnsembleRetriever
from langchain_community.retrievers import BM25Retriever
from langchain_community.vectorstores import Chroma

# 向量检索器
vector_retriever = vectorstore.as_retriever(search_kwargs={"k": 10})

# BM25 检索器 (关键词)
bm25_retriever = BM25Retriever.from_documents(documents, k=10)

# 混合检索 (RRF 融合)
ensemble_retriever = EnsembleRetriever(
    retrievers=[vector_retriever, bm25_retriever],
    weights=[0.6, 0.4]  # 向量 60%, BM25 40%
)

results = ensemble_retriever.invoke("ZeRO-3 显存优化原理")
```

### Parent-Child Retrieval

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Parent-Child 检索策略                                      │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   原理: 用小块检索 (精度高)，返回大块 (上下文完整)                          │
│                                                                             │
│   Parent (大块, 2000字):                                                    │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   第三章 分布式训练                                                  │   │
│   │   3.1 数据并行                                                      │   │
│   │   数据并行是最基础的分布式训练方式。DDP 将数据分到多个 GPU...         │   │
│   │   3.2 模型并行                                                      │   │
│   │   当模型太大无法放入单卡时，需要模型并行...                          │   │
│   │   3.3 ZeRO 优化                                                    │   │
│   │   ZeRO 将优化器状态、梯度和参数分片到所有 GPU...                    │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   Children (小块, 400字):                                                   │
│   ┌──────────┐ ┌──────────┐ ┌──────────┐ ┌──────────┐                     │
│   │ Child 1  │ │ Child 2  │ │ Child 3  │ │ Child 4  │                     │
│   │ 数据并行 │ │ DDP细节  │ │ 模型并行 │ │ ZeRO优化 │ ← 检索命中这个     │
│   └──────────┘ └──────────┘ └──────────┘ └──────────┘                     │
│                                                                             │
│   检索 Child 3 → 返回整个 Parent → LLM 获得更完整的上下文                  │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Post-Retrieval 优化

### Re-ranking（重排序）

```python
from sentence_transformers import CrossEncoder

# 加载 Cross-Encoder 重排序模型
reranker = CrossEncoder("BAAI/bge-reranker-v2-m3")

def rerank_results(query: str, candidates: list, top_k: int = 5):
    """使用 Cross-Encoder 重排序"""
    # Cross-Encoder 对 (query, doc) 对进行打分
    pairs = [(query, doc.page_content) for doc in candidates]
    scores = reranker.predict(pairs)
    
    # 按分数排序
    ranked = sorted(zip(candidates, scores), key=lambda x: x[1], reverse=True)
    return [doc for doc, score in ranked[:top_k]]

# 使用: 初始检索 20 条，精排到 5 条
candidates = vectorstore.similarity_search(query, k=20)
top_docs = rerank_results(query, candidates, top_k=5)
```

### Contextual Compression（上下文压缩）

```python
from langchain.retrievers import ContextualCompressionRetriever
from langchain.retrievers.document_compressors import LLMChainExtractor
from langchain_openai import ChatOpenAI

# 使用 LLM 从检索到的文档中只提取与问题相关的部分
compressor = LLMChainExtractor.from_llm(
    ChatOpenAI(model="gpt-4o-mini", temperature=0)
)

compression_retriever = ContextualCompressionRetriever(
    base_compressor=compressor,
    base_retriever=vectorstore.as_retriever(search_kwargs={"k": 10})
)

# 检索的文档会被压缩，只保留与问题相关的部分
compressed_docs = compression_retriever.invoke("ZeRO-3 如何分片参数？")
```

---

## Self-RAG

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         Self-RAG 架构                                        │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   核心思想: 模型自己决定 "是否需要检索" 和 "检索结果是否有用"               │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   Step 1: 判断是否需要检索 (Retrieve Token)                         │   │
│   │   ├── [Retrieve=Yes] → 执行检索                                     │   │
│   │   └── [Retrieve=No]  → 直接生成 (简单问题不需要检索)                │   │
│   │                                                                     │   │
│   │   Step 2: 评估检索结果相关性 (IsRel Token)                           │   │
│   │   ├── [IsRel=True]  → 使用该文档                                    │   │
│   │   └── [IsRel=False] → 丢弃该文档                                    │   │
│   │                                                                     │   │
│   │   Step 3: 评估生成结果质量 (IsSup Token)                             │   │
│   │   ├── [IsSup=True]  → 回答有支持，输出                              │   │
│   │   └── [IsSup=False] → 回答无支持，重新检索或拒答                    │   │
│   │                                                                     │   │
│   │   Step 4: 整体评估 (IsUse Token)                                     │   │
│   │   └── 评估最终回答的有用性                                           │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   优势: 按需检索，减少不必要的检索，提高回答质量                            │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Corrective RAG

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Corrective RAG (CRAG) 流程                                │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   Query → 检索 → 评估检索质量                                              │
│                      │                                                      │
│           ┌──────────┼──────────┐                                          │
│           │          │          │                                          │
│           ▼          ▼          ▼                                          │
│       [Correct]  [Ambiguous]  [Incorrect]                                  │
│           │          │          │                                          │
│           │          │          ▼                                          │
│           │          │    ┌────────────┐                                   │
│           │          │    │ Web Search │ ← 检索质量差时，转向网络搜索       │
│           │          │    └─────┬──────┘                                   │
│           │          │          │                                          │
│           │          ▼          │                                          │
│           │    ┌────────────┐   │                                          │
│           │    │ 知识精炼    │   │                                          │
│           │    │ (提取关键   │   │                                          │
│           │    │  信息)      │   │                                          │
│           │    └─────┬──────┘   │                                          │
│           │          │          │                                          │
│           └──────────┼──────────┘                                          │
│                      ▼                                                      │
│              ┌──────────────┐                                              │
│              │  LLM 生成    │                                              │
│              │  最终回答    │                                              │
│              └──────────────┘                                              │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Graph RAG

### 原理

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Graph RAG 核心思想                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   传统向量 RAG 的局限:                                                      │
│   • 只能检索局部片段，缺乏全局视角                                         │
│   • 多跳推理困难 (A→B→C 的关系)                                            │
│   • 总结性问题效果差 ("所有GPU架构的共同特点是什么？")                      │
│                                                                             │
│   Graph RAG 解决方案:                                                       │
│   1. 从文档中抽取实体和关系 → 构建知识图谱                                 │
│   2. 对图谱进行社区检测 → 生成社区摘要                                     │
│   3. 查询时: 匹配相关社区 → 用社区摘要回答                                │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   文档 → 实体抽取 → 知识图谱 → 社区检测 → 社区摘要                 │   │
│   │                                                                     │   │
│   │   (NVIDIA)──[开发]──(CUDA)──[用于]──(GPU计算)                       │   │
│   │      │                                   │                           │   │
│   │   [生产]                              [需要]                         │   │
│   │      │                                   │                           │   │
│   │   (H100)──[拥有]──(80GB HBM3)           (Tensor Core)               │   │
│   │                                                                     │   │
│   │   社区1: {NVIDIA, CUDA, GPU计算} → "NVIDIA 是 GPU 计算领域..."     │   │
│   │   社区2: {H100, HBM3, Tensor Core} → "H100 是最新一代..."          │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

```python
# 使用 Microsoft GraphRAG
from graphrag.index import build_index
from graphrag.query import global_search, local_search

# 1. 构建图索引 (离线)
build_index(input_dir="./docs", output_dir="./graph_index")

# 2. 全局查询 (适合总结性问题)
result = global_search(
    query="AI Infra 领域有哪些关键技术趋势？",
    index_dir="./graph_index"
)

# 3. 局部查询 (适合具体问题)
result = local_search(
    query="ZeRO-3 与 FSDP 的区别？",
    index_dir="./graph_index"
)
```

---

## Agentic RAG

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Agentic RAG 架构                                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   核心思想: LLM Agent 自主决定检索策略                                      │
│                                                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                        LLM Agent                                     │   │
│   │                                                                     │   │
│   │   "ZeRO-3 在 H100 上的吞吐量如何优化？"                             │   │
│   │                                                                     │   │
│   │   思考: 需要两方面信息:                                              │   │
│   │   1. ZeRO-3 的配置参数 → 搜索知识库                                 │   │
│   │   2. H100 的硬件规格 → 搜索知识库                                   │   │
│   │   3. 最新的 benchmark → 搜索网络                                    │   │
│   │                                                                     │   │
│   │   可用工具:                                                          │   │
│   │   🔧 search_knowledge_base(query) → 搜索内部知识库                  │   │
│   │   🔧 web_search(query) → 搜索互联网                                 │   │
│   │   🔧 run_code(code) → 执行计算                                      │   │
│   │   🔧 get_api_data(endpoint) → 调用 API                              │   │
│   │                                                                     │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   优势: 灵活、多步推理、多数据源、能处理复杂问题                            │
│   劣势: 延迟较高、成本较高、调试困难                                        │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

```python
from langchain.agents import AgentExecutor, create_openai_tools_agent
from langchain.tools import Tool
from langchain_openai import ChatOpenAI

# 定义工具
tools = [
    Tool(
        name="search_kb",
        description="搜索 AI Infra 知识库获取技术文档",
        func=lambda q: vectorstore.similarity_search(q, k=3)
    ),
    Tool(
        name="web_search",
        description="搜索互联网获取最新信息",
        func=lambda q: search_web(q)
    ),
]

# 创建 Agent
llm = ChatOpenAI(model="gpt-4o", temperature=0)
agent = create_openai_tools_agent(llm, tools, prompt)
agent_executor = AgentExecutor(agent=agent, tools=tools, verbose=True)

# 运行
result = agent_executor.invoke({
    "input": "ZeRO-3 在 H100 上怎么配置能达到最佳吞吐量？"
})
```

---

## Modular RAG 架构

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    Modular RAG: 像乐高一样组装 RAG                           │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   可替换模块:                                                               │
│                                                                             │
│   ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐           │
│   │ Indexing │ │ Pre-Ret │ │Retrieval│ │Post-Ret │ │Generate │           │
│   ├─────────┤ ├─────────┤ ├─────────┤ ├─────────┤ ├─────────┤           │
│   │ 固定分块 │ │ 直接查询│ │ 向量搜索│ │ 不处理  │ │ Stuff   │           │
│   │ 语义分块 │ │ 查询改写│ │ BM25   │ │ Rerank  │ │ Map/Red │           │
│   │ 按结构  │ │ HyDE   │ │ 混合搜索│ │ 压缩    │ │ Refine  │           │
│   │ Parent  │ │ 问题分解│ │ Graph  │ │ 过滤    │ │ Agent   │           │
│   └─────────┘ └─────────┘ └─────────┘ └─────────┘ └─────────┘           │
│                                                                             │
│   根据场景组合:                                                             │
│   • 简单QA: 固定分块 + 直接查询 + 向量搜索 + Stuff                         │
│   • 企业级: 语义分块 + HyDE + 混合搜索 + Rerank + Refine                   │
│   • 复杂推理: Parent + 问题分解 + Graph + 压缩 + Agent                     │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 实战练习

### 练习 1：实现 HyDE + Re-ranking Pipeline

```python
# advanced_rag_pipeline.py
from langchain_openai import ChatOpenAI, OpenAIEmbeddings
from langchain_community.vectorstores import Chroma
from sentence_transformers import CrossEncoder

llm = ChatOpenAI(model="gpt-4o-mini", temperature=0)
embeddings = OpenAIEmbeddings()
reranker = CrossEncoder("BAAI/bge-reranker-v2-m3")

def advanced_rag(query: str, vectorstore):
    # Step 1: HyDE
    hypothesis = llm.invoke(f"写一段文档回答: {query}").content
    hyde_emb = embeddings.embed_query(hypothesis)
    
    # Step 2: 粗召回 (20 条)
    candidates = vectorstore.similarity_search_by_vector(hyde_emb, k=20)
    
    # Step 3: Re-ranking (精排到 5 条)
    pairs = [(query, doc.page_content) for doc in candidates]
    scores = reranker.predict(pairs)
    ranked = sorted(zip(candidates, scores), key=lambda x: x[1], reverse=True)
    top_docs = [doc for doc, _ in ranked[:5]]
    
    # Step 4: 生成
    context = "\n\n".join([f"[{i+1}] {d.page_content}" for i, d in enumerate(top_docs)])
    answer = llm.invoke(
        f"基于以下资料回答，标注引用:\n{context}\n\n问题: {query}"
    )
    
    return answer.content, top_docs

answer, sources = advanced_rag("HNSW 和 IVF 哪个更适合大规模数据？", vectorstore)
print(answer)
```

### 练习 2：实现多路检索融合

```python
# multi_retrieval.py
from langchain.retrievers import EnsembleRetriever
from langchain_community.retrievers import BM25Retriever

# 向量检索
vector_retriever = vectorstore.as_retriever(search_kwargs={"k": 10})

# BM25 检索
bm25_retriever = BM25Retriever.from_documents(all_docs, k=10)

# 融合 (RRF)
ensemble = EnsembleRetriever(
    retrievers=[vector_retriever, bm25_retriever],
    weights=[0.6, 0.4]
)

results = ensemble.invoke("ZeRO Stage 3 参数分片")
for doc in results[:5]:
    print(f"  {doc.page_content[:100]}...")
```

---

*上一篇：[06-RAG 基础](06-rag-fundamentals.md)*

*下一篇：[08-消除幻觉与质量提升](08-eliminate-hallucination.md)*

*返回目录：[README](README.md)*

---

## 参考资料与引用

1. **Gao, Y., et al. (2024).** *Retrieval-Augmented Generation for Large Language Models: A Survey.*  
   https://arxiv.org/abs/2312.10997

2. **Ma, X., et al. (2023).** *Query Rewriting for Retrieval-Augmented Large Language Models.*  
   https://arxiv.org/abs/2305.14283

3. **Asai, A., et al. (2024).** *Self-RAG: Learning to Retrieve, Generate, and Critique through Self-Reflection.*  
   https://arxiv.org/abs/2310.11511
