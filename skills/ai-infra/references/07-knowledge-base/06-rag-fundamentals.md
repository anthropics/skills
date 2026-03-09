# RAG 基础

> RAG（Retrieval-Augmented Generation）是 LLM 接入知识库的核心架构。

## 目录

- [什么是 RAG](#什么是-rag)
- [RAG 核心架构](#rag-核心架构)
- [Naive RAG 实现](#naive-rag-实现)
- [Prompt 构造模式](#prompt-构造模式)
- [RAG vs Fine-tuning](#rag-vs-fine-tuning)
- [LangChain RAG 实现](#langchain-rag-实现)
- [LlamaIndex RAG 实现](#llamaindex-rag-实现)
- [RAG 常见问题与调优](#rag-常见问题与调优)
- [实战练习](#实战练习)

---

## 什么是 RAG

### 定义

RAG（Retrieval-Augmented Generation，检索增强生成）是一种将外部知识检索与 LLM 生成结合的架构。核心思想：**先检索相关文档，再让 LLM 基于文档生成回答**。

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         RAG = Retrieval + Generation                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   传统 LLM (纯生成):                                                       │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   用户问题 ──────────────────────────────▶ LLM ──▶ 回答             │   │
│   │                                                                     │   │
│   │   问题: 幻觉、知识过时、无法访问私有数据                            │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   RAG (检索 + 生成):                                                        │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │                       ┌──────────────┐                              │   │
│   │   用户问题 ──检索──▶  │   知识库      │                              │   │
│   │       │               │  (向量数据库) │                              │   │
│   │       │               └──────┬───────┘                              │   │
│   │       │                      │ Top-K 文档                           │   │
│   │       │                      ▼                                      │   │
│   │       └───────────▶ [问题 + 文档] ──▶ LLM ──▶ 准确回答             │   │
│   │                                                                     │   │
│   │   优势: 有依据、可追溯、知识可更新、减少幻觉                        │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### RAG 的核心价值

| 价值 | 说明 |
|------|------|
| **消除幻觉** | 回答基于检索到的文档，而非模型的参数记忆 |
| **知识更新** | 更新知识库即可，无需重新训练模型 |
| **可追溯** | 每个回答可标注来源文档 |
| **低成本** | 不需要 Fine-tuning 的 GPU 资源 |
| **隐私保护** | 私有数据只在知识库中，不需要发送给第三方训练 |

---

## RAG 核心架构

### 三阶段流程

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                         RAG 三阶段详解                                       │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   阶段1: Indexing (离线索引)                                                │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   文档 → 分块 → Embedding → 存入向量数据库                          │   │
│   │   (一次性或定期更新)                                                │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   阶段2: Retrieval (在线检索)                                               │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   用户查询 → Embedding → 向量相似度搜索 → Top-K 文档               │   │
│   │   (每次用户提问时执行, 延迟 10-100ms)                               │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   阶段3: Generation (在线生成)                                              │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   [System Prompt + 检索文档 + 用户问题] → LLM → 回答               │   │
│   │   (每次用户提问时执行, 延迟 1-10s)                                  │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Naive RAG 实现

### 最简实现

```python
from openai import OpenAI
from sentence_transformers import SentenceTransformer
import numpy as np

# 初始化
client = OpenAI()
embed_model = SentenceTransformer("BAAI/bge-m3")

# 1. 准备知识库 (简化版, 生产中用向量数据库)
documents = [
    "ZeRO-3 将优化器状态、梯度和模型参数全部在数据并行维度分片。每个 GPU 只保存参数的 1/N。",
    "HNSW 是一种基于图的向量索引算法，通过多层导航图结构实现高效的近似最近邻搜索。",
    "vLLM 使用 PagedAttention 技术管理 KV Cache，将注意力机制的显存使用效率提升到接近 100%。",
    "FlashAttention 通过 tiling 技术减少 GPU HBM 与 SRAM 之间的数据传输，加速 Attention 计算。",
]
doc_embeddings = embed_model.encode(documents, normalize_embeddings=True)

# 2. 检索
def retrieve(query: str, top_k: int = 3) -> list:
    query_emb = embed_model.encode([query], normalize_embeddings=True)
    scores = np.dot(doc_embeddings, query_emb.T).flatten()
    top_indices = np.argsort(scores)[::-1][:top_k]
    return [(documents[i], scores[i]) for i in top_indices]

# 3. 生成
def generate_with_rag(query: str):
    # 检索相关文档
    retrieved = retrieve(query, top_k=3)
    context = "\n".join([f"[{i+1}] {doc}" for i, (doc, _) in enumerate(retrieved)])
    
    # 构造 Prompt
    prompt = f"""基于以下参考资料回答问题。请标注引用来源 [1][2] 等。
如果资料中没有相关信息，请明确说明。

参考资料：
{context}

问题：{query}"""
    
    # 调用 LLM
    response = client.chat.completions.create(
        model="gpt-4o-mini",
        messages=[
            {"role": "system", "content": "你是一个 AI Infra 专家助手。"},
            {"role": "user", "content": prompt}
        ],
        temperature=0
    )
    
    return response.choices[0].message.content

# 使用
answer = generate_with_rag("ZeRO-3 如何优化显存？")
print(answer)
```

---

## Prompt 构造模式

### 常见 Prompt 模板

```python
# 模式1: 基础 RAG Prompt
basic_prompt = """基于以下参考资料回答问题。

参考资料：
{context}

问题：{question}

回答："""

# 模式2: 带引用的 RAG Prompt (推荐)
citation_prompt = """基于以下参考资料回答问题。在回答中用 [1][2] 等标注信息来源。
如果参考资料中没有相关信息，请回答"根据现有资料无法回答此问题"。

参考资料：
{context}

问题：{question}

请提供准确、详细的回答："""

# 模式3: 思维链 RAG Prompt
cot_prompt = """你是一个专业的 AI 基础设施专家。请基于以下参考资料回答问题。

参考资料：
{context}

问题：{question}

请按以下步骤回答：
1. 首先分析问题涉及哪些知识点
2. 从参考资料中找出相关信息
3. 综合信息给出完整回答
4. 标注每个论点的来源 [1][2]"""

# 模式4: 多语言 RAG Prompt
multilingual_prompt = """Answer the question based on the given context.
Use the same language as the question.

Context:
{context}

Question: {question}

Answer:"""
```

---

## RAG vs Fine-tuning

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    RAG vs Fine-tuning 决策                                    │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   选 RAG:                               选 Fine-tuning:                    │
│   ✅ 知识频繁更新                        ✅ 需要改变模型行为/风格           │
│   ✅ 需要追溯来源                        ✅ 需要学习特定领域的"语言"        │
│   ✅ 预算有限                            ✅ 需要极低推理延迟                │
│   ✅ 知识量大 (百万文档)                 ✅ 知识量小但深度要求高             │
│   ✅ 需要快速迭代                        ✅ 需要结构化输出                  │
│                                                                             │
│   最佳实践: RAG + Fine-tuning 结合使用                                      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   Fine-tuning: 让模型学会"如何使用检索结果"                         │   │
│   │   RAG: 提供最新/准确的知识                                          │   │
│   │   结合: 模型既懂领域语言，又有最新知识                              │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

| 维度 | RAG | Fine-tuning | RAG + FT |
|------|-----|-------------|----------|
| **知识更新** | ⭐⭐⭐⭐⭐ 实时 | ⭐ 需重训 | ⭐⭐⭐⭐⭐ |
| **幻觉控制** | ⭐⭐⭐⭐ 好 | ⭐⭐ 一般 | ⭐⭐⭐⭐⭐ |
| **领域适配** | ⭐⭐⭐ 中 | ⭐⭐⭐⭐⭐ 强 | ⭐⭐⭐⭐⭐ |
| **成本** | ⭐⭐⭐⭐ 低 | ⭐⭐ 高 | ⭐⭐⭐ 中 |
| **延迟** | ⭐⭐⭐ 增加 | ⭐⭐⭐⭐⭐ 无 | ⭐⭐⭐ |
| **可解释性** | ⭐⭐⭐⭐⭐ 高 | ⭐ 低 | ⭐⭐⭐⭐⭐ |

---

## LangChain RAG 实现

```python
from langchain_openai import ChatOpenAI, OpenAIEmbeddings
from langchain_community.vectorstores import Milvus
from langchain.chains import RetrievalQA
from langchain.prompts import PromptTemplate

# 1. 初始化组件
llm = ChatOpenAI(model="gpt-4o", temperature=0)
embeddings = OpenAIEmbeddings(model="text-embedding-3-large", dimensions=1024)

# 2. 连接知识库
vectorstore = Milvus(
    embedding_function=embeddings,
    connection_args={"host": "localhost", "port": "19530"},
    collection_name="ai_infra_kb"
)

# 3. 自定义 Prompt
prompt = PromptTemplate(
    template="""你是 AI Infra 专家。基于以下参考资料回答问题，用 [1][2] 标注来源。
如果资料不足，请明确说明。

参考资料：
{context}

问题：{question}

专业回答：""",
    input_variables=["context", "question"]
)

# 4. 构建 RAG Chain
qa_chain = RetrievalQA.from_chain_type(
    llm=llm,
    chain_type="stuff",  # stuff=全部塞入, map_reduce=分段处理, refine=迭代精炼
    retriever=vectorstore.as_retriever(
        search_type="similarity",
        search_kwargs={"k": 5}
    ),
    chain_type_kwargs={"prompt": prompt},
    return_source_documents=True
)

# 5. 使用
result = qa_chain.invoke({"query": "ZeRO-3 如何优化显存？"})
print("回答:", result["result"])
print("\n来源:")
for doc in result["source_documents"]:
    print(f"  - {doc.metadata.get('source', 'unknown')}")
```

---

## LlamaIndex RAG 实现

```python
from llama_index.core import (
    VectorStoreIndex,
    SimpleDirectoryReader,
    Settings,
    StorageContext,
)
from llama_index.llms.openai import OpenAI
from llama_index.embeddings.openai import OpenAIEmbedding

# 1. 配置
Settings.llm = OpenAI(model="gpt-4o", temperature=0)
Settings.embed_model = OpenAIEmbedding(model="text-embedding-3-large", dimensions=1024)

# 2. 加载文档 + 构建索引 (3 行核心代码)
documents = SimpleDirectoryReader("./docs").load_data()
index = VectorStoreIndex.from_documents(documents)
query_engine = index.as_query_engine(similarity_top_k=5)

# 3. 查询
response = query_engine.query("ZeRO-3 如何优化显存？")
print(response)

# 4. 查看来源
for node in response.source_nodes:
    print(f"  Score: {node.score:.4f}")
    print(f"  Source: {node.metadata.get('file_name', 'unknown')}")
    print(f"  Text: {node.text[:100]}...")
```

---

## RAG 常见问题与调优

| 问题 | 症状 | 解决方案 |
|------|------|----------|
| **检索不到** | 相关文档存在但没被检索到 | 优化分块策略、调整 top_k、使用 HyDE |
| **检索了但不相关** | 返回的文档与问题无关 | 添加 Re-ranking、使用混合搜索 |
| **回答不用检索结果** | LLM 忽略上下文，用自己的知识 | 优化 Prompt、降低 temperature |
| **上下文过长** | Token 超限或信息被稀释 | Prompt 压缩、减少 top_k、精排 |
| **回答太笼统** | 缺乏具体细节 | 增大 top_k、优化分块保留更多上下文 |

---

## 实战练习

### 练习：构建 RAG 问答系统

```python
# rag_demo.py - 完整 RAG 示例
from langchain_openai import ChatOpenAI, OpenAIEmbeddings
from langchain_community.vectorstores import Chroma
from langchain.chains import RetrievalQA
from langchain_community.document_loaders import DirectoryLoader, TextLoader
from langchain.text_splitter import RecursiveCharacterTextSplitter

# Step 1: 构建知识库
loader = DirectoryLoader("./docs", glob="**/*.md", loader_cls=TextLoader)
docs = loader.load()
chunks = RecursiveCharacterTextSplitter(chunk_size=512, chunk_overlap=64).split_documents(docs)
vectorstore = Chroma.from_documents(chunks, OpenAIEmbeddings(), persist_directory="./db")

# Step 2: 构建 RAG
qa = RetrievalQA.from_chain_type(
    llm=ChatOpenAI(model="gpt-4o-mini", temperature=0),
    retriever=vectorstore.as_retriever(search_kwargs={"k": 3}),
    return_source_documents=True
)

# Step 3: 交互式问答
while True:
    query = input("\n问题 (输入 q 退出): ")
    if query.lower() == 'q':
        break
    result = qa.invoke({"query": query})
    print(f"\n回答: {result['result']}")
    print(f"来源: {[d.metadata['source'] for d in result['source_documents']]}")
```

---

*上一篇：[05-从零构建知识库](05-build-from-scratch.md)*

*下一篇：[07-高级 RAG 技术](07-advanced-rag.md)*

*返回目录：[README](README.md)*
