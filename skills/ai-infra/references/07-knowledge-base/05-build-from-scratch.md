# 从零构建知识库

> 从数据采集到可检索的知识库，端到端构建完整 Pipeline。

## 目录

- [构建流程概览](#构建流程概览)
- [数据采集与来源](#数据采集与来源)
- [文档解析](#文档解析)
- [文本分块策略](#文本分块策略)
- [Embedding 生成与索引构建](#embedding-生成与索引构建)
- [端到端 Pipeline 设计](#端到端-pipeline-设计)
- [数据清洗与预处理](#数据清洗与预处理)
- [增量更新策略](#增量更新策略)
- [质量评估](#质量评估)
- [实战练习](#实战练习)

---

## 构建流程概览

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    知识库构建完整流程                                         │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │
│   │ 1.数据   │→│ 2.文档   │→│ 3.文本   │→│ 4.向量   │→│ 5.索引   │   │
│   │   采集   │  │   解析   │  │   分块   │  │   编码   │  │   存储   │   │
│   └──────────┘  └──────────┘  └──────────┘  └──────────┘  └──────────┘   │
│       │              │              │              │              │         │
│       ▼              ▼              ▼              ▼              ▼         │
│   PDF/HTML/     提取文本/      Chunking      Embedding      Milvus/       │
│   DOCX/API      表格/图片      策略选择      模型编码       Qdrant        │
│   爬虫/数据库    元数据提取     重叠/语义     批量处理       索引构建       │
│                                                                             │
│   关键决策点:                                                               │
│   • 数据质量 > 数据数量                                                    │
│   • 分块策略直接影响检索质量                                                │
│   • Embedding 模型决定语义理解能力                                          │
│   • 元数据设计影响过滤和追溯                                                │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 数据采集与来源

### 常见数据来源

| 来源 | 格式 | 采集方式 | 挑战 |
|------|------|----------|------|
| **企业文档** | PDF/DOCX/PPT | 文件系统/SharePoint | 格式多样，权限控制 |
| **网页内容** | HTML | 爬虫/API | 反爬虫，内容提取 |
| **数据库** | SQL/NoSQL | 连接器 | Schema 理解，隐私 |
| **API 数据** | JSON | REST/GraphQL | 频率限制，格式转换 |
| **代码仓库** | 多种 | Git Clone | 代码理解，依赖关系 |
| **Confluence/Notion** | HTML/MD | 官方 API | 权限，增量同步 |

### 数据采集示例

```python
from langchain_community.document_loaders import (
    PyPDFLoader,
    UnstructuredHTMLLoader,
    TextLoader,
    DirectoryLoader,
    GitLoader,
    NotionDBLoader,
    ConfluenceLoader,
    WebBaseLoader,
)

# PDF 文档
pdf_loader = PyPDFLoader("docs/manual.pdf")
pdf_docs = pdf_loader.load()

# 网页
web_loader = WebBaseLoader(["https://docs.example.com/guide"])
web_docs = web_loader.load()

# 整个目录
dir_loader = DirectoryLoader(
    "docs/",
    glob="**/*.md",
    loader_cls=TextLoader,
    show_progress=True
)
all_docs = dir_loader.load()

# Git 仓库
git_loader = GitLoader(
    clone_url="https://github.com/example/repo",
    branch="main",
    file_filter=lambda f: f.endswith((".py", ".md"))
)
code_docs = git_loader.load()

print(f"共加载 {len(all_docs)} 个文档")
```

---

## 文档解析

### 不同格式的解析策略

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    文档解析策略                                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   PDF 文档 (最复杂):                                                        │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   挑战: 布局多样、扫描件、表格、图片、多栏                          │   │
│   │                                                                     │   │
│   │   方案1: PyPDF2 / pdfplumber (简单文本 PDF)                         │   │
│   │   方案2: Unstructured (通用，布局识别)                              │   │
│   │   方案3: LlamaParse (AI 驱动，表格/图表最佳)                        │   │
│   │   方案4: Marker (PDF → Markdown，保留结构)                          │   │
│   │   方案5: Docling (IBM，学术论文好)                                  │   │
│   │                                                                     │   │
│   │   建议: 简单 PDF 用 PyPDF2，复杂 PDF 用 LlamaParse                 │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   HTML 文档:                                                                │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   方案1: BeautifulSoup (灵活，需自定义提取规则)                     │   │
│   │   方案2: Trafilatura (专门提取网页正文)                             │   │
│   │   方案3: Unstructured (通用)                                       │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   Office 文档 (DOCX/PPTX/XLSX):                                            │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   方案: python-docx / python-pptx / openpyxl                       │   │
│   │   或: Unstructured (统一接口)                                      │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### LlamaParse 示例

```python
from llama_parse import LlamaParse

parser = LlamaParse(
    result_type="markdown",  # 输出 Markdown 格式
    language="ch_sim",       # 中文支持
    parsing_instruction="提取所有文本内容，保留表格结构，忽略页眉页脚"
)

documents = parser.load_data("complex_report.pdf")
for doc in documents:
    print(doc.text[:500])
```

---

## 文本分块策略

### 分块策略全景

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    分块策略对比                                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   1. 固定大小分块 (Fixed Size)                                              │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   ████████████|████████████|████████████|████████                   │   │
│   │   ← 512 字符 →← 512 字符 →← 512 字符 →←  剩余  →                 │   │
│   │                                                                     │   │
│   │   优点: 简单，块大小均匀                                            │   │
│   │   缺点: 可能在句子中间切断                                          │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   2. 递归分块 (Recursive) ⭐ 最常用                                         │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   按优先级尝试分隔符: \n\n → \n → 。→ ！→ ？→ 空格                  │   │
│   │   优先按段落分 → 段落太大则按句子分 → 句子太长按字符分              │   │
│   │                                                                     │   │
│   │   优点: 保留语义完整性，通用性好                                    │   │
│   │   缺点: 分块大小不均匀                                              │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   3. 语义分块 (Semantic)                                                    │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   计算相邻句子的 Embedding 相似度，在相似度骤降处断句                │   │
│   │   [句1-句2-句3] | [句4-句5] | [句6-句7-句8-句9] | ...             │   │
│   │                                                                     │   │
│   │   优点: 语义最完整                                                  │   │
│   │   缺点: 需要 Embedding 模型，计算成本高                             │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   4. 文档结构分块 (Document Structure)                                      │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   按 Markdown 标题 / HTML 标签 / 代码函数 拆分                      │   │
│   │   # 标题1 → 块1 | ## 标题2 → 块2 | ### 标题3 → 块3               │   │
│   │                                                                     │   │
│   │   优点: 保留文档逻辑结构                                            │   │
│   │   缺点: 依赖文档格式，不通用                                        │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   5. 滑动窗口 (Sliding Window)                                              │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   ████████████████                                                  │   │
│   │        ████████████████                                             │   │
│   │             ████████████████                                        │   │
│   │   ← chunk_size →                                                    │   │
│   │   ← overlap →                                                       │   │
│   │                                                                     │   │
│   │   优点: 减少边界信息丢失                                            │   │
│   │   缺点: 存储冗余 (通常与其他策略结合使用)                           │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

### 分块策略选择建议

| 文档类型 | 推荐策略 | chunk_size | overlap |
|----------|----------|-----------|---------|
| **通用文档** | 递归分块 | 512-1024 | 64-128 |
| **技术文档** | 按标题结构 | 不限 | 0 |
| **代码文件** | 按函数/类 | 不限 | 0 |
| **法律文本** | 语义分块 | 256-512 | 32-64 |
| **对话记录** | 按对话轮次 | 不限 | 1-2 轮 |

### 分块代码示例

```python
from langchain.text_splitter import (
    RecursiveCharacterTextSplitter,
    MarkdownHeaderTextSplitter,
)
from langchain_experimental.text_splitter import SemanticChunker
from langchain_openai import OpenAIEmbeddings

# 1. 递归分块 (最常用)
recursive_splitter = RecursiveCharacterTextSplitter(
    chunk_size=512,
    chunk_overlap=64,
    separators=["\n\n", "\n", "。", "！", "？", "；", "，", " ", ""],
    length_function=len,
)
chunks = recursive_splitter.split_text(text)

# 2. Markdown 标题分块
md_splitter = MarkdownHeaderTextSplitter(
    headers_to_split_on=[
        ("#", "H1"),
        ("##", "H2"),
        ("###", "H3"),
    ]
)
md_chunks = md_splitter.split_text(markdown_text)
# 每个 chunk 自带标题元数据

# 3. 语义分块
semantic_splitter = SemanticChunker(
    OpenAIEmbeddings(),
    breakpoint_threshold_type="percentile",
    breakpoint_threshold_amount=95  # 相似度骤降 95 百分位处断句
)
semantic_chunks = semantic_splitter.split_text(text)

# 4. Parent-Child 分块 (小块检索，大块返回)
parent_splitter = RecursiveCharacterTextSplitter(chunk_size=2000)
child_splitter = RecursiveCharacterTextSplitter(chunk_size=400)

parent_chunks = parent_splitter.split_text(text)
for parent in parent_chunks:
    children = child_splitter.split_text(parent)
    # 检索时匹配 child，但返回完整 parent
```

---

## Embedding 生成与索引构建

```python
from langchain_openai import OpenAIEmbeddings
from langchain_community.vectorstores import Milvus
from langchain.text_splitter import RecursiveCharacterTextSplitter
from langchain_community.document_loaders import DirectoryLoader, TextLoader
import time

# 1. 加载文档
loader = DirectoryLoader("./knowledge_docs", glob="**/*.md", loader_cls=TextLoader)
documents = loader.load()
print(f"加载了 {len(documents)} 个文档")

# 2. 分块
splitter = RecursiveCharacterTextSplitter(chunk_size=512, chunk_overlap=64)
chunks = splitter.split_documents(documents)
print(f"切分为 {len(chunks)} 个块")

# 3. 添加元数据
for i, chunk in enumerate(chunks):
    chunk.metadata["chunk_id"] = i
    chunk.metadata["indexed_at"] = int(time.time())
    chunk.metadata["char_count"] = len(chunk.page_content)

# 4. 批量向量化 + 存储 (LangChain 自动处理)
embeddings = OpenAIEmbeddings(model="text-embedding-3-large", dimensions=1024)

vectorstore = Milvus.from_documents(
    chunks,
    embeddings,
    connection_args={"host": "localhost", "port": "19530"},
    collection_name="my_knowledge_base",
    index_params={
        "metric_type": "COSINE",
        "index_type": "HNSW",
        "params": {"M": 32, "efConstruction": 256}
    }
)

# 5. 验证
results = vectorstore.similarity_search_with_score("如何构建知识库？", k=3)
for doc, score in results:
    print(f"  [{score:.4f}] {doc.page_content[:80]}...")
```

---

## 端到端 Pipeline 设计

### 生产级 Pipeline

```python
import hashlib
from datetime import datetime
from dataclasses import dataclass

@dataclass
class PipelineConfig:
    """知识库构建 Pipeline 配置"""
    chunk_size: int = 512
    chunk_overlap: int = 64
    embedding_model: str = "BAAI/bge-m3"
    embedding_dim: int = 1024
    collection_name: str = "knowledge_base"
    batch_size: int = 100

class KnowledgeBasePipeline:
    """生产级知识库构建 Pipeline"""
    
    def __init__(self, config: PipelineConfig):
        self.config = config
        self.splitter = RecursiveCharacterTextSplitter(
            chunk_size=config.chunk_size,
            chunk_overlap=config.chunk_overlap
        )
    
    def process_document(self, file_path: str) -> list:
        """处理单个文档"""
        # 1. 加载
        doc = self._load_document(file_path)
        
        # 2. 清洗
        doc = self._clean_text(doc)
        
        # 3. 分块
        chunks = self.splitter.split_text(doc)
        
        # 4. 添加元数据
        processed = []
        for i, chunk in enumerate(chunks):
            processed.append({
                "text": chunk,
                "source": file_path,
                "chunk_index": i,
                "content_hash": hashlib.md5(chunk.encode()).hexdigest(),
                "processed_at": datetime.now().isoformat(),
            })
        
        return processed
    
    def _clean_text(self, text: str) -> str:
        """文本清洗"""
        import re
        # 去除多余空行
        text = re.sub(r'\n{3,}', '\n\n', text)
        # 去除特殊字符
        text = re.sub(r'[\x00-\x08\x0b\x0c\x0e-\x1f]', '', text)
        # 统一空格
        text = re.sub(r'[ \t]+', ' ', text)
        return text.strip()
    
    def _load_document(self, file_path: str) -> str:
        """根据文件类型加载文档"""
        if file_path.endswith('.pdf'):
            from langchain_community.document_loaders import PyPDFLoader
            return "\n".join([p.page_content for p in PyPDFLoader(file_path).load()])
        elif file_path.endswith('.md') or file_path.endswith('.txt'):
            with open(file_path, 'r', encoding='utf-8') as f:
                return f.read()
        else:
            raise ValueError(f"不支持的文件类型: {file_path}")
    
    def build(self, input_dir: str):
        """构建完整知识库"""
        import glob
        
        files = glob.glob(f"{input_dir}/**/*.*", recursive=True)
        all_chunks = []
        
        for f in files:
            try:
                chunks = self.process_document(f)
                all_chunks.extend(chunks)
                print(f"  ✅ {f}: {len(chunks)} chunks")
            except Exception as e:
                print(f"  ❌ {f}: {e}")
        
        print(f"\n总计: {len(all_chunks)} chunks，开始向量化...")
        # ... Embedding + 存储逻辑 ...

# 使用
config = PipelineConfig(chunk_size=512, chunk_overlap=64)
pipeline = KnowledgeBasePipeline(config)
pipeline.build("./docs")
```

---

## 增量更新策略

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    增量更新策略                                               │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│   策略1: 基于文件哈希的变更检测                                             │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   • 记录每个文件的 MD5 哈希                                         │   │
│   │   • 定期扫描，比较哈希                                              │   │
│   │   • 变更文件: 删除旧 chunks → 重新处理 → 插入新 chunks             │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   策略2: 基于时间戳的增量                                                   │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   • 记录上次同步时间                                                │   │
│   │   • 只处理修改时间 > 上次同步时间的文件                             │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
│   策略3: 基于 CDC (Change Data Capture)                                     │
│   ┌─────────────────────────────────────────────────────────────────────┐   │
│   │   • 监听数据库变更事件                                              │   │
│   │   • 实时同步到知识库                                                │   │
│   │   • 适用于数据库作为知识源的场景                                    │   │
│   └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## 质量评估

```python
def evaluate_knowledge_base(vectorstore, test_queries: list, ground_truth: list):
    """评估知识库质量"""
    
    total_recall = 0
    total_precision = 0
    
    for query, expected_sources in zip(test_queries, ground_truth):
        results = vectorstore.similarity_search(query, k=5)
        retrieved_sources = {doc.metadata["source"] for doc in results}
        
        # 召回率
        recall = len(retrieved_sources & set(expected_sources)) / len(expected_sources)
        # 精度
        precision = len(retrieved_sources & set(expected_sources)) / len(retrieved_sources)
        
        total_recall += recall
        total_precision += precision
    
    n = len(test_queries)
    print(f"平均召回率: {total_recall/n:.2%}")
    print(f"平均精度: {total_precision/n:.2%}")
```

---

## 实战练习

### 练习：构建 AI Infra 知识库

```python
# build_ai_infra_kb.py
# 将本项目的 references 目录构建为可检索的知识库

from langchain_community.document_loaders import DirectoryLoader, TextLoader
from langchain.text_splitter import RecursiveCharacterTextSplitter
from langchain_community.vectorstores import Chroma
from langchain_openai import OpenAIEmbeddings

# 1. 加载 AI Infra 文档
loader = DirectoryLoader(
    "skills/ai-infra/references",
    glob="**/*.md",
    loader_cls=TextLoader,
    loader_kwargs={"encoding": "utf-8"}
)
docs = loader.load()
print(f"加载了 {len(docs)} 个文档")

# 2. 分块
splitter = RecursiveCharacterTextSplitter(
    chunk_size=512, chunk_overlap=64,
    separators=["\n## ", "\n### ", "\n\n", "\n", "。", " "]
)
chunks = splitter.split_documents(docs)
print(f"生成 {len(chunks)} 个块")

# 3. 构建知识库
vectorstore = Chroma.from_documents(
    chunks,
    OpenAIEmbeddings(model="text-embedding-3-small"),
    persist_directory="./ai_infra_kb"
)

# 4. 测试检索
test_queries = [
    "ZeRO-3 如何优化显存？",
    "HNSW 索引的工作原理",
    "vLLM 的 PagedAttention",
]

for q in test_queries:
    results = vectorstore.similarity_search(q, k=3)
    print(f"\n查询: {q}")
    for doc in results:
        print(f"  [{doc.metadata['source']}] {doc.page_content[:80]}...")
```

---

*上一篇：[04-向量数据库](04-vector-databases.md)*

*下一篇：[06-RAG 基础](06-rag-fundamentals.md)*

*返回目录：[README](README.md)*
