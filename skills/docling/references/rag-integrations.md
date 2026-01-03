# RAG Framework Integrations Guide

This guide covers integrating Docling with popular RAG (Retrieval-Augmented Generation) frameworks.

## Overview

Docling provides native integrations with:

- **LangChain** - Most popular LLM framework
- **LlamaIndex** - Data framework for LLM apps
- **Haystack** - End-to-end NLP framework

Each integration provides document loaders that convert files to framework-native document formats.

## LangChain Integration

### Installation

```bash
pip install langchain-community docling
```

### Basic Usage

```python
from langchain_community.document_loaders import DoclingLoader

# Load single document
loader = DoclingLoader(file_path="document.pdf")
docs = loader.load()

# Each page becomes a Document
for doc in docs:
    print(f"Content: {doc.page_content[:200]}...")
    print(f"Metadata: {doc.metadata}")
```

### Multiple Documents

```python
from langchain_community.document_loaders import DoclingLoader
from pathlib import Path

# Load multiple files
files = list(Path("documents/").glob("*.pdf"))
all_docs = []

for file in files:
    loader = DoclingLoader(file_path=str(file))
    docs = loader.load()
    all_docs.extend(docs)

print(f"Loaded {len(all_docs)} documents")
```

### With Text Splitting

```python
from langchain_community.document_loaders import DoclingLoader
from langchain.text_splitter import RecursiveCharacterTextSplitter

loader = DoclingLoader(file_path="document.pdf")
docs = loader.load()

# Split into chunks
splitter = RecursiveCharacterTextSplitter(
    chunk_size=1000,
    chunk_overlap=200,
    separators=["\n\n", "\n", ". ", " ", ""]
)
chunks = splitter.split_documents(docs)

print(f"Created {len(chunks)} chunks")
```

### Complete RAG Pipeline

```python
from langchain_community.document_loaders import DoclingLoader
from langchain.text_splitter import RecursiveCharacterTextSplitter
from langchain_community.vectorstores import Chroma
from langchain_community.embeddings import HuggingFaceEmbeddings
from langchain_community.llms import Ollama
from langchain.chains import RetrievalQA

# 1. Load document
loader = DoclingLoader(file_path="document.pdf")
docs = loader.load()

# 2. Split into chunks
splitter = RecursiveCharacterTextSplitter(chunk_size=1000, chunk_overlap=200)
chunks = splitter.split_documents(docs)

# 3. Create embeddings and vector store
embeddings = HuggingFaceEmbeddings(model_name="all-MiniLM-L6-v2")
vectorstore = Chroma.from_documents(chunks, embeddings)

# 4. Create retrieval chain
llm = Ollama(model="llama2")
qa_chain = RetrievalQA.from_chain_type(
    llm=llm,
    chain_type="stuff",
    retriever=vectorstore.as_retriever(search_kwargs={"k": 3})
)

# 5. Query
response = qa_chain.invoke({"query": "What is the main topic?"})
print(response["result"])
```

## LlamaIndex Integration

### Installation

```bash
pip install llama-index llama-index-readers-docling docling
```

### Basic Usage

```python
from llama_index.readers.docling import DoclingReader

reader = DoclingReader()
documents = reader.load_data(file_path="document.pdf")

for doc in documents:
    print(f"Content: {doc.text[:200]}...")
    print(f"Metadata: {doc.metadata}")
```

### Building an Index

```python
from llama_index.readers.docling import DoclingReader
from llama_index.core import VectorStoreIndex, Settings
from llama_index.embeddings.huggingface import HuggingFaceEmbedding

# Load documents
reader = DoclingReader()
documents = reader.load_data(file_path="document.pdf")

# Configure embeddings
Settings.embed_model = HuggingFaceEmbedding(model_name="all-MiniLM-L6-v2")

# Build index
index = VectorStoreIndex.from_documents(documents)

# Query
query_engine = index.as_query_engine()
response = query_engine.query("What is the main topic?")
print(response)
```

### With Custom Chunking

```python
from llama_index.readers.docling import DoclingReader
from llama_index.core import VectorStoreIndex
from llama_index.core.node_parser import SentenceSplitter

# Load documents
reader = DoclingReader()
documents = reader.load_data(file_path="document.pdf")

# Custom node parser
parser = SentenceSplitter(chunk_size=1024, chunk_overlap=100)

# Build index with custom parser
index = VectorStoreIndex.from_documents(
    documents,
    transformations=[parser]
)
```

### Multiple File Types

```python
from llama_index.readers.docling import DoclingReader
from pathlib import Path

reader = DoclingReader()

# Load different file types
files = [
    "report.pdf",
    "presentation.pptx",
    "data.xlsx",
    "article.html"
]

all_documents = []
for file in files:
    docs = reader.load_data(file_path=file)
    all_documents.extend(docs)
```

## Haystack Integration

### Installation

```bash
pip install haystack-ai haystack-integrations-docling docling
```

### Basic Usage

```python
from haystack_integrations.components.converters.docling import DoclingConverter

converter = DoclingConverter()
result = converter.run(sources=["document.pdf"])

for doc in result["documents"]:
    print(f"Content: {doc.content[:200]}...")
    print(f"Metadata: {doc.meta}")
```

### Building a Pipeline

```python
from haystack import Pipeline
from haystack.components.writers import DocumentWriter
from haystack.document_stores.in_memory import InMemoryDocumentStore
from haystack_integrations.components.converters.docling import DoclingConverter

# Create document store
document_store = InMemoryDocumentStore()

# Build pipeline
pipeline = Pipeline()
pipeline.add_component("converter", DoclingConverter())
pipeline.add_component("writer", DocumentWriter(document_store=document_store))
pipeline.connect("converter", "writer")

# Run pipeline
pipeline.run({"converter": {"sources": ["document.pdf"]}})

print(f"Stored {document_store.count_documents()} documents")
```

### Complete RAG Pipeline

```python
from haystack import Pipeline
from haystack.components.embedders import SentenceTransformersDocumentEmbedder
from haystack.components.embedders import SentenceTransformersTextEmbedder
from haystack.components.retrievers.in_memory import InMemoryEmbeddingRetriever
from haystack.components.builders import PromptBuilder
from haystack.components.generators import HuggingFaceLocalGenerator
from haystack.document_stores.in_memory import InMemoryDocumentStore
from haystack_integrations.components.converters.docling import DoclingConverter

# Document store
document_store = InMemoryDocumentStore()

# Indexing pipeline
indexing = Pipeline()
indexing.add_component("converter", DoclingConverter())
indexing.add_component("embedder", SentenceTransformersDocumentEmbedder())
indexing.add_component("writer", DocumentWriter(document_store=document_store))
indexing.connect("converter", "embedder")
indexing.connect("embedder", "writer")

# Index documents
indexing.run({"converter": {"sources": ["document.pdf"]}})

# Query pipeline
prompt_template = """
Given the context, answer the question.
Context: {% for doc in documents %}{{ doc.content }}{% endfor %}
Question: {{ question }}
Answer:
"""

query_pipeline = Pipeline()
query_pipeline.add_component("embedder", SentenceTransformersTextEmbedder())
query_pipeline.add_component("retriever", InMemoryEmbeddingRetriever(document_store))
query_pipeline.add_component("prompt", PromptBuilder(template=prompt_template))
query_pipeline.add_component("llm", HuggingFaceLocalGenerator(model="google/flan-t5-base"))

query_pipeline.connect("embedder.embedding", "retriever.query_embedding")
query_pipeline.connect("retriever", "prompt.documents")
query_pipeline.connect("prompt", "llm")

# Query
result = query_pipeline.run({
    "embedder": {"text": "What is the main topic?"},
    "prompt": {"question": "What is the main topic?"}
})
print(result["llm"]["replies"][0])
```

## Vector Store Integration

### Chroma

```python
from langchain_community.vectorstores import Chroma
from langchain_community.embeddings import HuggingFaceEmbeddings

embeddings = HuggingFaceEmbeddings(model_name="all-MiniLM-L6-v2")

# Create from documents
vectorstore = Chroma.from_documents(
    documents=chunks,
    embedding=embeddings,
    persist_directory="./chroma_db"
)

# Query
results = vectorstore.similarity_search("query text", k=5)
```

### Qdrant

```python
from langchain_community.vectorstores import Qdrant
from langchain_community.embeddings import HuggingFaceEmbeddings

embeddings = HuggingFaceEmbeddings(model_name="all-MiniLM-L6-v2")

vectorstore = Qdrant.from_documents(
    documents=chunks,
    embedding=embeddings,
    location=":memory:",  # or URL for remote
    collection_name="documents"
)
```

### Milvus

```python
from langchain_community.vectorstores import Milvus
from langchain_community.embeddings import HuggingFaceEmbeddings

embeddings = HuggingFaceEmbeddings(model_name="all-MiniLM-L6-v2")

vectorstore = Milvus.from_documents(
    documents=chunks,
    embedding=embeddings,
    connection_args={"host": "localhost", "port": "19530"},
    collection_name="documents"
)
```

### Weaviate

```python
from langchain_community.vectorstores import Weaviate
from langchain_community.embeddings import HuggingFaceEmbeddings
import weaviate

client = weaviate.Client(url="http://localhost:8080")
embeddings = HuggingFaceEmbeddings(model_name="all-MiniLM-L6-v2")

vectorstore = Weaviate.from_documents(
    documents=chunks,
    embedding=embeddings,
    client=client,
    index_name="Documents"
)
```

## Chunking Strategies for RAG

### Recommended Chunk Sizes

| Use Case | Chunk Size | Overlap |
|----------|------------|---------|
| Q&A | 500-1000 | 100-200 |
| Summarization | 2000-4000 | 200-400 |
| Code | 1500-2500 | 300-500 |
| Legal/Technical | 1000-1500 | 200-300 |

### Hybrid Chunking

Combine semantic and size-based chunking:

```python
from langchain.text_splitter import RecursiveCharacterTextSplitter

# First pass: semantic boundaries
semantic_splitter = RecursiveCharacterTextSplitter(
    chunk_size=2000,
    chunk_overlap=0,
    separators=["\n\n\n", "\n\n", "\n# ", "\n## "]
)

# Second pass: size-based
size_splitter = RecursiveCharacterTextSplitter(
    chunk_size=500,
    chunk_overlap=100
)

# Apply both
docs = loader.load()
semantic_chunks = semantic_splitter.split_documents(docs)
final_chunks = size_splitter.split_documents(semantic_chunks)
```

## Best Practices

### 1. Preserve Metadata

Always include source information in chunks:

```python
for chunk in chunks:
    chunk.metadata["source"] = file_path
    chunk.metadata["chunk_index"] = i
```

### 2. Handle Tables Separately

Tables often need special treatment:

```python
from docling.document_converter import DocumentConverter

converter = DocumentConverter()
result = converter.convert("document.pdf")
doc = result.document

# Extract tables separately
for table in doc.tables:
    df = table.export_to_dataframe()
    # Index table content differently
```

### 3. Use Appropriate Embeddings

| Embedding Model | Dimensions | Quality | Speed |
|-----------------|------------|---------|-------|
| all-MiniLM-L6-v2 | 384 | Good | Fast |
| all-mpnet-base-v2 | 768 | Better | Medium |
| text-embedding-ada-002 | 1536 | Best | API |

### 4. Test Retrieval Quality

```python
# Test retrieval before deploying
test_queries = [
    "What is the main topic?",
    "What are the key findings?",
    "Who are the authors?"
]

for query in test_queries:
    results = vectorstore.similarity_search(query, k=3)
    print(f"\nQuery: {query}")
    for i, doc in enumerate(results):
        print(f"  {i+1}. {doc.page_content[:100]}...")
```
