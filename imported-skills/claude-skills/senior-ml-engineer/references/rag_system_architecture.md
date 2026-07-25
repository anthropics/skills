# RAG System Architecture

Retrieval-Augmented Generation patterns for production applications.

---

## Table of Contents

- [RAG Pipeline Architecture](#rag-pipeline-architecture)
- [Vector Database Selection](#vector-database-selection)
- [Chunking Strategies](#chunking-strategies)
- [Embedding Models](#embedding-models)
- [Retrieval Optimization](#retrieval-optimization)

---

## RAG Pipeline Architecture

### Basic RAG Flow

1. Receive user query
2. Generate query embedding
3. Search vector database for relevant chunks
4. Rerank retrieved chunks by relevance
5. Format context with retrieved chunks
6. Send prompt to LLM with context
7. Return generated response
8. **Validation:** Response references retrieved context, no hallucinations

### Pipeline Components

```python
from dataclasses import dataclass
from typing import List

@dataclass
class Document:
    content: str
    metadata: dict
    embedding: List[float] = None

@dataclass
class RetrievalResult:
    document: Document
    score: float

class RAGPipeline:
    def __init__(
        self,
        embedder: Embedder,
        vector_store: VectorStore,
        llm: LLMProvider,
        reranker: Reranker = None
    ):
        self.embedder = embedder
        self.vector_store = vector_store
        self.llm = llm
        self.reranker = reranker

    def query(self, question: str, top_k: int = 5) -> str:
        # 1. Embed query
        query_embedding = self.embedder.embed(question)

        # 2. Retrieve relevant documents
        results = self.vector_store.search(query_embedding, top_k=top_k * 2)

        # 3. Rerank if available
        if self.reranker:
            results = self.reranker.rerank(question, results)[:top_k]
        else:
            results = results[:top_k]

        # 4. Build context
        context = self._build_context(results)

        # 5. Generate response
        prompt = self._build_prompt(question, context)
        return self.llm.complete(prompt)

    def _build_context(self, results: List[RetrievalResult]) -> str:
        return "\n\n".join([
            f"[Source {i+1}]: {r.document.content}"
            for i, r in enumerate(results)
        ])

    def _build_prompt(self, question: str, context: str) -> str:
        return f"""Answer the question based on the context provided.

Context:
{context}

Question: {question}

Answer:"""
```

---

## Vector Database Selection

### Comparison Matrix

| Database | Hosting | Scale | Latency | Cost | Best For |
|----------|---------|-------|---------|------|----------|
| Pinecone | Managed | High | Low | $$ | Production, managed |
| Weaviate | Both | High | Low | $ | Hybrid search |
| Qdrant | Both | High | Very Low | $ | Performance-critical |
| Chroma | Self-hosted | Medium | Low | Free | Prototyping |
| pgvector | Self-hosted | Medium | Medium | Free | Existing Postgres |
| Milvus | Both | Very High | Low | $ | Large-scale |

### Pinecone Integration

```python
import pinecone

class PineconeVectorStore:
    def __init__(self, api_key: str, environment: str, index_name: str):
        pinecone.init(api_key=api_key, environment=environment)
        self.index = pinecone.Index(index_name)

    def upsert(self, documents: List[Document], batch_size: int = 100):
        """Upsert documents in batches."""
        vectors = [
            (doc.metadata["id"], doc.embedding, doc.metadata)
            for doc in documents
        ]

        for i in range(0, len(vectors), batch_size):
            batch = vectors[i:i + batch_size]
            self.index.upsert(vectors=batch)

    def search(self, embedding: List[float], top_k: int = 5) -> List[RetrievalResult]:
        """Search for similar vectors."""
        results = self.index.query(
            vector=embedding,
            top_k=top_k,
            include_metadata=True
        )

        return [
            RetrievalResult(
                document=Document(
                    content=match.metadata.get("content", ""),
                    metadata=match.metadata
                ),
                score=match.score
            )
            for match in results.matches
        ]
```

---

## Chunking Strategies

### Strategy Comparison

| Strategy | Chunk Size | Overlap | Best For |
|----------|------------|---------|----------|
| Fixed | 500-1000 tokens | 50-100 | General text |
| Sentence | 3-5 sentences | 1 sentence | Structured text |
| Paragraph | Natural breaks | None | Documents with clear structure |
| Semantic | Variable | Based on meaning | Research papers |
| Recursive | Hierarchical | Parent-child | Long documents |

### Recursive Character Splitter

```python
from langchain.text_splitter import RecursiveCharacterTextSplitter

def create_chunks(
    text: str,
    chunk_size: int = 1000,
    chunk_overlap: int = 100
) -> List[str]:
    """Split text using recursive character splitting."""
    splitter = RecursiveCharacterTextSplitter(
        chunk_size=chunk_size,
        chunk_overlap=chunk_overlap,
        separators=["\n\n", "\n", ". ", " ", ""]
    )

    return splitter.split_text(text)
```

### Semantic Chunking

```python
from sentence_transformers import SentenceTransformer
import numpy as np

def semantic_chunk(
    sentences: List[str],
    embedder: SentenceTransformer,
    threshold: float = 0.7
) -> List[List[str]]:
    """Group sentences by semantic similarity."""
    embeddings = embedder.encode(sentences)

    chunks = []
    current_chunk = [sentences[0]]
    current_embedding = embeddings[0]

    for i in range(1, len(sentences)):
        similarity = np.dot(current_embedding, embeddings[i]) / (
            np.linalg.norm(current_embedding) * np.linalg.norm(embeddings[i])
        )

        if similarity >= threshold:
            current_chunk.append(sentences[i])
            current_embedding = np.mean(
                [current_embedding, embeddings[i]], axis=0
            )
        else:
            chunks.append(current_chunk)
            current_chunk = [sentences[i]]
            current_embedding = embeddings[i]

    chunks.append(current_chunk)
    return chunks
```

---

## Embedding Models

### Model Comparison

| Model | Dimensions | Quality | Speed | Cost |
|-------|------------|---------|-------|------|
| text-embedding-3-large | 3072 | Excellent | Medium | $0.13/1M |
| text-embedding-3-small | 1536 | Good | Fast | $0.02/1M |
| BGE-large | 1024 | Excellent | Medium | Free |
| all-MiniLM-L6-v2 | 384 | Good | Very Fast | Free |
| Cohere embed-v3 | 1024 | Excellent | Medium | $0.10/1M |

### Embedding with Caching

```python
import hashlib
from functools import lru_cache

class CachedEmbedder:
    def __init__(self, model_name: str = "text-embedding-3-small"):
        self.client = OpenAI()
        self.model = model_name
        self._cache = {}

    def embed(self, text: str) -> List[float]:
        """Embed text with caching."""
        cache_key = hashlib.md5(text.encode()).hexdigest()

        if cache_key in self._cache:
            return self._cache[cache_key]

        response = self.client.embeddings.create(
            model=self.model,
            input=text
        )

        embedding = response.data[0].embedding
        self._cache[cache_key] = embedding

        return embedding

    def embed_batch(self, texts: List[str]) -> List[List[float]]:
        """Embed multiple texts efficiently."""
        response = self.client.embeddings.create(
            model=self.model,
            input=texts
        )

        return [item.embedding for item in response.data]
```

---

## Retrieval Optimization

### Hybrid Search

Combine dense (vector) and sparse (keyword) retrieval:

```python
from rank_bm25 import BM25Okapi

class HybridRetriever:
    def __init__(
        self,
        vector_store: VectorStore,
        documents: List[Document],
        alpha: float = 0.5
    ):
        self.vector_store = vector_store
        self.alpha = alpha  # Weight for vector search

        # Build BM25 index
        tokenized = [doc.content.lower().split() for doc in documents]
        self.bm25 = BM25Okapi(tokenized)
        self.documents = documents

    def search(self, query: str, query_embedding: List[float], top_k: int = 5):
        # Vector search
        vector_results = self.vector_store.search(query_embedding, top_k=top_k * 2)

        # BM25 search
        tokenized_query = query.lower().split()
        bm25_scores = self.bm25.get_scores(tokenized_query)

        # Combine scores
        combined = {}
        for result in vector_results:
            doc_id = result.document.metadata["id"]
            combined[doc_id] = self.alpha * result.score

        for i, score in enumerate(bm25_scores):
            doc_id = self.documents[i].metadata["id"]
            if doc_id in combined:
                combined[doc_id] += (1 - self.alpha) * score
            else:
                combined[doc_id] = (1 - self.alpha) * score

        # Sort and return top_k
        sorted_ids = sorted(combined.keys(), key=lambda x: combined[x], reverse=True)
        return sorted_ids[:top_k]
```

### Reranking

```python
from sentence_transformers import CrossEncoder

class Reranker:
    def __init__(self, model_name: str = "cross-encoder/ms-marco-MiniLM-L-12-v2"):
        self.model = CrossEncoder(model_name)

    def rerank(
        self,
        query: str,
        results: List[RetrievalResult],
        top_k: int = 5
    ) -> List[RetrievalResult]:
        """Rerank results using cross-encoder."""
        pairs = [(query, r.document.content) for r in results]
        scores = self.model.predict(pairs)

        # Update scores and sort
        for i, score in enumerate(scores):
            results[i].score = float(score)

        return sorted(results, key=lambda x: x.score, reverse=True)[:top_k]
```

### Query Expansion

```python
def expand_query(query: str, llm: LLMProvider) -> List[str]:
    """Generate query variations for better retrieval."""
    prompt = f"""Generate 3 alternative phrasings of this question for search.
Return only the questions, one per line.

Original: {query}

Alternatives:"""

    response = llm.complete(prompt, max_tokens=150)
    alternatives = [q.strip() for q in response.strip().split("\n") if q.strip()]

    return [query] + alternatives[:3]
```
