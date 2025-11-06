#!/usr/bin/env python3
"""
ObjectBox Vector Search Example - RAG Application with Python

This example demonstrates how to build a Retrieval-Augmented Generation (RAG)
application using ObjectBox's vector search capabilities. It includes:
- Document storage with vector embeddings
- Semantic search using cosine similarity
- Context retrieval for LLM queries

Requirements:
    pip install objectbox sentence-transformers
"""

from datetime import datetime
from typing import List, Optional
import numpy as np

try:
    from objectbox import *
    from sentence_transformers import SentenceTransformer
except ImportError as e:
    print(f"Error: {e}")
    print("\nPlease install required packages:")
    print("  pip install objectbox sentence-transformers")
    exit(1)


# ============================================================================
# Entity Definitions
# ============================================================================

@Entity()
class Document:
    """Document entity with text content and vector embedding."""
    id = Id()
    title = String()
    content = String()
    category = String()
    created_at = Date()

    # Vector embedding for semantic search
    # Note: Configure HNSW index via schema or annotations
    embedding = Float32Vector()  # 384 dimensions for all-MiniLM-L6-v2

    def __repr__(self):
        return f"Document(id={self.id}, title='{self.title}', category='{self.category}')"


# ============================================================================
# Document Store with Vector Search
# ============================================================================

class DocumentStore:
    """
    High-level interface for document storage and semantic search using ObjectBox.
    """

    def __init__(self, db_path: str = "vectordb", model_name: str = "all-MiniLM-L6-v2"):
        """
        Initialize document store with ObjectBox and embedding model.

        Args:
            db_path: Path to ObjectBox database directory
            model_name: Sentence-transformers model name
        """
        print(f"Initializing DocumentStore...")
        print(f"  Database: {db_path}")
        print(f"  Embedding model: {model_name}")

        # Initialize ObjectBox
        self.ob = ObjectBox()
        self.ob.open_store(directory=db_path)
        self.box = self.ob.box(Document)

        # Initialize embedding model
        print(f"Loading embedding model (this may take a moment)...")
        self.model = SentenceTransformer(model_name)
        self.embedding_dim = self.model.get_sentence_embedding_dimension()
        print(f"  Embedding dimensions: {self.embedding_dim}")
        print("Initialization complete!\n")

    def add_document(self, title: str, content: str, category: str = "general") -> int:
        """
        Add a document with automatic embedding generation.

        Args:
            title: Document title
            content: Document content
            category: Document category

        Returns:
            Document ID
        """
        # Generate embedding from content
        embedding = self.model.encode(content)

        # Create document
        doc = Document()
        doc.title = title
        doc.content = content
        doc.category = category
        doc.created_at = datetime.now()
        doc.embedding = embedding.tolist()

        # Store in ObjectBox
        doc_id = self.box.put(doc)
        return doc_id

    def add_documents_batch(self, documents: List[dict]) -> List[int]:
        """
        Batch add multiple documents with transaction for performance.

        Args:
            documents: List of dicts with 'title', 'content', and optional 'category'

        Returns:
            List of document IDs
        """
        print(f"Adding {len(documents)} documents in batch...")

        # Generate all embeddings at once (more efficient)
        contents = [doc['content'] for doc in documents]
        embeddings = self.model.encode(contents, show_progress_bar=True)

        # Create document objects
        doc_objects = []
        for i, doc_dict in enumerate(documents):
            doc = Document()
            doc.title = doc_dict['title']
            doc.content = doc_dict['content']
            doc.category = doc_dict.get('category', 'general')
            doc.created_at = datetime.now()
            doc.embedding = embeddings[i].tolist()
            doc_objects.append(doc)

        # Batch insert with transaction (much faster)
        ids = self.box.put_many(doc_objects)
        print(f"Successfully added {len(ids)} documents\n")
        return ids

    def semantic_search(
        self,
        query: str,
        top_k: int = 5,
        category: Optional[str] = None
    ) -> List[tuple]:
        """
        Perform semantic search using vector similarity.

        Args:
            query: Search query text
            top_k: Number of results to return
            category: Optional category filter

        Returns:
            List of (document, score) tuples
        """
        # Generate query embedding
        query_embedding = self.model.encode(query)

        # Build query with vector search
        # Note: Actual API may vary - this is illustrative
        query_builder = self.box.query()

        # Add category filter if specified
        if category:
            query_builder = query_builder.equals(Document.category, category)

        # Perform nearest neighbor search
        # In actual ObjectBox Python API, this would be:
        # query_builder.nearest_neighbors(Document.embedding, query_embedding, top_k)

        # For this example, we'll do manual cosine similarity
        # (Real implementation would use ObjectBox's native vector search)
        all_docs = self.box.get_all()

        results_with_scores = []
        for doc in all_docs:
            if category and doc.category != category:
                continue

            if doc.embedding:
                # Compute cosine similarity
                score = self._cosine_similarity(query_embedding, np.array(doc.embedding))
                results_with_scores.append((doc, score))

        # Sort by score (descending) and return top K
        results_with_scores.sort(key=lambda x: x[1], reverse=True)
        return results_with_scores[:top_k]

    def _cosine_similarity(self, a: np.ndarray, b: np.ndarray) -> float:
        """Compute cosine similarity between two vectors."""
        return np.dot(a, b) / (np.linalg.norm(a) * np.linalg.norm(b))

    def get_all_documents(self) -> List[Document]:
        """Get all documents from the database."""
        return self.box.get_all()

    def get_document_count(self) -> int:
        """Get total number of documents."""
        return self.box.count()

    def close(self):
        """Close the database."""
        self.ob.close()


# ============================================================================
# RAG Application Example
# ============================================================================

def build_context(documents: List[tuple], max_tokens: int = 500) -> str:
    """
    Build context string from retrieved documents for LLM.

    Args:
        documents: List of (document, score) tuples
        max_tokens: Approximate maximum tokens (chars/4)

    Returns:
        Context string
    """
    context_parts = []
    total_chars = 0
    max_chars = max_tokens * 4  # Rough approximation

    for doc, score in documents:
        doc_text = f"[{doc.title}]\n{doc.content}\n"
        if total_chars + len(doc_text) > max_chars:
            break
        context_parts.append(doc_text)
        total_chars += len(doc_text)

    return "\n---\n".join(context_parts)


def rag_query(store: DocumentStore, question: str, top_k: int = 3) -> dict:
    """
    Perform a RAG query: retrieve relevant context and prepare for LLM.

    Args:
        store: DocumentStore instance
        question: User question
        top_k: Number of documents to retrieve

    Returns:
        Dict with question, context, and retrieved documents
    """
    print(f"Question: {question}\n")
    print("Retrieving relevant documents...")

    # Semantic search for relevant documents
    results = store.semantic_search(question, top_k=top_k)

    print(f"Found {len(results)} relevant documents:\n")
    for i, (doc, score) in enumerate(results, 1):
        print(f"{i}. {doc.title} (score: {score:.4f})")
        print(f"   Category: {doc.category}")
        print(f"   Preview: {doc.content[:100]}...")
        print()

    # Build context for LLM
    context = build_context(results)

    return {
        'question': question,
        'context': context,
        'retrieved_docs': [doc for doc, _ in results],
        'scores': [score for _, score in results]
    }


# ============================================================================
# Example Usage
# ============================================================================

def main():
    """Demonstrate ObjectBox vector search for RAG application."""

    print("=" * 70)
    print("ObjectBox Vector Search RAG Example")
    print("=" * 70)
    print()

    # Initialize document store
    store = DocumentStore(db_path="rag_example_db")

    # Sample documents about machine learning
    sample_docs = [
        {
            "title": "Introduction to Neural Networks",
            "content": "Neural networks are computing systems inspired by biological neural networks. "
                      "They consist of interconnected nodes (neurons) organized in layers. Each connection "
                      "has a weight that adjusts during learning. Neural networks excel at pattern recognition "
                      "and are fundamental to deep learning.",
            "category": "ml_basics"
        },
        {
            "title": "Understanding Transformers",
            "content": "Transformers are a type of neural network architecture based on self-attention mechanisms. "
                      "Introduced in 2017, they revolutionized NLP by processing entire sequences simultaneously "
                      "rather than sequentially. Key components include multi-head attention, positional encodings, "
                      "and feed-forward networks. Models like BERT and GPT are built on transformer architecture.",
            "category": "deep_learning"
        },
        {
            "title": "Vector Databases Explained",
            "content": "Vector databases store and query high-dimensional vector embeddings efficiently. "
                      "They use algorithms like HNSW (Hierarchical Navigable Small Worlds) for fast approximate "
                      "nearest neighbor search. Essential for semantic search, recommendation systems, and RAG "
                      "applications. ObjectBox provides on-device vector database capabilities.",
            "category": "databases"
        },
        {
            "title": "What is RAG?",
            "content": "Retrieval-Augmented Generation (RAG) combines information retrieval with text generation. "
                      "First, relevant documents are retrieved using semantic search. Then, these documents provide "
                      "context to a language model for generating accurate, grounded responses. RAG reduces hallucinations "
                      "and enables LLMs to access external knowledge.",
            "category": "ml_applications"
        },
        {
            "title": "Embeddings in NLP",
            "content": "Embeddings represent text as dense vectors in high-dimensional space. Words or sentences "
                      "with similar meanings have similar vector representations. Modern embedding models like "
                      "sentence-transformers capture semantic meaning effectively. These embeddings enable semantic "
                      "search, clustering, and similarity comparison.",
            "category": "nlp"
        }
    ]

    # Add documents if database is empty
    if store.get_document_count() == 0:
        print("Populating database with sample documents...\n")
        store.add_documents_batch(sample_docs)
    else:
        print(f"Database already contains {store.get_document_count()} documents\n")

    print("-" * 70)
    print("EXAMPLE 1: Basic Semantic Search")
    print("-" * 70)
    print()

    # Example 1: Semantic search
    query1 = "How do attention mechanisms work?"
    results1 = store.semantic_search(query1, top_k=2)

    print(f"Query: '{query1}'\n")
    print("Top results:")
    for i, (doc, score) in enumerate(results1, 1):
        print(f"\n{i}. {doc.title} (similarity: {score:.4f})")
        print(f"   {doc.content[:150]}...")

    print("\n")
    print("-" * 70)
    print("EXAMPLE 2: RAG Query")
    print("-" * 70)
    print()

    # Example 2: RAG query
    question = "What are the benefits of using vector databases for AI applications?"
    rag_result = rag_query(store, question, top_k=3)

    print("\n" + "=" * 70)
    print("Context prepared for LLM:")
    print("=" * 70)
    print(rag_result['context'][:500] + "...")
    print()

    print("-" * 70)
    print("EXAMPLE 3: Category-Filtered Search")
    print("-" * 70)
    print()

    # Example 3: Filtered search
    query3 = "machine learning concepts"
    results3 = store.semantic_search(query3, top_k=3, category="ml_basics")

    print(f"Query: '{query3}' (filtered by category='ml_basics')\n")
    print("Results:")
    for i, (doc, score) in enumerate(results3, 1):
        print(f"\n{i}. {doc.title}")
        print(f"   Category: {doc.category}")
        print(f"   Similarity: {score:.4f}")

    print("\n")
    print("=" * 70)
    print(f"Example complete! Database contains {store.get_document_count()} documents.")
    print("=" * 70)

    # Cleanup
    store.close()


if __name__ == "__main__":
    main()
