#!/usr/bin/env python3
"""
Retrieval Evaluator - Evaluates retrieval quality using standard IR metrics.

This script evaluates retrieval system performance using standard information retrieval
metrics including precision@k, recall@k, MRR, and NDCG. It uses a built-in TF-IDF
implementation as a baseline retrieval system.

Metrics calculated:
- Precision@K: Fraction of retrieved documents that are relevant
- Recall@K: Fraction of relevant documents that are retrieved  
- Mean Reciprocal Rank (MRR): Average reciprocal rank of first relevant result
- Normalized Discounted Cumulative Gain (NDCG): Ranking quality with position discount

No external dependencies - uses only Python standard library.
"""

import argparse
import json
import math
import os
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Dict, List, Tuple, Set, Any, Optional


class Document:
    """Represents a document in the corpus."""
    
    def __init__(self, doc_id: str, title: str, content: str, path: str = ""):
        self.doc_id = doc_id
        self.title = title
        self.content = content
        self.path = path
        self.tokens = self._tokenize(content)
        self.token_count = len(self.tokens)
    
    def _tokenize(self, text: str) -> List[str]:
        """Simple tokenization - split on whitespace and punctuation."""
        # Convert to lowercase and extract words
        tokens = re.findall(r'\b[a-zA-Z0-9]+\b', text.lower())
        return tokens
    
    def __str__(self):
        return f"Document({self.doc_id}, '{self.title[:50]}...', {self.token_count} tokens)"


class TFIDFRetriever:
    """TF-IDF based retrieval system - no external dependencies."""
    
    def __init__(self, documents: List[Document]):
        self.documents = {doc.doc_id: doc for doc in documents}
        self.doc_ids = list(self.documents.keys())
        self.vocabulary = set()
        self.tf_scores = {}  # doc_id -> {term: tf_score}
        self.df_scores = {}  # term -> document_frequency
        self.idf_scores = {}  # term -> idf_score
        self._build_index()
    
    def _build_index(self):
        """Build TF-IDF index from documents."""
        print(f"Building TF-IDF index for {len(self.documents)} documents...")
        
        # Calculate term frequencies and build vocabulary
        for doc_id, doc in self.documents.items():
            term_counts = Counter(doc.tokens)
            doc_length = len(doc.tokens)
            
            # Calculate TF scores (term_count / doc_length)
            tf_scores = {}
            for term, count in term_counts.items():
                tf_scores[term] = count / doc_length if doc_length > 0 else 0
                self.vocabulary.add(term)
            
            self.tf_scores[doc_id] = tf_scores
        
        # Calculate document frequencies
        for term in self.vocabulary:
            df = sum(1 for doc in self.documents.values() if term in doc.tokens)
            self.df_scores[term] = df
        
        # Calculate IDF scores: log(N / df)
        num_docs = len(self.documents)
        for term, df in self.df_scores.items():
            self.idf_scores[term] = math.log(num_docs / df) if df > 0 else 0
    
    def search(self, query: str, k: int = 10) -> List[Tuple[str, float]]:
        """Search for documents matching the query using TF-IDF similarity."""
        query_tokens = re.findall(r'\b[a-zA-Z0-9]+\b', query.lower())
        if not query_tokens:
            return []
        
        # Calculate query TF scores
        query_tf = Counter(query_tokens)
        query_length = len(query_tokens)
        
        # Calculate TF-IDF similarity for each document
        scores = {}
        for doc_id in self.doc_ids:
            score = self._calculate_similarity(query_tf, query_length, doc_id)
            if score > 0:
                scores[doc_id] = score
        
        # Sort by score and return top k
        sorted_results = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        return sorted_results[:k]
    
    def _calculate_similarity(self, query_tf: Counter, query_length: int, doc_id: str) -> float:
        """Calculate cosine similarity between query and document using TF-IDF."""
        doc_tf = self.tf_scores[doc_id]
        
        # Calculate TF-IDF vectors
        query_vector = []
        doc_vector = []
        
        # Only consider terms that appear in both query and document
        common_terms = set(query_tf.keys()) & set(doc_tf.keys())
        
        if not common_terms:
            return 0.0
        
        for term in common_terms:
            # Query TF-IDF
            q_tf = query_tf[term] / query_length
            q_tfidf = q_tf * self.idf_scores.get(term, 0)
            query_vector.append(q_tfidf)
            
            # Document TF-IDF
            d_tfidf = doc_tf[term] * self.idf_scores.get(term, 0)
            doc_vector.append(d_tfidf)
        
        # Cosine similarity
        dot_product = sum(q * d for q, d in zip(query_vector, doc_vector))
        query_norm = math.sqrt(sum(q * q for q in query_vector))
        doc_norm = math.sqrt(sum(d * d for d in doc_vector))
        
        if query_norm == 0 or doc_norm == 0:
            return 0.0
        
        return dot_product / (query_norm * doc_norm)


class RetrievalEvaluator:
    """Evaluates retrieval system performance using standard IR metrics."""
    
    def __init__(self):
        self.metrics = {}
    
    def evaluate(self, queries: List[Dict[str, Any]], ground_truth: Dict[str, List[str]], 
                 retriever: TFIDFRetriever, k_values: List[int] = None) -> Dict[str, Any]:
        """Evaluate retrieval performance."""
        k_values = k_values or [1, 3, 5, 10]
        
        print(f"Evaluating retrieval performance for {len(queries)} queries...")
        
        query_results = []
        all_precision_at_k = {k: [] for k in k_values}
        all_recall_at_k = {k: [] for k in k_values}
        all_ndcg_at_k = {k: [] for k in k_values}
        reciprocal_ranks = []
        
        for query_data in queries:
            query_id = query_data['id']
            query_text = query_data['query']
            
            # Get ground truth for this query
            relevant_docs = set(ground_truth.get(query_id, []))
            
            if not relevant_docs:
                print(f"Warning: No ground truth found for query {query_id}")
                continue
            
            # Retrieve documents
            max_k = max(k_values)
            results = retriever.search(query_text, max_k)
            retrieved_doc_ids = [doc_id for doc_id, _ in results]
            
            # Calculate metrics for this query
            query_metrics = {}
            
            # Precision@K and Recall@K
            for k in k_values:
                retrieved_at_k = set(retrieved_doc_ids[:k])
                relevant_retrieved = retrieved_at_k & relevant_docs
                
                precision = len(relevant_retrieved) / len(retrieved_at_k) if retrieved_at_k else 0
                recall = len(relevant_retrieved) / len(relevant_docs) if relevant_docs else 0
                
                query_metrics[f'precision@{k}'] = precision
                query_metrics[f'recall@{k}'] = recall
                
                all_precision_at_k[k].append(precision)
                all_recall_at_k[k].append(recall)
            
            # Mean Reciprocal Rank (MRR)
            reciprocal_rank = self._calculate_reciprocal_rank(retrieved_doc_ids, relevant_docs)
            query_metrics['reciprocal_rank'] = reciprocal_rank
            reciprocal_ranks.append(reciprocal_rank)
            
            # NDCG@K
            for k in k_values:
                ndcg = self._calculate_ndcg(retrieved_doc_ids[:k], relevant_docs)
                query_metrics[f'ndcg@{k}'] = ndcg
                all_ndcg_at_k[k].append(ndcg)
            
            # Store query-level results
            query_results.append({
                'query_id': query_id,
                'query': query_text,
                'relevant_count': len(relevant_docs),
                'retrieved_count': len(retrieved_doc_ids),
                'metrics': query_metrics,
                'retrieved_docs': results[:5],  # Top 5 for analysis
                'relevant_docs': list(relevant_docs)
            })
        
        # Calculate aggregate metrics
        aggregate_metrics = {}
        
        for k in k_values:
            aggregate_metrics[f'mean_precision@{k}'] = self._safe_mean(all_precision_at_k[k])
            aggregate_metrics[f'mean_recall@{k}'] = self._safe_mean(all_recall_at_k[k])
            aggregate_metrics[f'mean_ndcg@{k}'] = self._safe_mean(all_ndcg_at_k[k])
        
        aggregate_metrics['mean_reciprocal_rank'] = self._safe_mean(reciprocal_ranks)
        
        # Failure analysis
        failure_analysis = self._analyze_failures(query_results)
        
        return {
            'aggregate_metrics': aggregate_metrics,
            'query_results': query_results,
            'failure_analysis': failure_analysis,
            'evaluation_summary': self._generate_summary(aggregate_metrics, len(queries))
        }
    
    def _calculate_reciprocal_rank(self, retrieved_docs: List[str], relevant_docs: Set[str]) -> float:
        """Calculate reciprocal rank - 1/rank of first relevant document."""
        for i, doc_id in enumerate(retrieved_docs):
            if doc_id in relevant_docs:
                return 1.0 / (i + 1)
        return 0.0
    
    def _calculate_ndcg(self, retrieved_docs: List[str], relevant_docs: Set[str]) -> float:
        """Calculate Normalized Discounted Cumulative Gain."""
        if not retrieved_docs:
            return 0.0
        
        # DCG calculation
        dcg = 0.0
        for i, doc_id in enumerate(retrieved_docs):
            relevance = 1 if doc_id in relevant_docs else 0
            dcg += relevance / math.log2(i + 2)  # +2 because log2(1) = 0
        
        # IDCG calculation (ideal DCG)
        ideal_relevances = [1] * min(len(relevant_docs), len(retrieved_docs))
        idcg = sum(rel / math.log2(i + 2) for i, rel in enumerate(ideal_relevances))
        
        return dcg / idcg if idcg > 0 else 0.0
    
    def _safe_mean(self, values: List[float]) -> float:
        """Calculate mean, handling empty lists."""
        return sum(values) / len(values) if values else 0.0
    
    def _analyze_failures(self, query_results: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Analyze common failure patterns."""
        total_queries = len(query_results)
        
        # Identify queries with poor performance
        poor_precision_queries = []
        poor_recall_queries = []
        zero_results_queries = []
        
        for result in query_results:
            metrics = result['metrics']
            
            if metrics.get('precision@5', 0) < 0.2:
                poor_precision_queries.append(result)
            
            if metrics.get('recall@5', 0) < 0.3:
                poor_recall_queries.append(result)
            
            if result['retrieved_count'] == 0:
                zero_results_queries.append(result)
        
        # Analyze query characteristics
        query_length_analysis = self._analyze_query_lengths(query_results)
        
        return {
            'poor_precision_count': len(poor_precision_queries),
            'poor_recall_count': len(poor_recall_queries),
            'zero_results_count': len(zero_results_queries),
            'poor_precision_examples': poor_precision_queries[:3],
            'poor_recall_examples': poor_recall_queries[:3],
            'query_length_analysis': query_length_analysis,
            'common_failure_patterns': self._identify_failure_patterns(query_results)
        }
    
    def _analyze_query_lengths(self, query_results: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Analyze relationship between query length and performance."""
        short_queries = []  # <= 3 words
        medium_queries = []  # 4-7 words  
        long_queries = []  # >= 8 words
        
        for result in query_results:
            query_length = len(result['query'].split())
            precision = result['metrics'].get('precision@5', 0)
            
            if query_length <= 3:
                short_queries.append(precision)
            elif query_length <= 7:
                medium_queries.append(precision)
            else:
                long_queries.append(precision)
        
        return {
            'short_queries': {
                'count': len(short_queries),
                'avg_precision@5': self._safe_mean(short_queries)
            },
            'medium_queries': {
                'count': len(medium_queries),
                'avg_precision@5': self._safe_mean(medium_queries)
            },
            'long_queries': {
                'count': len(long_queries),
                'avg_precision@5': self._safe_mean(long_queries)
            }
        }
    
    def _identify_failure_patterns(self, query_results: List[Dict[str, Any]]) -> List[str]:
        """Identify common patterns in failed queries."""
        patterns = []
        
        # Check for vocabulary mismatch
        vocab_mismatch_count = 0
        for result in query_results:
            if result['metrics'].get('precision@1', 0) == 0 and result['retrieved_count'] > 0:
                vocab_mismatch_count += 1
        
        if vocab_mismatch_count > len(query_results) * 0.2:
            patterns.append(f"Vocabulary mismatch: {vocab_mismatch_count} queries may have vocabulary mismatch issues")
        
        # Check for specificity issues
        zero_results = sum(1 for r in query_results if r['retrieved_count'] == 0)
        if zero_results > len(query_results) * 0.1:
            patterns.append(f"Query specificity: {zero_results} queries returned no results (may be too specific)")
        
        # Check for recall issues
        low_recall = sum(1 for r in query_results if r['metrics'].get('recall@10', 0) < 0.5)
        if low_recall > len(query_results) * 0.3:
            patterns.append(f"Low recall: {low_recall} queries have recall@10 < 0.5 (missing relevant documents)")
        
        return patterns
    
    def _generate_summary(self, metrics: Dict[str, float], num_queries: int) -> str:
        """Generate human-readable evaluation summary."""
        summary = f"Evaluation Summary ({num_queries} queries):\n"
        summary += f"{'='*50}\n"
        
        # Key metrics
        p1 = metrics.get('mean_precision@1', 0)
        p5 = metrics.get('mean_precision@5', 0)
        r5 = metrics.get('mean_recall@5', 0)
        mrr = metrics.get('mean_reciprocal_rank', 0)
        ndcg5 = metrics.get('mean_ndcg@5', 0)
        
        summary += f"Precision@1:  {p1:.3f} ({p1*100:.1f}%)\n"
        summary += f"Precision@5:  {p5:.3f} ({p5*100:.1f}%)\n"
        summary += f"Recall@5:     {r5:.3f} ({r5*100:.1f}%)\n"
        summary += f"MRR:          {mrr:.3f}\n"
        summary += f"NDCG@5:       {ndcg5:.3f}\n"
        
        # Performance assessment
        summary += f"\nPerformance Assessment:\n"
        if p1 >= 0.7:
            summary += "✓ Excellent precision - most queries return relevant results first\n"
        elif p1 >= 0.5:
            summary += "○ Good precision - many queries return relevant results first\n"
        else:
            summary += "✗ Poor precision - few queries return relevant results first\n"
        
        if r5 >= 0.8:
            summary += "✓ Excellent recall - finding most relevant documents\n"
        elif r5 >= 0.6:
            summary += "○ Good recall - finding many relevant documents\n"
        else:
            summary += "✗ Poor recall - missing many relevant documents\n"
        
        return summary


def load_queries(file_path: str) -> List[Dict[str, Any]]:
    """Load queries from JSON file."""
    with open(file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    # Handle different JSON formats
    if isinstance(data, list):
        return data
    elif 'queries' in data:
        return data['queries']
    else:
        raise ValueError("Invalid query file format. Expected list of queries or {'queries': [...]}.")


def load_ground_truth(file_path: str) -> Dict[str, List[str]]:
    """Load ground truth relevance judgments."""
    with open(file_path, 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    # Handle different JSON formats
    if isinstance(data, dict):
        # Convert all values to lists if they aren't already
        return {k: v if isinstance(v, list) else [v] for k, v in data.items()}
    else:
        raise ValueError("Invalid ground truth format. Expected dict mapping query_id -> relevant_doc_ids.")


def load_corpus(directory: str, extensions: List[str] = None) -> List[Document]:
    """Load document corpus from directory."""
    extensions = extensions or ['.txt', '.md', '.markdown']
    documents = []
    
    corpus_path = Path(directory)
    if not corpus_path.exists():
        raise FileNotFoundError(f"Corpus directory not found: {directory}")
    
    for file_path in corpus_path.rglob('*'):
        if file_path.is_file() and file_path.suffix.lower() in extensions:
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                
                if content.strip():
                    # Use filename (without extension) as doc_id
                    doc_id = file_path.stem
                    title = file_path.name
                    
                    doc = Document(doc_id, title, content, str(file_path))
                    documents.append(doc)
                    
            except Exception as e:
                print(f"Warning: Could not read {file_path}: {e}")
    
    if not documents:
        raise ValueError(f"No valid documents found in {directory}")
    
    print(f"Loaded {len(documents)} documents from corpus")
    return documents


def generate_recommendations(evaluation_results: Dict[str, Any]) -> List[str]:
    """Generate improvement recommendations based on evaluation results."""
    recommendations = []
    
    metrics = evaluation_results['aggregate_metrics']
    failure_analysis = evaluation_results['failure_analysis']
    
    # Precision-based recommendations
    p1 = metrics.get('mean_precision@1', 0)
    p5 = metrics.get('mean_precision@5', 0)
    
    if p1 < 0.3:
        recommendations.append("LOW PRECISION: Consider implementing query expansion or reranking to improve result quality.")
    
    if p5 < 0.4:
        recommendations.append("RANKING ISSUES: Current ranking may not prioritize relevant documents. Consider BM25 or learning-to-rank models.")
    
    # Recall-based recommendations
    r5 = metrics.get('mean_recall@5', 0)
    r10 = metrics.get('mean_recall@10', 0)
    
    if r5 < 0.5:
        recommendations.append("LOW RECALL: Consider query expansion techniques (synonyms, related terms) to find more relevant documents.")
    
    if r10 - r5 > 0.2:
        recommendations.append("RANKING DEPTH: Many relevant documents found in positions 6-10. Consider increasing default result count.")
    
    # MRR-based recommendations
    mrr = metrics.get('mean_reciprocal_rank', 0)
    if mrr < 0.4:
        recommendations.append("POOR RANKING: First relevant result appears late in rankings. Implement result reranking.")
    
    # Failure pattern recommendations
    zero_results = failure_analysis.get('zero_results_count', 0)
    total_queries = len(evaluation_results['query_results'])
    
    if zero_results > total_queries * 0.1:
        recommendations.append("COVERAGE ISSUES: Many queries return no results. Check for vocabulary mismatch or missing content.")
    
    # Query length analysis
    query_analysis = failure_analysis.get('query_length_analysis', {})
    short_perf = query_analysis.get('short_queries', {}).get('avg_precision@5', 0)
    long_perf = query_analysis.get('long_queries', {}).get('avg_precision@5', 0)
    
    if short_perf < 0.3:
        recommendations.append("SHORT QUERY ISSUES: Brief queries perform poorly. Consider query completion or suggestion features.")
    
    if long_perf > short_perf + 0.2:
        recommendations.append("QUERY PROCESSING: Longer queries perform better. Consider query parsing to extract key terms.")
    
    # General recommendations
    if not recommendations:
        recommendations.append("GOOD PERFORMANCE: System performs well overall. Consider A/B testing incremental improvements.")
    
    return recommendations


def main():
    """Main function with command-line interface."""
    parser = argparse.ArgumentParser(description='Evaluate retrieval system performance')
    parser.add_argument('queries', help='JSON file containing queries')
    parser.add_argument('corpus', help='Directory containing document corpus')
    parser.add_argument('ground_truth', help='JSON file containing ground truth relevance judgments')
    parser.add_argument('--output', '-o', help='Output file for results (JSON format)')
    parser.add_argument('--k-values', nargs='+', type=int, default=[1, 3, 5, 10], 
                       help='K values for precision@k, recall@k, NDCG@k evaluation')
    parser.add_argument('--extensions', nargs='+', default=['.txt', '.md', '.markdown'], 
                       help='File extensions to include from corpus')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    try:
        # Load data
        print("Loading evaluation data...")
        queries = load_queries(args.queries)
        ground_truth = load_ground_truth(args.ground_truth)
        documents = load_corpus(args.corpus, args.extensions)
        
        print(f"Loaded {len(queries)} queries, {len(documents)} documents, ground truth for {len(ground_truth)} queries")
        
        # Build retrieval system
        retriever = TFIDFRetriever(documents)
        
        # Run evaluation
        evaluator = RetrievalEvaluator()
        results = evaluator.evaluate(queries, ground_truth, retriever, args.k_values)
        
        # Generate recommendations
        recommendations = generate_recommendations(results)
        results['recommendations'] = recommendations
        
        # Save results
        if args.output:
            with open(args.output, 'w') as f:
                json.dump(results, f, indent=2)
            print(f"Results saved to {args.output}")
        
        # Print summary
        print("\n" + results['evaluation_summary'])
        
        print("\nRecommendations:")
        for i, rec in enumerate(recommendations, 1):
            print(f"{i}. {rec}")
        
        if args.verbose:
            print(f"\nDetailed Metrics:")
            for metric, value in results['aggregate_metrics'].items():
                print(f"  {metric}: {value:.4f}")
            
            print(f"\nFailure Analysis:")
            fa = results['failure_analysis']
            print(f"  Poor precision queries: {fa['poor_precision_count']}")
            print(f"  Poor recall queries: {fa['poor_recall_count']}")
            print(f"  Zero result queries: {fa['zero_results_count']}")
        
    except Exception as e:
        print(f"Error: {e}")
        return 1
    
    return 0


if __name__ == '__main__':
    exit(main())