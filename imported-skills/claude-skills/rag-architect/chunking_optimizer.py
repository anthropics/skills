#!/usr/bin/env python3
"""
Chunking Optimizer - Analyzes document corpus and recommends optimal chunking strategy.

This script analyzes a collection of text/markdown documents and evaluates different
chunking strategies to recommend the optimal approach for the given corpus.

Strategies tested:
- Fixed-size chunking (character and token-based) with overlap
- Sentence-based chunking
- Paragraph-based chunking  
- Semantic chunking (heading-aware)

Metrics measured:
- Chunk size distribution (mean, std, min, max)
- Semantic coherence (topic continuity heuristic)
- Boundary quality (sentence break analysis)

No external dependencies - uses only Python standard library.
"""

import argparse
import json
import os
import re
import statistics
from collections import Counter, defaultdict
from math import log, sqrt
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Any


class DocumentCorpus:
    """Handles loading and preprocessing of document corpus."""
    
    def __init__(self, directory: str, extensions: List[str] = None):
        self.directory = Path(directory)
        self.extensions = extensions or ['.txt', '.md', '.markdown']
        self.documents = []
        self._load_documents()
    
    def _load_documents(self):
        """Load all text documents from directory."""
        if not self.directory.exists():
            raise FileNotFoundError(f"Directory not found: {self.directory}")
        
        for file_path in self.directory.rglob('*'):
            if file_path.is_file() and file_path.suffix.lower() in self.extensions:
                try:
                    with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    if content.strip():  # Only include non-empty files
                        self.documents.append({
                            'path': str(file_path),
                            'content': content,
                            'size': len(content)
                        })
                except Exception as e:
                    print(f"Warning: Could not read {file_path}: {e}")
        
        if not self.documents:
            raise ValueError(f"No valid documents found in {self.directory}")
        
        print(f"Loaded {len(self.documents)} documents totaling {sum(d['size'] for d in self.documents):,} characters")


class ChunkingStrategy:
    """Base class for chunking strategies."""
    
    def __init__(self, name: str, config: Dict[str, Any]):
        self.name = name
        self.config = config
    
    def chunk(self, text: str) -> List[Dict[str, Any]]:
        """Split text into chunks. Returns list of chunk dictionaries."""
        raise NotImplementedError


class FixedSizeChunker(ChunkingStrategy):
    """Fixed-size chunking with optional overlap."""
    
    def __init__(self, chunk_size: int = 1000, overlap: int = 100, unit: str = 'char'):
        config = {'chunk_size': chunk_size, 'overlap': overlap, 'unit': unit}
        super().__init__(f'fixed_size_{unit}', config)
        self.chunk_size = chunk_size
        self.overlap = overlap
        self.unit = unit
    
    def chunk(self, text: str) -> List[Dict[str, Any]]:
        chunks = []
        if self.unit == 'char':
            return self._chunk_by_chars(text)
        else:  # word-based approximation
            words = text.split()
            return self._chunk_by_words(words)
    
    def _chunk_by_chars(self, text: str) -> List[Dict[str, Any]]:
        chunks = []
        start = 0
        chunk_id = 0
        
        while start < len(text):
            end = min(start + self.chunk_size, len(text))
            chunk_text = text[start:end]
            
            chunks.append({
                'id': chunk_id,
                'text': chunk_text,
                'start': start,
                'end': end,
                'size': len(chunk_text)
            })
            
            start = max(start + self.chunk_size - self.overlap, start + 1)
            chunk_id += 1
            
            if start >= len(text):
                break
        
        return chunks
    
    def _chunk_by_words(self, words: List[str]) -> List[Dict[str, Any]]:
        chunks = []
        start = 0
        chunk_id = 0
        
        while start < len(words):
            end = min(start + self.chunk_size, len(words))
            chunk_words = words[start:end]
            chunk_text = ' '.join(chunk_words)
            
            chunks.append({
                'id': chunk_id,
                'text': chunk_text,
                'start': start,
                'end': end,
                'size': len(chunk_text)
            })
            
            start = max(start + self.chunk_size - self.overlap, start + 1)
            chunk_id += 1
            
            if start >= len(words):
                break
        
        return chunks


class SentenceChunker(ChunkingStrategy):
    """Sentence-based chunking."""
    
    def __init__(self, max_size: int = 1000):
        config = {'max_size': max_size}
        super().__init__('sentence_based', config)
        self.max_size = max_size
        # Simple sentence boundary detection
        self.sentence_endings = re.compile(r'[.!?]+\s+')
    
    def chunk(self, text: str) -> List[Dict[str, Any]]:
        # Split into sentences
        sentences = self._split_sentences(text)
        chunks = []
        current_chunk = []
        current_size = 0
        chunk_id = 0
        
        for sentence in sentences:
            sentence_size = len(sentence)
            
            if current_size + sentence_size > self.max_size and current_chunk:
                # Save current chunk
                chunk_text = ' '.join(current_chunk)
                chunks.append({
                    'id': chunk_id,
                    'text': chunk_text,
                    'start': 0,  # Approximate
                    'end': len(chunk_text),
                    'size': len(chunk_text),
                    'sentence_count': len(current_chunk)
                })
                chunk_id += 1
                current_chunk = [sentence]
                current_size = sentence_size
            else:
                current_chunk.append(sentence)
                current_size += sentence_size
        
        # Add final chunk
        if current_chunk:
            chunk_text = ' '.join(current_chunk)
            chunks.append({
                'id': chunk_id,
                'text': chunk_text,
                'start': 0,
                'end': len(chunk_text),
                'size': len(chunk_text),
                'sentence_count': len(current_chunk)
            })
        
        return chunks
    
    def _split_sentences(self, text: str) -> List[str]:
        """Simple sentence splitting."""
        sentences = []
        parts = self.sentence_endings.split(text)
        
        for i, part in enumerate(parts[:-1]):
            # Add the sentence ending back
            ending_match = list(self.sentence_endings.finditer(text))
            if i < len(ending_match):
                sentence = part + ending_match[i].group().strip()
            else:
                sentence = part
            
            if sentence.strip():
                sentences.append(sentence.strip())
        
        # Add final part if it exists
        if parts[-1].strip():
            sentences.append(parts[-1].strip())
        
        return [s for s in sentences if len(s.strip()) > 0]


class ParagraphChunker(ChunkingStrategy):
    """Paragraph-based chunking."""
    
    def __init__(self, max_size: int = 2000, min_paragraph_size: int = 50):
        config = {'max_size': max_size, 'min_paragraph_size': min_paragraph_size}
        super().__init__('paragraph_based', config)
        self.max_size = max_size
        self.min_paragraph_size = min_paragraph_size
    
    def chunk(self, text: str) -> List[Dict[str, Any]]:
        # Split by double newlines (paragraph boundaries)
        paragraphs = [p.strip() for p in re.split(r'\n\s*\n', text) if p.strip()]
        chunks = []
        current_chunk = []
        current_size = 0
        chunk_id = 0
        
        for paragraph in paragraphs:
            paragraph_size = len(paragraph)
            
            # Skip very short paragraphs unless they're the only content
            if paragraph_size < self.min_paragraph_size and len(paragraphs) > 1:
                continue
            
            if current_size + paragraph_size > self.max_size and current_chunk:
                # Save current chunk
                chunk_text = '\n\n'.join(current_chunk)
                chunks.append({
                    'id': chunk_id,
                    'text': chunk_text,
                    'start': 0,
                    'end': len(chunk_text),
                    'size': len(chunk_text),
                    'paragraph_count': len(current_chunk)
                })
                chunk_id += 1
                current_chunk = [paragraph]
                current_size = paragraph_size
            else:
                current_chunk.append(paragraph)
                current_size += paragraph_size + 2  # Account for newlines
        
        # Add final chunk
        if current_chunk:
            chunk_text = '\n\n'.join(current_chunk)
            chunks.append({
                'id': chunk_id,
                'text': chunk_text,
                'start': 0,
                'end': len(chunk_text),
                'size': len(chunk_text),
                'paragraph_count': len(current_chunk)
            })
        
        return chunks


class SemanticChunker(ChunkingStrategy):
    """Heading-aware semantic chunking."""
    
    def __init__(self, max_size: int = 1500, heading_weight: float = 2.0):
        config = {'max_size': max_size, 'heading_weight': heading_weight}
        super().__init__('semantic_heading', config)
        self.max_size = max_size
        self.heading_weight = heading_weight
        
        # Markdown and plain text heading patterns
        self.heading_patterns = [
            re.compile(r'^#{1,6}\s+(.+)$', re.MULTILINE),  # Markdown headers
            re.compile(r'^(.+)\n[=-]+\s*$', re.MULTILINE),  # Underlined headers
            re.compile(r'^\d+\.\s*(.+)$', re.MULTILINE),   # Numbered sections
        ]
    
    def chunk(self, text: str) -> List[Dict[str, Any]]:
        sections = self._identify_sections(text)
        chunks = []
        chunk_id = 0
        
        for section in sections:
            section_chunks = self._chunk_section(section, chunk_id)
            chunks.extend(section_chunks)
            chunk_id += len(section_chunks)
        
        return chunks
    
    def _identify_sections(self, text: str) -> List[Dict[str, Any]]:
        """Identify sections based on headings."""
        sections = []
        lines = text.split('\n')
        current_section = {'heading': 'Introduction', 'content': '', 'level': 0}
        
        for line in lines:
            is_heading = False
            heading_level = 0
            heading_text = line.strip()
            
            # Check for markdown headers
            if line.strip().startswith('#'):
                level = len(line) - len(line.lstrip('#'))
                if level <= 6:
                    heading_text = line.strip('#').strip()
                    heading_level = level
                    is_heading = True
            
            # Check for underlined headers  
            elif len(sections) > 0 and line.strip() and all(c in '=-' for c in line.strip()):
                # Previous line might be heading
                if current_section['content']:
                    content_lines = current_section['content'].strip().split('\n')
                    if content_lines:
                        potential_heading = content_lines[-1].strip()
                        if len(potential_heading) > 0 and len(potential_heading) < 100:
                            # Treat as heading
                            current_section['content'] = '\n'.join(content_lines[:-1])
                            sections.append(current_section)
                            current_section = {
                                'heading': potential_heading,
                                'content': '',
                                'level': 1 if '=' in line else 2
                            }
                            continue
            
            if is_heading:
                if current_section['content'].strip():
                    sections.append(current_section)
                current_section = {
                    'heading': heading_text,
                    'content': '',
                    'level': heading_level
                }
            else:
                current_section['content'] += line + '\n'
        
        # Add final section
        if current_section['content'].strip():
            sections.append(current_section)
        
        return sections
    
    def _chunk_section(self, section: Dict[str, Any], start_id: int) -> List[Dict[str, Any]]:
        """Chunk a single section."""
        content = section['content'].strip()
        if not content:
            return []
        
        heading = section['heading']
        chunks = []
        
        # If section is small enough, return as single chunk
        if len(content) <= self.max_size:
            chunks.append({
                'id': start_id,
                'text': f"{heading}\n\n{content}" if heading else content,
                'start': 0,
                'end': len(content),
                'size': len(content),
                'heading': heading,
                'level': section['level']
            })
            return chunks
        
        # Split large sections by paragraphs
        paragraphs = [p.strip() for p in content.split('\n\n') if p.strip()]
        current_chunk = []
        current_size = len(heading) + 2 if heading else 0  # Account for heading
        chunk_id = start_id
        
        for paragraph in paragraphs:
            paragraph_size = len(paragraph)
            
            if current_size + paragraph_size > self.max_size and current_chunk:
                # Save current chunk
                chunk_text = '\n\n'.join(current_chunk)
                if heading and chunk_id == start_id:
                    chunk_text = f"{heading}\n\n{chunk_text}"
                
                chunks.append({
                    'id': chunk_id,
                    'text': chunk_text,
                    'start': 0,
                    'end': len(chunk_text),
                    'size': len(chunk_text),
                    'heading': heading if chunk_id == start_id else f"{heading} (continued)",
                    'level': section['level']
                })
                chunk_id += 1
                current_chunk = [paragraph]
                current_size = paragraph_size
            else:
                current_chunk.append(paragraph)
                current_size += paragraph_size + 2  # Account for newlines
        
        # Add final chunk
        if current_chunk:
            chunk_text = '\n\n'.join(current_chunk)
            if heading and chunk_id == start_id:
                chunk_text = f"{heading}\n\n{chunk_text}"
            elif heading:
                chunk_text = f"{heading} (continued)\n\n{chunk_text}"
            
            chunks.append({
                'id': chunk_id,
                'text': chunk_text,
                'start': 0,
                'end': len(chunk_text),
                'size': len(chunk_text),
                'heading': heading if chunk_id == start_id else f"{heading} (continued)",
                'level': section['level']
            })
        
        return chunks


class ChunkAnalyzer:
    """Analyzes chunks and provides quality metrics."""
    
    def __init__(self):
        self.vocabulary = set()
        self.word_freq = Counter()
    
    def analyze_chunks(self, chunks: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Comprehensive chunk analysis."""
        if not chunks:
            return {'error': 'No chunks to analyze'}
        
        sizes = [chunk['size'] for chunk in chunks]
        
        # Basic size statistics
        size_stats = {
            'count': len(chunks),
            'mean': statistics.mean(sizes),
            'median': statistics.median(sizes),
            'std': statistics.stdev(sizes) if len(sizes) > 1 else 0,
            'min': min(sizes),
            'max': max(sizes),
            'total': sum(sizes)
        }
        
        # Boundary quality analysis
        boundary_quality = self._analyze_boundary_quality(chunks)
        
        # Semantic coherence (simple heuristic)
        coherence_score = self._calculate_semantic_coherence(chunks)
        
        # Vocabulary distribution
        vocab_stats = self._analyze_vocabulary(chunks)
        
        return {
            'size_statistics': size_stats,
            'boundary_quality': boundary_quality,
            'semantic_coherence': coherence_score,
            'vocabulary_statistics': vocab_stats
        }
    
    def _analyze_boundary_quality(self, chunks: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Analyze how well chunks respect natural boundaries."""
        sentence_breaks = 0
        word_breaks = 0
        total_chunks = len(chunks)
        
        sentence_endings = re.compile(r'[.!?]\s*$')
        
        for chunk in chunks:
            text = chunk['text'].strip()
            if not text:
                continue
            
            # Check if chunk ends with sentence boundary
            if sentence_endings.search(text):
                sentence_breaks += 1
            
            # Check if chunk ends with word boundary
            if text[-1].isalnum() or text[-1] in '.!?':
                word_breaks += 1
        
        return {
            'sentence_boundary_ratio': sentence_breaks / total_chunks if total_chunks > 0 else 0,
            'word_boundary_ratio': word_breaks / total_chunks if total_chunks > 0 else 0,
            'clean_breaks': sentence_breaks,
            'total_chunks': total_chunks
        }
    
    def _calculate_semantic_coherence(self, chunks: List[Dict[str, Any]]) -> float:
        """Simple semantic coherence heuristic based on vocabulary overlap."""
        if len(chunks) < 2:
            return 1.0
        
        coherence_scores = []
        
        for i in range(len(chunks) - 1):
            chunk1_words = set(re.findall(r'\b\w+\b', chunks[i]['text'].lower()))
            chunk2_words = set(re.findall(r'\b\w+\b', chunks[i+1]['text'].lower()))
            
            if not chunk1_words or not chunk2_words:
                continue
            
            # Jaccard similarity as coherence measure
            intersection = len(chunk1_words & chunk2_words)
            union = len(chunk1_words | chunk2_words)
            
            if union > 0:
                coherence_scores.append(intersection / union)
        
        return statistics.mean(coherence_scores) if coherence_scores else 0.0
    
    def _analyze_vocabulary(self, chunks: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Analyze vocabulary distribution across chunks."""
        all_words = []
        chunk_vocab_sizes = []
        
        for chunk in chunks:
            words = re.findall(r'\b\w+\b', chunk['text'].lower())
            all_words.extend(words)
            chunk_vocab_sizes.append(len(set(words)))
        
        total_vocab = len(set(all_words))
        word_freq = Counter(all_words)
        
        return {
            'total_vocabulary': total_vocab,
            'avg_chunk_vocabulary': statistics.mean(chunk_vocab_sizes) if chunk_vocab_sizes else 0,
            'vocabulary_diversity': total_vocab / len(all_words) if all_words else 0,
            'most_common_words': word_freq.most_common(10)
        }


class ChunkingOptimizer:
    """Main optimizer that tests different chunking strategies."""
    
    def __init__(self):
        self.analyzer = ChunkAnalyzer()
    
    def optimize(self, corpus: DocumentCorpus, config: Dict[str, Any] = None) -> Dict[str, Any]:
        """Test all chunking strategies and recommend the best one."""
        config = config or {}
        
        strategies = self._create_strategies(config)
        results = {}
        
        print(f"Testing {len(strategies)} chunking strategies...")
        
        for strategy in strategies:
            print(f"  Testing {strategy.name}...")
            strategy_results = self._test_strategy(corpus, strategy)
            results[strategy.name] = strategy_results
        
        # Recommend best strategy
        recommendation = self._recommend_strategy(results)
        
        return {
            'corpus_info': {
                'document_count': len(corpus.documents),
                'total_size': sum(d['size'] for d in corpus.documents),
                'avg_document_size': statistics.mean([d['size'] for d in corpus.documents])
            },
            'strategy_results': results,
            'recommendation': recommendation,
            'sample_chunks': self._generate_sample_chunks(corpus, recommendation['best_strategy'])
        }
    
    def _create_strategies(self, config: Dict[str, Any]) -> List[ChunkingStrategy]:
        """Create all chunking strategies to test."""
        strategies = []
        
        # Fixed-size strategies
        for size in config.get('fixed_sizes', [512, 1000, 1500]):
            for overlap in config.get('overlaps', [50, 100]):
                strategies.append(FixedSizeChunker(size, overlap, 'char'))
        
        # Sentence-based strategies
        for max_size in config.get('sentence_max_sizes', [800, 1200]):
            strategies.append(SentenceChunker(max_size))
        
        # Paragraph-based strategies
        for max_size in config.get('paragraph_max_sizes', [1500, 2000]):
            strategies.append(ParagraphChunker(max_size))
        
        # Semantic strategies
        for max_size in config.get('semantic_max_sizes', [1200, 1800]):
            strategies.append(SemanticChunker(max_size))
        
        return strategies
    
    def _test_strategy(self, corpus: DocumentCorpus, strategy: ChunkingStrategy) -> Dict[str, Any]:
        """Test a single chunking strategy."""
        all_chunks = []
        document_results = []
        
        for doc in corpus.documents:
            try:
                chunks = strategy.chunk(doc['content'])
                all_chunks.extend(chunks)
                
                doc_analysis = self.analyzer.analyze_chunks(chunks)
                document_results.append({
                    'path': doc['path'],
                    'chunk_count': len(chunks),
                    'analysis': doc_analysis
                })
            except Exception as e:
                print(f"    Error processing {doc['path']}: {e}")
                continue
        
        # Overall analysis
        overall_analysis = self.analyzer.analyze_chunks(all_chunks)
        
        return {
            'strategy_config': strategy.config,
            'total_chunks': len(all_chunks),
            'overall_analysis': overall_analysis,
            'document_results': document_results,
            'performance_score': self._calculate_performance_score(overall_analysis)
        }
    
    def _calculate_performance_score(self, analysis: Dict[str, Any]) -> float:
        """Calculate overall performance score for a strategy."""
        if 'error' in analysis:
            return 0.0
        
        size_stats = analysis['size_statistics']
        boundary_quality = analysis['boundary_quality']
        coherence = analysis['semantic_coherence']
        
        # Normalize metrics to 0-1 range and combine
        size_consistency = 1.0 - min(size_stats['std'] / size_stats['mean'], 1.0) if size_stats['mean'] > 0 else 0
        boundary_score = (boundary_quality['sentence_boundary_ratio'] + boundary_quality['word_boundary_ratio']) / 2
        coherence_score = coherence
        
        # Weighted combination
        return (size_consistency * 0.3 + boundary_score * 0.4 + coherence_score * 0.3)
    
    def _recommend_strategy(self, results: Dict[str, Any]) -> Dict[str, Any]:
        """Recommend the best chunking strategy based on analysis."""
        best_strategy = None
        best_score = 0
        
        strategy_scores = {}
        
        for strategy_name, result in results.items():
            score = result['performance_score']
            strategy_scores[strategy_name] = score
            
            if score > best_score:
                best_score = score
                best_strategy = strategy_name
        
        return {
            'best_strategy': best_strategy,
            'best_score': best_score,
            'all_scores': strategy_scores,
            'reasoning': self._generate_reasoning(best_strategy, results[best_strategy] if best_strategy else None)
        }
    
    def _generate_reasoning(self, strategy_name: str, result: Dict[str, Any]) -> str:
        """Generate human-readable reasoning for the recommendation."""
        if not result:
            return "No valid strategy found."
        
        analysis = result['overall_analysis']
        size_stats = analysis['size_statistics']
        boundary = analysis['boundary_quality']
        
        reasoning = f"Recommended '{strategy_name}' because:\n"
        reasoning += f"- Average chunk size: {size_stats['mean']:.0f} characters\n"
        reasoning += f"- Size consistency: {size_stats['std']:.0f} std deviation\n"
        reasoning += f"- Boundary quality: {boundary['sentence_boundary_ratio']:.2%} clean sentence breaks\n"
        reasoning += f"- Semantic coherence: {analysis['semantic_coherence']:.3f}\n"
        
        return reasoning
    
    def _generate_sample_chunks(self, corpus: DocumentCorpus, strategy_name: str) -> List[Dict[str, Any]]:
        """Generate sample chunks using the recommended strategy."""
        if not strategy_name or not corpus.documents:
            return []
        
        # Create strategy instance
        strategy = None
        if 'fixed_size' in strategy_name:
            strategy = FixedSizeChunker()
        elif 'sentence' in strategy_name:
            strategy = SentenceChunker()
        elif 'paragraph' in strategy_name:
            strategy = ParagraphChunker()
        elif 'semantic' in strategy_name:
            strategy = SemanticChunker()
        
        if not strategy:
            return []
        
        # Get chunks from first document
        sample_doc = corpus.documents[0]
        chunks = strategy.chunk(sample_doc['content'])
        
        # Return first 3 chunks as samples
        return chunks[:3]


def main():
    """Main function with command-line interface."""
    parser = argparse.ArgumentParser(description='Analyze documents and recommend optimal chunking strategy')
    parser.add_argument('directory', help='Directory containing text/markdown documents')
    parser.add_argument('--output', '-o', help='Output file for results (JSON format)')
    parser.add_argument('--config', '-c', help='Configuration file (JSON format)')
    parser.add_argument('--extensions', nargs='+', default=['.txt', '.md', '.markdown'], 
                       help='File extensions to process')
    parser.add_argument('--verbose', '-v', action='store_true', help='Verbose output')
    
    args = parser.parse_args()
    
    # Load configuration
    config = {}
    if args.config and os.path.exists(args.config):
        with open(args.config, 'r') as f:
            config = json.load(f)
    
    try:
        # Load corpus
        print(f"Loading documents from {args.directory}...")
        corpus = DocumentCorpus(args.directory, args.extensions)
        
        # Run optimization
        optimizer = ChunkingOptimizer()
        results = optimizer.optimize(corpus, config)
        
        # Save results
        if args.output:
            with open(args.output, 'w') as f:
                json.dump(results, f, indent=2)
            print(f"Results saved to {args.output}")
        
        # Print summary
        print("\n" + "="*60)
        print("CHUNKING OPTIMIZATION RESULTS")
        print("="*60)
        
        corpus_info = results['corpus_info']
        print(f"Corpus: {corpus_info['document_count']} documents, {corpus_info['total_size']:,} characters")
        
        recommendation = results['recommendation']
        print(f"\nRecommended Strategy: {recommendation['best_strategy']}")
        print(f"Performance Score: {recommendation['best_score']:.3f}")
        print(f"\nReasoning:\n{recommendation['reasoning']}")
        
        if args.verbose:
            print("\nAll Strategy Scores:")
            for strategy, score in recommendation['all_scores'].items():
                print(f"  {strategy}: {score:.3f}")
        
        print("\nSample Chunks:")
        for i, chunk in enumerate(results['sample_chunks'][:2]):
            print(f"\nChunk {i+1} ({chunk['size']} chars):")
            print("-" * 40)
            print(chunk['text'][:200] + "..." if len(chunk['text']) > 200 else chunk['text'])
        
    except Exception as e:
        print(f"Error: {e}")
        return 1
    
    return 0


if __name__ == '__main__':
    exit(main())