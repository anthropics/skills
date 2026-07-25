import numpy as np
import os
from typing import List, Dict, Any, Optional, Union
from rank_bm25 import BM25Okapi
from loguru import logger
from sentence_transformers import SentenceTransformer
from sklearn.metrics.pairwise import cosine_similarity

class HybridSearcher:
    """
    统一混合检索引擎 (Hybrid RAG)
    实现 BM25 (文本) + 向量 (语义) 的融合搜索 (RRF)
    """
    
    def __init__(self, data: List[Dict[str, Any]], text_fields: List[str] = ["title", "content"], model_name: str = None):
        """
        初始化搜索器
        
        Args:
            data: 数据列表，每个元素为 Dict
            text_fields: 用于建立索引的文本字段
            model_name: 向量模型名称，默认使用 paraphrase-multilingual-MiniLM-L12-v2
        """
        self.data = data
        self.text_fields = text_fields
        self._corpus = []
        self._bm25 = None
        self._vector_model = None
        self._embeddings = None
        self._fitted = False
        self._vector_fitted = False
        
        # 默认模型
        self.model_name = model_name or os.getenv("EMBEDDING_MODEL", "paraphrase-multilingual-MiniLM-L12-v2")
        
        if data:
            self._prepare_corpus()
            self._fit_bm25()
            # 延迟加载向量模型，仅在需要时或初始化时显式调用
            # self._fit_vector() 

    def _prepare_corpus(self):
        """准备语料库用于分词"""
        import jieba  # 使用 jieba 进行中文分词
        
        self._corpus = []
        self._full_texts = []
        for item in self.data:
            text = " ".join([str(item.get(field, "")) for field in self.text_fields])
            self._full_texts.append(text)
            # 中文分词优化
            tokens = list(jieba.cut(text))
            self._corpus.append(tokens)

    def _fit_bm25(self):
        """训练 BM25 模型"""
        if self._corpus:
            self._bm25 = BM25Okapi(self._corpus)
            self._fitted = True
            logger.info(f"✅ BM25 index fitted with {len(self.data)} documents")

    def _fit_vector(self):
        """训练向量模型并生成 Embeddings"""
        if not self.data:
            return
            
        try:
            logger.info(f"📡 Loading embedding model: {self.model_name}...")
            self._vector_model = SentenceTransformer(self.model_name)
            logger.info(f"🧠 Encoding {len(self._full_texts)} documents...")
            self._embeddings = self._vector_model.encode(self._full_texts, show_progress_bar=False)
            self._vector_fitted = True
            logger.info("✅ Vector index fitted successfully")
        except Exception as e:
            logger.error(f"❌ Failed to fit vector index: {e}")
            self._vector_fitted = False

    def _compute_rrf(self, rank_lists: List[List[int]], k: int = 60) -> List[tuple]:
        """
        计算 Reciprocal Rank Fusion (RRF)
        
        Args:
            rank_lists: 多个排序后的索引列表
            k: RRF 常数，默认 60
        """
        scores = {}
        for rank_list in rank_lists:
            for rank, idx in enumerate(rank_list):
                if idx not in scores:
                    scores[idx] = 0
                scores[idx] += 1.0 / (k + rank + 1)
        
        # 按分数排序
        sorted_indices = sorted(scores.items(), key=lambda x: x[1], reverse=True)
        return sorted_indices

    def search(self, query: str, top_n: int = 5, use_vector: bool = False) -> List[Dict[str, Any]]:
        """
        执行混合搜索
        
        Args:
            query: 搜索关键词
            top_n: 返回结果数量
            use_vector: 是否启用向量搜索
        """
        if not self._fitted or not query:
            return []
        
        import jieba
        query_tokens = list(jieba.cut(query))
        
        # 1. BM25 搜索结果
        bm25_scores = self._bm25.get_scores(query_tokens)
        bm25_rank = np.argsort(bm25_scores)[::-1].tolist()
        
        rank_lists = [bm25_rank]
        
        # 2. 向量搜索逻辑
        if use_vector:
            if not self._vector_fitted:
                self._fit_vector()
            
            if self._vector_fitted:
                query_embedding = self._vector_model.encode([query], show_progress_bar=False)
                similarities = cosine_similarity(query_embedding, self._embeddings)[0]
                vector_rank = np.argsort(similarities)[::-1].tolist()
                rank_lists.append(vector_rank)
            else:
                logger.warning("Vector search requested but model not fitted, falling back to BM25")
        
        # 3. 融合排序 (RRF)
        if len(rank_lists) > 1:
            rrf_results = self._compute_rrf(rank_lists)
            # RRF 返回 (idx, score) 列表
            final_rank = [idx for idx, score in rrf_results]
        else:
            final_rank = bm25_rank
        
        # 返回前 top_n 条结果
        results = [self.data[idx].copy() for idx in final_rank[:top_n]]
        
        # 为每个结果注入相关性评分
        for i, res in enumerate(results):
            try:
                original_idx = final_rank[i]
                res["_search_score"] = bm25_scores[original_idx]
                if use_vector and self._vector_fitted:
                    res["_vector_score"] = float(similarities[original_idx])
            except:
                res["_search_score"] = 0
            
        return results

class InMemoryRAG(HybridSearcher):
    """专门用于 ReportAgent 跨章节检索的内存态 RAG"""
    
    def search(self, query: str, top_n: int = 3, use_vector: bool = True) -> List[Dict[str, Any]]:
        """默认开启向量搜索的内存检索"""
        return super().search(query, top_n=top_n, use_vector=use_vector)

    def update_data(self, new_data: List[Dict[str, Any]]):
        """动态更新数据并重新训练索引"""
        self.data = new_data
        self._prepare_corpus()
        self._fit_bm25()
        # 如果之前已经加载过向量模型，则更新向量索引
        if self._vector_model:
            self._fit_vector()
        logger.info(f"🔄 InMemoryRAG updated with {len(new_data)} items")

class LocalNewsSearch(HybridSearcher):
    """持久态 RAG：检索数据库中的历史新闻"""
    
    def __init__(self, db_manager):
        """
        Args:
            db_manager: DatabaseManager 实例
        """
        self.db = db_manager
        # 初始时不加载数据，需调用 load_history
        super().__init__([], ["title", "content"])
    
    def load_history(self, days: int = 30, limit: int = 1000):
        """从数据库加载最近 N 天的新闻构建索引"""
        try:
            # 假设 db_manager 有 execute_query
            query = f"SELECT title, content, publish_time, source FROM daily_news ORDER BY publish_time DESC LIMIT ?"
            results = self.db.execute_query(query, (limit,))
            
            data = []
            for row in results:
                # 转换 Row 为 Dict
                if hasattr(row, 'keys'):
                    item = dict(row)
                else:
                    item = {
                        "title": row[0], 
                        "content": row[1], 
                        "publish_time": row[2],
                        "source": row[3]
                    }
                data.append(item)
            
            self.data = data
            self._prepare_corpus()
            self._fit_bm25()
            # 默认不立即训练向量，等到第一次搜索时按需训练
            logger.info(f"📚 LocalNewsSearch loaded {len(data)} items from history")
        except Exception as e:
            logger.error(f"Failed to load history for search: {e}")

    def search(self, query: str, top_n: int = 5, use_vector: bool = True) -> List[Dict[str, Any]]:
        """执行本地历史搜索，默认开启向量搜索"""
        if not self.data:
            self.load_history()
        return super().search(query, top_n=top_n, use_vector=use_vector)
