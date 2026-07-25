import os
import hashlib
import json
import re
import requests
import time
import threading
from typing import List, Dict, Optional, Any
from agno.tools.duckduckgo import DuckDuckGoTools
from agno.tools.baidusearch import BaiduSearchTools
from datetime import datetime
from .database_manager import DatabaseManager
from .content_extractor import ContentExtractor
from .hybrid_search import LocalNewsSearch

# 默认搜索缓存 TTL（秒），可通过环境变量覆盖
DEFAULT_SEARCH_TTL = int(os.getenv("SEARCH_CACHE_TTL", "3600"))  # 默认 1 小时


class JinaSearchEngine:
    """Jina Search API 封装 - 使用 s.jina.ai 进行网络搜索"""
    
    JINA_SEARCH_URL = "https://s.jina.ai/"
    
    # 速率限制配置
    _rate_limit_no_key = 10  # 无 key 时每分钟最大请求数
    _rate_window = 60.0
    _min_interval = 2.0
    _request_times = []
    _last_request_time = 0.0
    _lock = threading.Lock()
    
    def __init__(self):
        self.api_key = os.getenv("JINA_API_KEY", "").strip()
        self.has_api_key = bool(self.api_key)
        if self.has_api_key:
            logger.info("✅ Jina Search API key configured")
    
    @classmethod
    def _wait_for_rate_limit(cls, has_api_key: bool) -> None:
        """等待以满足速率限制"""
        if has_api_key:
            time.sleep(0.3)
            return
        
        with cls._lock:
            current_time = time.time()
            cls._request_times = [t for t in cls._request_times if current_time - t < cls._rate_window]
            
            if len(cls._request_times) >= cls._rate_limit_no_key:
                oldest = cls._request_times[0]
                wait_time = cls._rate_window - (current_time - oldest) + 1.0
                if wait_time > 0:
                    logger.warning(f"⏳ Jina Search rate limit, waiting {wait_time:.1f}s...")
                    time.sleep(wait_time)
                    current_time = time.time()
                    cls._request_times = [t for t in cls._request_times if current_time - t < cls._rate_window]
            
            time_since_last = current_time - cls._last_request_time
            if time_since_last < cls._min_interval:
                time.sleep(cls._min_interval - time_since_last)
            
            cls._request_times.append(time.time())
            cls._last_request_time = time.time()
    
    def search(self, query: str, max_results: int = 5) -> List[Dict]:
        """
        使用 Jina Search API 执行搜索
        
        Args:
            query: 搜索关键词
            max_results: 返回结果数量
            
        Returns:
            搜索结果列表，每个结果包含 title, url, content
        """
        if not query:
            return []
        
        logger.info(f"🔍 Jina Search: {query}")
        
        # 等待速率限制
        self._wait_for_rate_limit(self.has_api_key)
        
        headers = {
            "Accept": "application/json",
            "X-Retain-Images": "none",
        }
        
        if self.has_api_key:
            headers["Authorization"] = f"Bearer {self.api_key}"
        
        try:
            # Jina Search API: https://s.jina.ai/{query}
            import urllib.parse
            encoded_query = urllib.parse.quote(query)
            url = f"{self.JINA_SEARCH_URL}{encoded_query}"
            
            response = requests.get(url, headers=headers, timeout=30)
            
            if response.status_code == 429:
                logger.warning("⚠️ Jina Search rate limited (429), waiting 30s...")
                time.sleep(30)
                return self.search(query, max_results)
            
            if response.status_code != 200:
                logger.warning(f"Jina Search failed (Status {response.status_code})")
                return []
            
            # 解析响应
            try:
                data = response.json()
            except json.JSONDecodeError:
                # 如果返回纯文本，尝试解析
                data = {"data": [{"title": "Search Result", "url": "", "content": response.text}]}
            
            results = []
            
            # Jina 返回格式可能是 {"data": [...]} 或直接是列表
            items = data.get("data", []) if isinstance(data, dict) else data
            if not isinstance(items, list):
                items = [items] if items else []
            
            for i, item in enumerate(items[:max_results]):
                if isinstance(item, dict):
                    results.append({
                        "title": item.get("title", f"Result {i+1}"),
                        "url": item.get("url", ""),
                        "href": item.get("url", ""),  # 兼容性
                        "content": item.get("content", item.get("description", "")),
                        "body": item.get("content", item.get("description", "")),  # 兼容性
                    })
                elif isinstance(item, str):
                    results.append({
                        "title": f"Result {i+1}",
                        "url": "",
                        "content": item
                    })
            
            logger.info(f"✅ Jina Search returned {len(results)} results")
            return results
            
        except requests.exceptions.Timeout:
            logger.error("Jina Search timeout")
            return []
        except requests.exceptions.RequestException as e:
            logger.error(f"Jina Search request error: {e}")
            return []
        except Exception as e:
            logger.error(f"Jina Search unexpected error: {e}")
            return []

class SearchTools:
    """扩展性搜索工具库 - 支持多引擎聚合与内容缓存"""
    
    def __init__(self, db: DatabaseManager):
        self.db = db
        
        # 检查 Jina API Key 是否配置
        jina_api_key = os.getenv("JINA_API_KEY", "").strip()
        self._jina_enabled = bool(jina_api_key)
        
        self._engines = {
            "ddg": DuckDuckGoTools(),
            "baidu": BaiduSearchTools(),
            "local": LocalNewsSearch(db)
        }
        
        # 如果配置了 Jina API Key，添加 Jina 引擎
        if self._jina_enabled:
            self._engines["jina"] = JinaSearchEngine()
            logger.info("🚀 Jina Search engine enabled (JINA_API_KEY configured)")
        
        # 确定默认搜索引擎
        self._default_engine = "jina" if self._jina_enabled else "ddg"

    def _generate_hash(self, query: str, engine: str, max_results: int) -> str:
        return hashlib.md5(f"{engine}:{query}:{max_results}".encode()).hexdigest()

    def search(self, query: str, engine: str = None, max_results: int = 5, ttl: Optional[int] = None) -> str:
        """
        使用指定搜索引擎执行网络搜索，结果会被缓存以提高效率。
        
        Args:
            query: 搜索关键词，如 "英伟达财报" 或 "光伏行业政策"。
            engine: 搜索引擎选择。可选值: 
                    "jina" (Jina Search，需配置 JINA_API_KEY，LLM友好输出),
                    "ddg" (DuckDuckGo，推荐英文/国际搜索), 
                    "baidu" (百度，推荐中文/国内搜索),
                    "local" (本地历史新闻搜索，基于向量+BM25)。
                    默认: 若配置了 JINA_API_KEY 则使用 "jina"，否则 "ddg"。
            max_results: 期望返回的结果数量，默认 5 条。
            ttl: 缓存有效期（秒）。如果缓存超过此时间会重新搜索。
                 默认使用环境变量 SEARCH_CACHE_TTL 或 3600 秒。
                 设为 0 可强制刷新。
        
        Returns:
            搜索结果的文本描述，包含标题、摘要和链接。
        """
        # 使用默认引擎（如果配置了 Jina 则优先使用 Jina）
        if engine is None:
            engine = self._default_engine
        
        if engine not in self._engines:
            return f"Error: Unsupported engine '{engine}'. Available: {list(self._engines.keys())}"

        query_hash = self._generate_hash(query, engine, max_results)
        effective_ttl = ttl if ttl is not None else DEFAULT_SEARCH_TTL
        
        # 1. 尝试从缓存读取 (local 引擎不缓存，因为它本身就是查库)
        if engine != "local":
            cache = self.db.get_search_cache(query_hash, ttl_seconds=effective_ttl if effective_ttl > 0 else None)
            if cache and effective_ttl != 0:
                logger.info(f"ℹ️ Found search results in cache for: {query} ({engine})")
                return cache['results']

        # 2. 执行真实搜索
        logger.info(f"📡 Searching {engine} for: {query}")
        try:
            tool = self._engines[engine]
            if engine == "jina":
                # Jina Search 返回 List[Dict]
                jina_results = tool.search(query, max_results=max_results)
                results = []
                for r in jina_results:
                    results.append({
                        "title": r.get("title", ""),
                        "href": r.get("url", ""),
                        "body": r.get("content", "")
                    })
            elif engine == "ddg":
                results = tool.duckduckgo_search(query, max_results=max_results)
            elif engine == "baidu":
                results = tool.baidu_search(query, max_results=max_results)
            elif engine == "local":
                # LocalNewsSearch 返回的是 List[Dict]
                local_results = tool.search(query, top_n=max_results)
                results = []
                for r in local_results:
                    results.append({
                        "title": r.get("title"),
                        "href": r.get("url", "local"),
                        "body": r.get("content", "")
                    })
            else:
                results = "Search not implemented for this engine."
            
            results_str = str(results)
            if engine != "local":
                self.db.save_search_cache(query_hash, query, engine, results_str)
            return results_str
            
        except Exception as e:
            # 搜索失败时的降级策略
            if engine == "jina":
                logger.warning(f"⚠️ Jina search failed, falling back to ddg: {query} ({e})")
                try:
                    return self.search(query, engine="ddg", max_results=max_results, ttl=ttl)
                except Exception as e2:
                    logger.error(f"❌ DDG fallback also failed for {query}: {e2}")
            elif engine == "ddg":
                logger.warning(f"⚠️ DDG search failed, falling back to baidu: {query} ({e})")
                try:
                    return self.search(query, engine="baidu", max_results=max_results, ttl=ttl)
                except Exception as e2:
                    logger.error(f"❌ Baidu fallback also failed for {query}: {e2}")

            logger.error(f"❌ Search failed for {query}: {e}")
            return f"Error occurred during search: {str(e)}"

    def search_list(self, query: str, engine: str = None, max_results: int = 5, ttl: Optional[int] = None, enrich: bool = True) -> List[Dict]:
        """
        执行搜索并返回结构化列表 (List[Dict])。
        Dict 包含: title, href (or url), body (or snippet)
        
        Args:
            engine: 搜索引擎，默认使用配置的默认引擎（Jina 优先）
            enrich: 是否抓取正文内容 (默认 True)
        """
        # 使用默认引擎
        if engine is None:
            engine = self._default_engine
            
        if engine not in self._engines:
            logger.error(f"Unsupported engine {engine}")
            return []
            
        # 不同的 hash 以区分是否 enrichment
        enrich_suffix = ":enriched" if enrich else ""
        query_hash = self._generate_hash(query, engine + enrich_suffix, max_results)
        effective_ttl = ttl if ttl is not None else DEFAULT_SEARCH_TTL
        
        # 1. 尝试从缓存读取
        cache = self.db.get_search_cache(query_hash, ttl_seconds=effective_ttl if effective_ttl > 0 else None)
        if cache and effective_ttl != 0:
            try:
                cached_data = json.loads(cache['results'])
                if isinstance(cached_data, list):
                    logger.info(f"ℹ️ Found structured search cache for: {query}")
                    return cached_data
            except:
                pass
        
        # 1.5 Smart Cache (Delegated to Agent)
        # The Agent should call list_similar_searches and judge relevance using PROMPTS.md

        
        # 2. 执行搜索
        logger.info(f"📡 Searching {engine} (structured) for: {query}")
        try:
            tool = self._engines[engine]
            results = []
            if engine == "jina":
                # Jina Search 直接返回结构化数据
                jina_results = tool.search(query, max_results=max_results)
                for r in jina_results:
                    results.append({
                        "title": r.get("title", ""),
                        "url": r.get("url", ""),
                        "href": r.get("url", ""),
                        "body": r.get("content", ""),
                        "content": r.get("content", ""),
                        "source": "Jina Search"
                    })
            elif engine == "ddg":
                results = tool.duckduckgo_search(query, max_results=max_results)
            elif engine == "baidu":
                results = tool.baidu_search(query, max_results=max_results)
            elif engine == "local":
                # LocalNewsSearch 返回的是 List[Dict]
                local_results = tool.search(query, top_n=max_results)
                results = []
                for r in local_results:
                    results.append({
                        "title": r.get("title"),
                        "url": r.get("url", "local"),
                        "body": r.get("content", "")[:500],
                        "source": f"Local ({r.get('source', 'db')})",
                        "publish_time": r.get("publish_time")
                    })
            
            # 处理字符串类型的 JSON 返回 (Baidu 常返 JSON 字符串)
            if isinstance(results, str) and engine not in ["local", "jina"]:
                try:
                    results = json.loads(results)
                except:
                    pass
            
            # 转为统一格式
            normalized_results = []
            if isinstance(results, list):
                
                for i, r in enumerate(results, 1):
                    title = r.get('title', '')
                    url = r.get('href') or r.get('url') or r.get('link', '')
                    content = r.get('body') or r.get('snippet') or r.get('abstract', '')
                    
                    if title and url:
                        normalized_results.append({
                            "id": self._generate_hash(url + query, "search_item", i),
                            "rank": i,
                            "title": title,
                            "url": url,
                            "content": content,
                            "original_snippet": content, # 保留摘要
                            "source": f"Search ({engine})",
                            "publish_time": datetime.now().isoformat(), # 暂用当前时间
                            "crawl_time": datetime.now().isoformat(),
                            "meta_data": {"query": query, "engine": engine}
                        })
            
            # Fallback if still string and failed to parse
            elif isinstance(results, str) and results:
                 normalized_results.append({"title": query, "url": "", "content": results, "source": engine})

            # 3. 抓取正文 & 计算情绪 (Enrichment)
            # 注意：如果使用 Jina Search，内容已经是 LLM 友好格式，可选择跳过 enrichment
            skip_content_enrichment = (engine == "jina")
            
            if enrich and normalized_results:
                logger.info(f"🕸️ Enriching {len(normalized_results)} search results with Jina & Sentiment...")
                extractor = ContentExtractor()
                
                # Lazy load sentiment tool
                if not hasattr(self, 'sentiment_tool') or self.sentiment_tool is None:
                    from .sentiment_tools import SentimentTools
                    self.sentiment_tool = SentimentTools(self.db)
                
                for item in normalized_results:
                    if item.get("url"):
                        try:
                            # 如果是 Jina Search，内容已经足够好，跳过额外抓取
                            if skip_content_enrichment and item.get("content") and len(item.get("content", "")) > 100:
                                full_content = item["content"]
                            else:
                                # Use Jina Reader to get full content
                                full_content = extractor.extract_with_jina(item["url"], timeout=60)
                            
                            if full_content and len(full_content) > 100:
                                item["content"] = full_content
                                
                                # Calculate sentiment
                                # Use title + snippet of content for efficiency
                                text_to_analyze = f"{item['title']} {full_content[:500]}"
                                sent_result = self.sentiment_tool.analyze_sentiment(text_to_analyze)  # Using self.sentiment_tool
                                score = sent_result.get('score', 0.0)
                                item["sentiment_score"] = float(score)
                                
                                logger.info(f"  ✅ Enriched: {item['title'][:20]}... (Sentiment: {score:.2f})")
                            else:
                                # Fallback: Use snippet for sentiment
                                logger.info(f"  ⚠️ Content short/failed for {item['url']}, using snippet for sentiment.")
                                text_to_analyze = f"{item['title']} {item['content']}" # content is snippet here
                                sent_result = self.sentiment_tool.analyze_sentiment(text_to_analyze)
                                score = sent_result.get('score', 0.0)
                                item["sentiment_score"] = float(score)

                        except Exception as e:
                             # Fallback: Use snippet for sentiment on error
                            logger.warning(f"Failed to enrich {item['url']}: {e}. Using snippet.")
                            text_to_analyze = f"{item['title']} {item['content']}"
                            sent_result = self.sentiment_tool.analyze_sentiment(text_to_analyze)
                            score = sent_result.get('score', 0.0)
                            item["sentiment_score"] = float(score)
            
            # 缓存结果 list
            if normalized_results:
                # Pass list directly, DB manager will handle JSON dump for main cache and populate search_details
                # Only cache if NOT from local news reuse (though this logic path is for fresh search)
                self.db.save_search_cache(query_hash, query, engine, normalized_results)
            
            return normalized_results
            
        except Exception as e:
            # 搜索失败时的降级策略
            if engine == "jina":
                logger.warning(f"⚠️ Jina search_list failed, falling back to ddg: {query} ({e})")
                try:
                    return self.search_list(query, engine="ddg", max_results=max_results, ttl=ttl, enrich=enrich)
                except Exception as e2:
                    logger.error(f"❌ DDG fallback (search_list) also failed for {query}: {e2}")
            elif engine == "ddg":
                logger.warning(f"⚠️ DDG search_list failed, falling back to baidu: {query} ({e})")
                try:
                    return self.search_list(query, engine="baidu", max_results=max_results, ttl=ttl, enrich=enrich)
                except Exception as e2:
                    logger.error(f"❌ Baidu fallback (search_list) also failed for {query}: {e2}")

            logger.error(f"❌ Structured search failed for {query}: {e}")
            return []

    def list_similar_queries(self, query: str, limit: int = 5) -> List[Dict]:
        """
        查找与当前查询类似的已缓存查询。
        Agent 可用此方法获取候选缓存，并使用 PROMPTS.md 进行评估以决定是否重用。
        """
        return self.db.find_similar_queries(query, limit=limit)


    def aggregate_search(self, query: str, engines: Optional[List[str]] = None, max_results: int = 5) -> str:
        """
        使用多个搜索引擎同时搜索并聚合结果，获得更全面的信息覆盖。
        
        Args:
            query: 搜索关键词。
            engines: 要使用的搜索引擎列表。可选值: ["ddg", "baidu"]。
                     默认同时使用 ddg 和 baidu。
            max_results: 每个引擎期望返回的结果数量。
        
        Returns:
            聚合后的搜索结果，按引擎分组显示。
        """
        engines = engines or ["ddg", "baidu"]
        aggregated_results = []
        for engine in engines:
            res = self.search(query, engine=engine, max_results=max_results)
            aggregated_results.append(f"--- Results from {engine.upper()} ---\n{res}")
        
        return "\n\n".join(aggregated_results)
