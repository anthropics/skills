import sqlite3
import json
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Optional, Union
from loguru import logger

class DatabaseManager:
    """
    AlphaEar Search Database Manager
    Reduced version for alphaear-search skill
    """
    
    def __init__(self, db_path: str = "data/signal_flux.db"):
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(self.db_path), check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self._init_db()
        logger.debug(f"💾 Search Database initialized at {self.db_path}")

    def _init_db(self):
        cursor = self.conn.cursor()
        
        # 1. Daily News (Required for Local Search RAG)
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS daily_news (
                id TEXT PRIMARY KEY,
                source TEXT,
                rank INTEGER,
                title TEXT,
                url TEXT,
                content TEXT,
                publish_time TEXT,
                crawl_time TEXT,
                sentiment_score REAL,
                analysis TEXT,
                meta_data TEXT
            )
        """)
        
        # 2. Search Cache
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS search_cache (
                query_hash TEXT PRIMARY KEY,
                query TEXT,
                engine TEXT,
                results TEXT,
                timestamp TEXT
            )
        """)

        # 3. Search Details
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS search_detail (
                id TEXT,
                query_hash TEXT,
                rank INTEGER,
                title TEXT,
                url TEXT,
                content TEXT,
                publish_time TEXT,
                crawl_time TEXT,
                sentiment_score REAL,
                source TEXT,
                meta_data TEXT,
                PRIMARY KEY (query_hash, id)
            )
        """)
        
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_search_cache_timestamp ON search_cache(timestamp)")
        self.conn.commit()

    # --- Search Cache Operations ---
    
    def get_search_cache(self, query_hash: str, ttl_seconds: Optional[int] = None) -> Optional[Dict]:
        cursor = self.conn.cursor()
        
        # Try detailed cache first
        cursor.execute("""
            SELECT * FROM search_detail 
            WHERE query_hash = ? 
            ORDER BY rank
        """, (query_hash,))
        details = [dict(row) for row in cursor.fetchall()]
        
        if details:
            first_time = datetime.fromisoformat(details[0]['crawl_time'])
            if ttl_seconds and (datetime.now() - first_time).total_seconds() > ttl_seconds:
                return None
            return {"results": json.dumps(details), "timestamp": details[0]['crawl_time']}

        # Fallback to simple cache
        cursor.execute("SELECT * FROM search_cache WHERE query_hash = ?", (query_hash,))
        row = cursor.fetchone()
        
        if not row: return None
        row_dict = dict(row)
        if ttl_seconds:
            cache_time = datetime.fromisoformat(row_dict['timestamp'])
            if (datetime.now() - cache_time).total_seconds() > ttl_seconds:
                return None
        return row_dict

    def save_search_cache(self, query_hash: str, query: str, engine: str, results: Union[str, List[Dict]]):
        cursor = self.conn.cursor()
        current_time = datetime.now().isoformat()
        results_str = results if isinstance(results, str) else json.dumps(results)
        
        cursor.execute("""
            INSERT OR REPLACE INTO search_cache (query_hash, query, engine, results, timestamp)
            VALUES (?, ?, ?, ?, ?)
        """, (query_hash, query, engine, results_str, current_time))
        
        if isinstance(results, list):
            for item in results:
                try:
                    item_id = item.get('id') or f"{hash(item.get('url', ''))}"
                    cursor.execute("""
                        INSERT OR REPLACE INTO search_detail
                        (id, query_hash, rank, title, url, content, publish_time, crawl_time, sentiment_score, source, meta_data)
                        VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                    """, (
                        str(item_id), query_hash, item.get('rank', 0), item.get('title'),
                        item.get('url'), item.get('content', ''), item.get('publish_time'),
                        item.get('crawl_time') or current_time, item.get('sentiment_score'),
                        item.get('source'), json.dumps(item.get('meta_data', {}))
                    ))
                except Exception as e:
                    logger.error(f"Error saving search detail: {e}")
                    
        self.conn.commit()

    def find_similar_queries(self, query: str, limit: int = 5) -> List[Dict]:
        cursor = self.conn.cursor()
        q_wild = f"%{query}%"
        cursor.execute("""
            SELECT query, query_hash, timestamp, results 
            FROM search_cache 
            WHERE query LIKE ? OR ? LIKE ('%' || query || '%')
            ORDER BY timestamp DESC
            LIMIT ?
        """, (q_wild, query, limit))
        return [dict(row) for row in cursor.fetchall()]

    def search_local_news(self, query: str, limit: int = 5) -> List[Dict]:
        cursor = self.conn.cursor()
        q_wild = f"%{query}%"
        cursor.execute("""
            SELECT * FROM daily_news
            WHERE title LIKE ? OR content LIKE ?
            ORDER BY crawl_time DESC
            LIMIT ?
        """, (q_wild, q_wild, limit))
        return [dict(row) for row in cursor.fetchall()]

    def close(self):
        if self.conn:
            self.conn.close()
