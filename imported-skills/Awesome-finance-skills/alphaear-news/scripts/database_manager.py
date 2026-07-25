import sqlite3
import json
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Optional
from loguru import logger

class DatabaseManager:
    """
    AlphaEar News Database Manager
    Reduced version for alphaear-news skill
    """
    
    def __init__(self, db_path: str = "data/signal_flux.db"):
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(self.db_path), check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self._init_db()
        logger.debug(f"💾 Database initialized at {self.db_path}")

    def _init_db(self):
        """Initialize news-related tables only"""
        cursor = self.conn.cursor()
        
        # Daily News Table
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
        
        # Indexes
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_news_crawl_time ON daily_news(crawl_time)")
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_news_source ON daily_news(source)")
        
        self.conn.commit()

    # --- News Operations ---
    
    def save_daily_news(self, news_list: List[Dict]) -> int:
        """Save hot news items"""
        cursor = self.conn.cursor()
        count = 0
        crawl_time = datetime.now().isoformat()
        
        for news in news_list:
            try:
                news_id = news.get('id') or f"{news.get('source')}_{news.get('rank')}_{crawl_time[:10]}"
                cursor.execute("""
                    INSERT OR REPLACE INTO daily_news 
                    (id, source, rank, title, url, content, publish_time, crawl_time, sentiment_score, meta_data)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    news_id,
                    news.get('source'),
                    news.get('rank'),
                    news.get('title'),
                    news.get('url'),
                    news.get('content', ''),
                    news.get('publish_time'),
                    crawl_time,
                    news.get('sentiment_score'),
                    json.dumps(news.get('meta_data', {}))
                ))
                count += 1
            except Exception as e:
                logger.error(f"Error saving news item {news.get('title')}: {e}")
        
        self.conn.commit()
        return count

    def get_daily_news(self, source: Optional[str] = None, limit: int = 100, days: int = 1) -> List[Dict]:
        """Get recent news"""
        cursor = self.conn.cursor()
        time_threshold = (datetime.now().timestamp() - days * 86400)
        time_threshold_str = datetime.fromtimestamp(time_threshold).isoformat()
        
        query = "SELECT * FROM daily_news WHERE crawl_time >= ?"
        params = [time_threshold_str]
        
        if source:
            query += " AND source = ?"
            params.append(source)
            
        query += " ORDER BY crawl_time DESC, rank LIMIT ?"
        params.append(limit)
        
        cursor.execute(query, params)
        return [dict(row) for row in cursor.fetchall()]

    def delete_news(self, news_id: str) -> bool:
        cursor = self.conn.cursor()
        cursor.execute("DELETE FROM daily_news WHERE id = ?", (news_id,))
        self.conn.commit()
        return cursor.rowcount > 0
    
    def update_news_content(self, news_id: str, content: str = None, analysis: str = None) -> bool:
        cursor = self.conn.cursor()
        updates = []
        params = []
        
        if content is not None:
            updates.append("content = ?")
            params.append(content)
        if analysis is not None:
            updates.append("analysis = ?")
            params.append(analysis)
            
        if not updates:
            return False
            
        params.append(news_id)
        query = f"UPDATE daily_news SET {', '.join(updates)} WHERE id = ?"
        cursor.execute(query, params)
        self.conn.commit()
        return cursor.rowcount > 0

    def close(self):
        if self.conn:
            self.conn.close()
