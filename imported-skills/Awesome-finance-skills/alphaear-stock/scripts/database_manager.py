import sqlite3
from pathlib import Path
from typing import List, Dict, Optional
import pandas as pd
from loguru import logger

class DatabaseManager:
    """
    AlphaEar Stock Database Manager
    Reduced version for alphaear-stock skill
    """
    
    def __init__(self, db_path: str = "data/signal_flux.db"):
        self.db_path = Path(db_path)
        self.db_path.parent.mkdir(parents=True, exist_ok=True)
        self.conn = sqlite3.connect(str(self.db_path), check_same_thread=False)
        self.conn.row_factory = sqlite3.Row
        self._init_db()
        logger.debug(f"💾 Stock Database initialized at {self.db_path}")

    def _init_db(self):
        """Initialize stock-related tables"""
        cursor = self.conn.cursor()
        
        # Stock Prices Table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS stock_prices (
                ticker TEXT,
                date TEXT,
                open REAL,
                close REAL,
                high REAL,
                low REAL,
                volume REAL,
                change_pct REAL,
                PRIMARY KEY (ticker, date)
            )
        """)
        
        # Stock List Table
        cursor.execute("""
            CREATE TABLE IF NOT EXISTS stock_list (
                code TEXT PRIMARY KEY,
                name TEXT
            )
        """)
        
        cursor.execute("CREATE INDEX IF NOT EXISTS idx_stock_prices_ticker_date ON stock_prices(ticker, date)")
        self.conn.commit()

    # --- Stock Operations ---

    def save_stock_list(self, df: pd.DataFrame):
        cursor = self.conn.cursor()
        try:
            cursor.execute("DELETE FROM stock_list")
            data = df[['code', 'name']].to_dict('records')
            cursor.executemany(
                "INSERT INTO stock_list (code, name) VALUES (:code, :name)",
                data
            )
            self.conn.commit()
        except Exception as e:
            logger.error(f"Error saving stock list: {e}")

    def search_stock(self, query: str, limit: int = 5) -> List[Dict]:
        cursor = self.conn.cursor()
        wild = f"%{query}%"
        cursor.execute("""
            SELECT code, name FROM stock_list 
            WHERE code LIKE ? OR name LIKE ? 
            LIMIT ?
        """, (wild, wild, limit))
        return [dict(row) for row in cursor.fetchall()]

    def get_stock_by_code(self, code: str) -> Optional[Dict[str, str]]:
        if not code: return None
        clean = "".join([c for c in str(code).strip() if c.isdigit()])
        if not clean: return None

        cursor = self.conn.cursor()
        cursor.execute("SELECT code, name FROM stock_list WHERE code = ? LIMIT 1", (clean,))
        row = cursor.fetchone()
        return dict(row) if row else None

    def save_stock_prices(self, ticker: str, df: pd.DataFrame):
        if df.empty: return
        cursor = self.conn.cursor()
        try:
            for _, row in df.iterrows():
                cursor.execute("""
                    INSERT OR REPLACE INTO stock_prices 
                    (ticker, date, open, close, high, low, volume, change_pct)
                    VALUES (?, ?, ?, ?, ?, ?, ?, ?)
                """, (
                    ticker, row['date'], row['open'], row['close'],
                    row['high'], row['low'], row['volume'], row['change_pct']
                ))
            self.conn.commit()
        except Exception as e:
            logger.error(f"Error saving prices for {ticker}: {e}")

    def get_stock_prices(self, ticker: str, start_date: str, end_date: str) -> pd.DataFrame:
        cursor = self.conn.cursor()
        cursor.execute("""
            SELECT * FROM stock_prices 
            WHERE ticker = ? AND date >= ? AND date <= ?
            ORDER BY date
        """, (ticker, start_date, end_date))
        
        rows = cursor.fetchall()
        if not rows: return pd.DataFrame()
        
        columns = ['ticker', 'date', 'open', 'close', 'high', 'low', 'volume', 'change_pct']
        return pd.DataFrame([dict(row) for row in rows], columns=columns)

    def close(self):
        if self.conn:
            self.conn.close()
