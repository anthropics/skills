from datetime import datetime, timedelta
from typing import List, Dict, Optional
import akshare as ak
import yfinance as yf
import pandas as pd
import re
import sqlite3
import requests as _requests
from requests.exceptions import RequestException
from loguru import logger
from .database_manager import DatabaseManager
import os
from contextlib import contextmanager

class EastMoneyDirect:
    """东方财富 HTTP 直接调用 —— 作为 akshare 的零依赖降级方案。
    
    仅使用 requests，无需 API Key，国内网络直连。
    """
    
    KLINE_URL = "https://push2his.eastmoney.com/api/qt/stock/kline/get"
    LIST_URL = "https://push2.eastmoney.com/api/qt/clist/get"
    UT = "fa5fd1943c7b386f172d6893dbfba10b"

    @staticmethod
    def _secid(ticker: str) -> str:
        """将纯数字 ticker 转为东方财富 secid 格式。
        
        A股: 6开头 -> 1.{ticker}(上交所) | 其他 -> 0.{ticker}(深交所)
        港股: 5位数字 -> 116.{ticker}
        """
        if len(ticker) == 5:
            return f"116.{ticker}"
        if ticker.startswith(('6', '9')):
            return f"1.{ticker}"
        return f"0.{ticker}"

    @classmethod
    def fetch_kline(cls, ticker: str, start_date: str, end_date: str) -> pd.DataFrame:
        """获取 K 线数据，返回与 akshare 对齐的 DataFrame。
        
        Args:
            ticker: 纯数字股票代码
            start_date: YYYYMMDD
            end_date: YYYYMMDD
        """
        params = {
            'secid': cls._secid(ticker),
            'fields1': 'f1,f2,f3,f4,f5,f6',
            'fields2': 'f51,f52,f53,f54,f55,f56,f57,f58,f59,f60,f61',
            'klt': '101',   # 日K
            'fqt': '1',     # 前复权
            'beg': start_date,
            'end': end_date,
            'lmt': '1000',
            'ut': cls.UT,
        }
        resp = _requests.get(cls.KLINE_URL, params=params, timeout=10)
        resp.raise_for_status()
        data = resp.json().get('data')
        if not data or not data.get('klines'):
            return pd.DataFrame()
        
        # kline 格式: "日期,开盘,收盘,最高,最低,成交量,成交额,振幅,涨跌幅,涨跌额,换手率"
        rows = [k.split(',') for k in data['klines']]
        df = pd.DataFrame(rows, columns=[
            '日期', '开盘', '收盘', '最高', '最低', '成交量',
            '成交额', '振幅', '涨跌幅', '涨跌额', '换手率'
        ])
        # 转为数值类型
        for col in ['开盘', '收盘', '最高', '最低', '成交量', '涨跌幅']:
            df[col] = pd.to_numeric(df[col], errors='coerce')
        
        return df

    @classmethod
    def fetch_stock_list(cls, market: str = 'a') -> pd.DataFrame:
        """获取股票列表。
        
        Args:
            market: 'a' for A股, 'hk' for 港股
        """
        if market == 'a':
            fs = 'm:0+t:6,m:0+t:80,m:1+t:2,m:1+t:23'
        else:
            fs = 'm:128+t:3,m:128+t:4,m:128+t:1,m:128+t:2'
        
        all_items = []
        page = 1
        while True:
            params = {
                'pn': str(page), 'pz': '5000', 'po': '1', 'np': '1',
                'fltt': '2', 'invt': '2', 'fid': 'f12',
                'fs': fs, 'fields': 'f12,f14',
                'ut': cls.UT,
            }
            resp = _requests.get(cls.LIST_URL, params=params, timeout=15)
            resp.raise_for_status()
            data = resp.json().get('data', {})
            diff = data.get('diff', [])
            if not diff:
                break
            for item in diff:
                all_items.append({'code': item.get('f12', ''), 'name': item.get('f14', '')})
            total = data.get('total', 0)
            if page * 5000 >= total:
                break
            page += 1
        
        return pd.DataFrame(all_items)


@contextmanager
def temporary_no_proxy():
    """Context manager to temporarily unset proxy environment variables."""
    proxies = {k: os.environ.get(k) for k in ['http_proxy', 'https_proxy', 'HTTP_PROXY', 'HTTPS_PROXY']}
    for k in proxies:
        if k in os.environ:
            del os.environ[k]
    try:
        yield
    finally:
        for k, v in proxies.items():
            if v is not None:
                os.environ[k] = v

class StockTools:
    """金融分析股票工具 - 结合高性能数据库缓存与增量更新，支持获取实时行情及公司基本面"""
    
    def __init__(self, db: DatabaseManager, auto_update: bool = True):
        """
        初始化股票工具
        
        Args:
            db: 数据库管理器
            auto_update: 是否在列表为空时自动更新，默认 True
        """
        self.db = db
        if auto_update:
            self._check_and_update_stock_list()

    def _check_and_update_stock_list(self, force: bool = False):
        """检查并更新股票列表。仅在列表为空或 force=True 时从网络拉取。"""
        # 直接查询表中记录数
        cursor = self.db.conn.cursor()
        cursor.execute("SELECT COUNT(*) FROM stock_list")
        count = cursor.fetchone()[0]
        
        if count > 0 and not force:
            logger.info(f"ℹ️ Stock list already cached ({count} stocks)")
            return
        
        logger.info("📡 Updating A-share and HK-share stock list...")
        
        df_combined = None
        
        # === 主路径: akshare ===
        try:
            def fetch_data_ak():
                df_a = ak.stock_zh_a_spot_em()
                df_a = df_a[['代码', '名称']].copy()
                df_a.columns = ['code', 'name']
                
                df_hk = ak.stock_hk_spot_em()
                df_hk = df_hk[['代码', '名称']].copy()
                df_hk.columns = ['code', 'name']
                
                return pd.concat([df_a, df_hk], ignore_index=True)

            try:
                df_combined = fetch_data_ak()
            except (RequestException, Exception) as e:
                if "Proxy" in str(e) or "proxy" in str(e):
                    logger.warning(f"⚠️ Proxy error detected: {e}. Retrying with proxy disabled...")
                    with temporary_no_proxy():
                        df_combined = fetch_data_ak()
                else:
                    raise e
            logger.info(f"✅ akshare: fetched {len(df_combined)} stocks.")
        except Exception as e:
            logger.warning(f"⚠️ akshare stock list failed: {e}. Trying EastMoney direct...")
        
        # === 降级路径: 东方财富直接 HTTP ===
        if df_combined is None or df_combined.empty:
            try:
                df_a = EastMoneyDirect.fetch_stock_list('a')
                df_hk = EastMoneyDirect.fetch_stock_list('hk')
                df_combined = pd.concat([df_a, df_hk], ignore_index=True)
                logger.info(f"✅ EastMoney direct: fetched {len(df_combined)} stocks.")
            except Exception as e2:
                logger.error(f"❌ All stock list sources failed. akshare + EastMoney: {e2}")
                return
        
        if df_combined is not None and not df_combined.empty:
            self.db.save_stock_list(df_combined)
            logger.info(f"✅ Cached {len(df_combined)} stocks to database.")


    def search_ticker(self, query: str, limit: int = 5) -> List[Dict]:
        """
        模糊搜索 A 股股票代码或名称，支持常见缩写。
        """
        # 清洗后缀 (如 CATL.SZ -> CATL, 000001.SZ -> 000001)
        clean_query = re.sub(r'\.(SZ|SH|HK|US)$', '', query, flags=re.IGNORECASE)
        
        # 常见缩写映射
        aliases = {
            "CATL": "宁德时代",
            "BYD": "比亚迪",
            "TSLA": "特斯拉",
            "Moutai": "贵州茅台",
            "Tencent": "腾讯",
            "Alibaba": "阿里巴巴",
            "Meituan": "美团",
        }
        
        search_query = aliases.get(clean_query.upper(), clean_query)
        
        # Robustness: if regex-like ticker code is embedded in query (e.g. "300364 中文在线"), try to extract it
        if not search_query.isdigit():
             # Extract explicit 5-6 digit codes
             match = re.search(r'\b(\d{5,6})\b', clean_query)
             if match:
                 search_query = match.group(1)

        res = self.db.search_stock(search_query, limit)
        if not res and search_query.isalpha():
            # Robustness: mock search hit for alphabetic US tickers
            return [{"code": search_query.upper(), "name": search_query.upper()}]
        return res

    def get_stock_price(
        self,
        ticker: str,
        start_date: Optional[str] = None,
        end_date: Optional[str] = None,
        force_sync: bool = False,
    ) -> pd.DataFrame:
        """
        获取指定股票的历史价格数据。优先从本地缓存读取，缺失时自动从网络补齐。
        
        Args:
            ticker: 股票代码，如 "600519"（贵州茅台）或 "000001"（平安银行）。
            start_date: 开始日期，格式 "YYYY-MM-DD"。默认为 90 天前。
            end_date: 结束日期，格式 "YYYY-MM-DD"。默认为今天。
        
        Returns:
            包含 date, open, close, high, low, volume, change_pct 列的 DataFrame。
        """
        now = datetime.now()
        if not end_date:
            end_date = now.strftime('%Y-%m-%d')
        if not start_date:
            start_date = (now - timedelta(days=90)).strftime('%Y-%m-%d')

        df_db = self.db.get_stock_prices(ticker, start_date, end_date)
        
        need_update = False
        if df_db.empty:
            need_update = True
        else:
            db_latest = pd.to_datetime(df_db['date'].max())
            req_latest = pd.to_datetime(end_date)
            if (req_latest - db_latest).days > 2:
                need_update = True

        if force_sync:
            need_update = True

        if need_update:
            logger.info(f"📡 Data stale or missing for {ticker}, syncing from network...")
            
            is_us_stock = bool(re.search(r'[a-zA-Z]', ticker)) and not bool(re.search(r'\d{5,6}', ticker))
            
            if is_us_stock:
                clean_ticker = ticker.upper()
            else:
                # 清洗 ticker，确保只包含数字（Akshare A 股接口通常只需要数字代码）
                clean_ticker = "".join(filter(str.isdigit, ticker))
                if not clean_ticker:
                    logger.warning(f"⚠️ Unsupported ticker format: {ticker}")
                    return df_db

            try:
                s_fmt = start_date.replace("-", "")
                e_fmt = end_date.replace("-", "")
                
                df_remote = None
                
                def fetch_data_akshare():
                    """主路径: akshare"""
                    if is_us_stock:
                        return _fetch_data_yfinance()
                    if len(clean_ticker) == 5:
                        return ak.stock_hk_hist(
                            symbol=clean_ticker, period="daily",
                            start_date=s_fmt, end_date=e_fmt,
                            adjust="qfq"
                        )
                    else:
                        return ak.stock_zh_a_hist(
                            symbol=clean_ticker, period="daily",
                            start_date=s_fmt, end_date=e_fmt,
                            adjust="qfq"
                        )

                def _fetch_data_yfinance():
                    """美股路径: yfinance"""
                    yf_ticker = yf.Ticker(clean_ticker)
                    end_dt = datetime.strptime(end_date, "%Y-%m-%d") + timedelta(days=1)
                    df_us = yf_ticker.history(start=start_date, end=end_dt.strftime("%Y-%m-%d"))
                    if df_us.empty:
                        return pd.DataFrame()
                    
                    df_us = df_us.reset_index()
                    date_col = 'Date' if 'Date' in df_us.columns else df_us.columns[0]
                    df_us = df_us.rename(columns={
                        'Open': 'open', 'Close': 'close',
                        'High': 'high', 'Low': 'low', 'Volume': 'volume'
                    })
                    
                    if pd.api.types.is_datetime64_any_dtype(df_us[date_col]):
                        df_us['date'] = df_us[date_col].dt.strftime('%Y-%m-%d')
                    else:
                        df_us['date'] = pd.to_datetime(df_us[date_col]).dt.strftime('%Y-%m-%d')
                        
                    df_us['change_pct'] = df_us['close'].pct_change() * 100
                    df_us['change_pct'] = df_us['change_pct'].fillna(0)
                    
                    return df_us[['date', 'open', 'close', 'high', 'low', 'volume', 'change_pct']]

                def fetch_data_eastmoney():
                    """降级路径: 东方财富直接 HTTP"""
                    logger.info(f"📡 Trying EastMoney direct for {clean_ticker}...")
                    return EastMoneyDirect.fetch_kline(clean_ticker, s_fmt, e_fmt)

                # === 多源尝试: akshare → 东方财富直接 ===
                try:
                    try:
                        df_remote = fetch_data_akshare()
                    except (RequestException, Exception) as e:
                        if "Proxy" in str(e) or "proxy" in str(e):
                            logger.warning(f"⚠️ Proxy error detected: {e}. Retrying with proxy disabled...")
                            with temporary_no_proxy():
                                df_remote = fetch_data_akshare()
                        else:
                            raise e
                except Exception as e:
                    logger.warning(f"⚠️ akshare failed for {clean_ticker}: {e}")
                    if not is_us_stock:
                        try:
                            df_remote = fetch_data_eastmoney()
                        except Exception as e2:
                            logger.warning(f"⚠️ EastMoney direct also failed for {clean_ticker}: {e2}")
                            raise e  # 抛出原始错误
                
                if df_remote is not None and not df_remote.empty:
                    if not is_us_stock:
                        df_remote = df_remote.rename(columns={
                            '日期': 'date', '开盘': 'open', '收盘': 'close',
                            '最高': 'high', '最低': 'low', '成交量': 'volume',
                            '涨跌幅': 'change_pct'
                        })
                    # 确保日期格式正确
                    df_remote['date'] = pd.to_datetime(df_remote['date']).dt.strftime('%Y-%m-%d')
                    
                    # 只有在获取到有意义的数据时才保存
                    self.db.save_stock_prices(clean_ticker, df_remote) # 保存时使用清洗后的 clean_ticker
                    
                    # 重新查询数据库返回结果，保证一致性
                    return self.db.get_stock_prices(clean_ticker, start_date, end_date)
                else:
                    logger.warning(f"⚠️ Akshare returned empty data for {clean_ticker}")
                    
            except KeyError as e:
                # Akshare 有时在某些股票无数据时会抛出 KeyError
                logger.warning(f"⚠️ Akshare data missing for {clean_ticker}: {e}")
            except (RequestException, ConnectionError) as e:
                logger.error(f"❌ Network error during Akshare sync for {clean_ticker}: {e}")
            except sqlite3.Error as e:
                logger.error(f"❌ Database error during Akshare sync for {clean_ticker}: {e}")
            except Exception as e:
                logger.error(f"❌ Unexpected error during Akshare sync for {clean_ticker}: {e}")
        
        return df_db

    def get_stock_fundamentals(self, ticker: str) -> Dict:
        """
        获取公司基本面数据（市值、行业、市盈率、财务摘要等）。
        
        Args:
            ticker: 股票代码，如 "600519"、"AAPL" 或 "00700"。
            
        Returns:
            包含基本面字段的字典。
        """
        is_us_stock = bool(re.search(r'[a-zA-Z]', ticker)) and not bool(re.search(r'\d{5,6}', ticker))
        
        # 清洗 ticker
        if is_us_stock:
            clean_ticker = ticker.upper()
        else:
            clean_ticker = "".join(filter(str.isdigit, ticker))

        if is_us_stock:
            # 美股路径: yfinance
            try:
                tk = yf.Ticker(clean_ticker)
                info = tk.info
                if not info or 'longName' not in info:
                    logger.warning(f"⚠️ No fundamental data found for US stock: {clean_ticker}")
                    return {}
                return {
                    "name": info.get("longName"),
                    "sector": info.get("sector"),
                    "industry": info.get("industry"),
                    "market_cap": info.get("marketCap"),
                    "pe_ratio": info.get("trailingPE"),
                    "summary": info.get("longBusinessSummary", "")[:300] + "..." if info.get("longBusinessSummary") else "",
                    "currency": info.get("currency")
                }
            except Exception as e:
                logger.error(f"❌ yfinance fundamentals failed for {clean_ticker}: {e}")
                return {}
        else:
            # A股/港股路径: akshare
            try:
                # 使用东财接口获取个股基本信息
                df_info = ak.stock_individual_info_em(symbol=clean_ticker)
                if df_info is None or df_info.empty:
                    logger.warning(f"⚠️ No fundamental data found via akshare for: {clean_ticker}")
                    return {}
                
                info_dict = dict(zip(df_info['item'], df_info['value']))
                return {
                    "name": info_dict.get("股票简称"),
                    "code": info_dict.get("股票代码"),
                    "sector": info_dict.get("行业"),
                    "market_cap": info_dict.get("总市值"),
                    "listing_date": info_dict.get("上市时间"),
                    "pe_ratio": info_dict.get("市盈率(动)"),
                }
            except Exception as e:
                logger.error(f"❌ akshare fundamentals failed for {clean_ticker}: {e}")
                return {}



def get_stock_analysis(ticker: str, db: DatabaseManager) -> str:
    """
    生成指定股票的分析摘要报告。
    
    Args:
        ticker: 股票代码
        db: 数据库管理器实例
    
    Returns:
        Markdown 格式的分析报告，包含价格走势和关键指标。
    """
    tools = StockTools(db)
    df = tools.get_stock_price(ticker)
    
    if df.empty:
        return f"❌ 未能获取 {ticker} 的股价数据。"
    
    latest = df.iloc[-1]
    change = ((latest['close'] - df.iloc[0]['close']) / df.iloc[0]['close']) * 100
    
    report = [
        f"## 📊 {ticker} 分析报告",
        f"- **查询时段**: {df.iloc[0]['date']} -> {latest['date']}",
        f"- **当前价**: ¥{latest['close']:.2f}",
        f"- **时段涨跌**: {change:+.2f}%",
        f"- **最高/最低**: ¥{df['high'].max():.2f} / ¥{df['low'].min():.2f}",
        "\n### 最近交易概览",
        "```",
        df.tail(5)[['date', 'close', 'change_pct', 'volume']].to_string(index=False),
        "```"
    ]
    return "\n".join(report)
