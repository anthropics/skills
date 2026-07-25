import time
from typing import Optional, List
from loguru import logger

from .utils.database_manager import DatabaseManager

class FinUtils:
    """
    金融分析辅助工具 (FinUtils)
    提供数据清洗、Output Sanitization 等功能。
    核心分析逻辑已移交 Agent 执行 (参考 scripts/prompts/PROMPTS.md)。
    """
    
    def __init__(self, db: DatabaseManager):
        self.db = db

    @staticmethod
    def _clean_digits(value: str) -> str:
        s = (value or "").strip()
        if not s:
            return ""
        return "".join([c for c in s if c.isdigit()])

    def sanitize_signal_output(self, json_data: dict, research_data: Optional[dict] = None, raw_signal: str = "") -> dict:
        """Post-process LLM output to prevent spurious ticker/name binding."""
        if not isinstance(json_data, dict):
            return json_data

        tool_suggested: set[str] = set()
        if isinstance(research_data, dict):
            tf = research_data.get('tickers_found')
            if isinstance(tf, list):
                for item in tf:
                    if not isinstance(item, dict):
                        continue
                    code_raw = item.get('code') or item.get('ticker') or item.get('symbol')
                    code = self._clean_digits(str(code_raw or ""))
                    if code:
                        tool_suggested.add(code)

        sources = json_data.get('sources')
        source_titles: list[str] = []
        source_urls: list[str] = []
        if isinstance(sources, list):
            for s in sources:
                if not isinstance(s, dict):
                    continue
                t = str(s.get('title') or "").strip()
                u = str(s.get('url') or "").strip()
                if t:
                    source_titles.append(t)
                if u:
                    source_urls.append(u)

        evidence_text = " ".join([
            str(raw_signal or ""),
            str(json_data.get('title') or ""),
            str(json_data.get('summary') or ""),
            " ".join(source_titles),
            " ".join(source_urls),
        ])

        impact = json_data.get('impact_tickers')
        if not isinstance(impact, list):
            return json_data
        
        if not impact:
            return json_data

        sanitized: list[dict] = []
        for item in impact:
            if not isinstance(item, dict):
                continue
            code_raw = item.get('ticker') or item.get('code') or item.get('symbol')
            code = self._clean_digits(str(code_raw or ""))
            
            # Simple validation if DB lookup is too expensive or complex here. 
            # But the original code used self.db, so we try to use it.
            if not (code.isdigit() and len(code) in (5, 6)):
                continue

            # Original logic used DB to verify stock existence
            try:
                stock = self.db.get_stock_by_code(code)
                if not stock:
                    continue
                official_name = stock.get('name') or ""
                
                mentioned = (code in evidence_text) or (official_name and official_name in evidence_text)
                if tool_suggested:
                    if code not in tool_suggested and not mentioned:
                        continue
                else:
                    if not mentioned:
                        continue

                new_item = dict(item)
                new_item['ticker'] = code
                new_item['name'] = official_name
                sanitized.append(new_item)
            except Exception:
                # If DB access fails, be permissive or conservative? Conservative to avoid hallucinations.
                pass

        json_data['impact_tickers'] = sanitized
        return json_data
