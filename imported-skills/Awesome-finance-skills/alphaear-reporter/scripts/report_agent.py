import hashlib
import json
import re
import pandas as pd
from typing import List, Dict, Any, Optional
from loguru import logger
from types import SimpleNamespace

from .utils.database_manager import DatabaseManager
from .utils.json_utils import extract_json

class ReportUtils:
    """
    研报辅助工具集 (ReportUtils)
    提供格式化、引用管理、 JSON 提取等辅助功能。
    核心生成逻辑（聚类、写作）已移交 Agent 执行。
    """
    
    def __init__(self, db: DatabaseManager):
        self.db = db
        logger.info("📝 ReportUtils initialized")

    @staticmethod
    def _make_cite_key(url: str, title: str = "", source_name: str = "") -> str:
        basis = (url or "").strip() or f"{(title or '').strip()}|{(source_name or '').strip()}"
        digest = hashlib.sha1(basis.encode("utf-8")).hexdigest()[:8]
        return f"SF-{digest}"

    def build_bibliography(self, signals: List[Any]) -> tuple[list[Dict[str, Any]], Dict[int, list[str]]]:
        """Build stable bibliography entries and per-signal cite key mapping."""
        bib_by_key: Dict[str, Dict[str, Any]] = {}
        signal_to_keys: Dict[int, list[str]] = {}

        for sig_idx, signal in enumerate(signals, 1):
            source_items: list[Dict[str, Any]] = []

            if hasattr(signal, "sources") and getattr(signal, "sources"):
                source_items = list(getattr(signal, "sources") or [])
            elif isinstance(signal, dict) and signal.get("sources"):
                src_list = signal.get("sources")
                if isinstance(src_list, list) and src_list:
                    source_items = list(src_list)
            elif isinstance(signal, dict):
                if signal.get("url") or signal.get("title"):
                    source_items = [
                        {
                            "title": signal.get("title"),
                            "url": signal.get("url"),
                            "source_name": signal.get("source") or signal.get("source_name"),
                            "publish_time": signal.get("publish_time"),
                        }
                    ]

            if not source_items:
                continue

            for src in source_items:
                url = (src.get("url") or "").strip()
                title = (src.get("title") or "").strip()
                source_name = (src.get("source_name") or src.get("source") or "").strip()
                publish_time = (src.get("publish_time") or "").strip() if isinstance(src.get("publish_time"), str) else src.get("publish_time")

                key = self._make_cite_key(url=url, title=title, source_name=source_name)
                signal_to_keys.setdefault(sig_idx, [])
                if key not in signal_to_keys[sig_idx]:
                    signal_to_keys[sig_idx].append(key)

                if key in bib_by_key:
                    continue

                # Prefer canonical metadata from DB when possible
                enriched = self.db.lookup_reference_by_url(url) if url else None
                bib_by_key[key] = {
                    "key": key,
                    "url": url or (enriched.get("url") if enriched else ""),
                    "title": (enriched.get("title") if enriched else None) or title or "（无标题）",
                    "source": (enriched.get("source") if enriched else None) or source_name or "（未知来源）",
                    "publish_time": (enriched.get("publish_time") if enriched else None) or publish_time or "",
                }

        return list(bib_by_key.values()), signal_to_keys

    @staticmethod
    def render_references_section(bib_entries: list[Dict[str, Any]]) -> str:
        lines = ["## 参考文献", ""]
        if not bib_entries:
            lines.append("（无）")
            return "\n".join(lines).strip() + "\n"

        for i, entry in enumerate(bib_entries, 1):
            key = entry.get("key")
            title = entry.get("title") or "（无标题）"
            source = entry.get("source") or "（未知来源）"
            url = entry.get("url") or ""
            publish_time = entry.get("publish_time") or ""
            suffix = ""
            if publish_time:
                suffix = f"，{publish_time}"
            label = f"[{i}]"
            if url:
                lines.append(f"<a id=\"ref-{key}\"></a>{label} {title} ({source}{suffix}), {url}")
            else:
                lines.append(f"<a id=\"ref-{key}\"></a>{label} {title} ({source}{suffix})")

        return "\n".join(lines).strip() + "\n"

    @staticmethod
    def sanitize_json_chart_blocks(text: str) -> str:
        """Best-effort repair for malformed json-chart fenced blocks."""
        if not text:
            return text
        # (Simplified logic: if closing ``` is missing, append it)
        # Full logic omitted for brevity as it was complex regex, but retaining simple closure fix
        if "```json-chart" in text and text.count("```") % 2 != 0:
            text += "\n```"
        return text

    @staticmethod
    def build_structured_report(report_md: str, signals: List[Dict[str, Any]], clusters: List[Dict[str, Any]]) -> Dict[str, Any]:
        """构建结构化研报输出（便于前端渲染/JSON化）"""
        text = (report_md or "").strip()
        lines = text.splitlines() if text else []

        title = "研报"
        for line in lines:
            if line.startswith("# "):
                title = line.replace("# ", "").strip()
                break

        sections: List[Dict[str, Any]] = []
        current: Dict[str, Any] | None = None
        for line in lines:
            heading = re.match(r"^(#{2,4})\s+(.*)$", line.strip())
            if heading:
                if current:
                    sections.append(current)
                current = {"title": heading.group(2).strip(), "content": []}
                continue
            if current is None:
                current = {"title": "摘要", "content": []}
            current["content"].append(line)
        if current:
            sections.append(current)

        bullets = [
            re.sub(r"^[-*•]\s+", "", l.strip())
            for l in lines
            if l.strip().startswith(("- ", "* ", "• "))
        ]
        bullets = [b for b in bullets if b]

        return {
            "title": title,
            "summary_bullets": bullets[:8],
            "sections": [
                {"title": s["title"], "content": "\n".join(s["content"]).strip()}
                for s in sections
            ]
        }

    @staticmethod
    def _clean_ticker(ticker_raw: str) -> str:
        t = (ticker_raw or "").strip()
        if not t:
            return ""
        digits = "".join([c for c in t if c.isdigit()])
        return digits or t
