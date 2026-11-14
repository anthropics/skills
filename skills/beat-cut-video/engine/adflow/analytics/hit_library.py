# -*- coding: utf-8 -*-
"""爆款素材库 — 导入+索引+单文件记忆（类比 memory_store 模式）

目录结构:
  data/hit_library/
    ├── index.json          # 索引: [{hit_id, name, tags, thumbnail, ...}]
    ├── videos/             # 视频副本
    │   └── {hit_id}.mp4
    └── memories/           # 每爆款一个记忆文件
        └── {hit_id}.json   # 完整数据: 因子+表现+标注+分析

用法:
  lib = HitLibrary()
  hit_id = lib.import_video("爆款A.mp4", performance_data={...})
  hits = lib.list_hits(tags=["护肤品", "女声"])
  memory = lib.get_memory(hit_id)  # → 注入 prompt
"""

import json
import os
import shutil
import uuid
from datetime import datetime
from pathlib import Path
from typing import Optional



class HitLibrary:
    """爆款素材库 — 单例"""

    _instance: Optional["HitLibrary"] = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init()
        return cls._instance

    def _init(self):
        root = Path(__file__).parent.parent.parent
        self._base_dir = os.path.join(root, "data", "hit_library")
        self._video_dir = os.path.join(self._base_dir, "videos")
        self._memory_dir = os.path.join(self._base_dir, "memories")
        self._thumb_dir = os.path.join(self._base_dir, "thumbnails")
        self._index_path = os.path.join(self._base_dir, "index.json")

        for d in [self._video_dir, self._memory_dir, self._thumb_dir]:
            os.makedirs(d, exist_ok=True)
        if not os.path.exists(self._index_path):
            self._write_json(self._index_path, [])

    # ═══════════════════════════════════
    # 导入
    # ═══════════════════════════════════

    def import_video(
        self,
        video_path: str,
        performance: dict | None = None,
        factors: dict | None = None,
        tags: list[str] | None = None,
        notes: str = "",
    ) -> str:
        """导入一条爆款视频。

        Args:
            video_path: 源视频路径
            performance: 投放数据 {ctr, cvr, play_3s_rate, ...}
            factors: 因子快照（可选, 自动提取）
            tags: 标签 ["护肤品", "女声", "紧迫型"]
            notes: 备注

        Returns:
            hit_id (uuid)
        """
        hit_id = uuid.uuid4().hex[:12]

        # 1. 复制视频
        ext = os.path.splitext(video_path)[1] or ".mp4"
        dest_video = os.path.join(self._video_dir, f"{hit_id}{ext}")
        shutil.copy2(video_path, dest_video)

        # 2. 生成缩略图
        thumb_path = ""
        try:
            from adflow.engine.video_probe import VideoProbe
            thumb = os.path.join(self._thumb_dir, f"{hit_id}.jpg")
            VideoProbe.generate_thumbnail(dest_video, thumb, time_sec=1.0)
            if os.path.exists(thumb):
                thumb_path = thumb
        except Exception:
            pass

        # 3. 提取因子
        if factors is None:
            try:
                from adflow.analytics.factor_extractor import FactorExtractor
                f = FactorExtractor.extract(video_path=dest_video)
                factors = f.to_dict()
            except Exception:
                factors = {}

        # 4. 写记忆文件
        memory = {
            "hit_id": hit_id,
            "name": os.path.basename(video_path),
            "source_path": video_path,
            "imported_at": datetime.now().isoformat(),
            "tags": tags or [],
            "notes": notes,
            "performance": performance or {},
            "factors": factors,
            # 爆款分析摘要（供prompt注入）
            "summary": self._build_summary(factors, performance or {}, tags or []),
        }
        mem_path = os.path.join(self._memory_dir, f"{hit_id}.json")
        self._write_json(mem_path, memory)

        # 5. 更新索引
        index = self._read_json(self._index_path)
        index.append({
            "hit_id": hit_id,
            "name": os.path.basename(video_path),
            "tags": tags or [],
            "thumbnail": thumb_path,
            "video_path": dest_video,
            "ctr": (performance or {}).get("ctr", 0),
            "play_3s": (performance or {}).get("play_3s_rate", 0),
            "imported_at": memory["imported_at"],
            "notes": notes[:100],
        })
        self._write_json(self._index_path, index)

        return hit_id

    # ═══════════════════════════════════
    # 查询
    # ═══════════════════════════════════

    def list_hits(self, tags: list[str] | None = None,
                  keyword: str = "",
                  limit: int = 50) -> list[dict]:
        """列出爆款，支持标签过滤 + 关键词搜索"""
        index = self._read_json(self._index_path)
        result = []
        for h in reversed(index):  # 最新在前
            if tags:
                hit_tags = set(h.get("tags", []))
                if not hit_tags.intersection(tags):
                    continue
            if keyword:
                kw = keyword.lower()
                if kw not in h.get("name", "").lower() and \
                   kw not in h.get("notes", "").lower():
                    continue
            result.append(h)
            if len(result) >= limit:
                break
        return result

    def get_memory(self, hit_id: str) -> dict | None:
        """读取单个爆款的完整记忆文件"""
        mem_path = os.path.join(self._memory_dir, f"{hit_id}.json")
        if not os.path.exists(mem_path):
            return None
        return self._read_json(mem_path)

    def get_video_path(self, hit_id: str) -> str:
        """获取爆款视频的本地路径"""
        for ext in [".mp4", ".mov", ".avi", ".webm"]:
            p = os.path.join(self._video_dir, f"{hit_id}{ext}")
            if os.path.exists(p):
                return p
        return ""

    def count(self) -> int:
        return len(self._read_json(self._index_path))

    # ═══════════════════════════════════
    # 更新
    # ═══════════════════════════════════

    def update_tags(self, hit_id: str, tags: list[str]):
        """更新标签"""
        mem = self.get_memory(hit_id)
        if mem:
            mem["tags"] = tags
            self._write_json(
                os.path.join(self._memory_dir, f"{hit_id}.json"), mem)
        self._update_index(hit_id, tags=tags)

    def import_text_only(
        self,
        text: str,
        product_name: str = "",
        category: str = "",
        hook_type: str = "",
        narrative_structure: str = "",
        tags: list[str] | None = None,
        notes: str = "",
    ) -> str:
        """导入纯文本爆款文案（不需要视频文件）

        Args:
            text: 爆款文案全文
            product_name: 产品名
            category: 品类
            hook_type: 钩子类型（痛点/悬念/反差/场景/达人安利）
            narrative_structure: 结构摘要
            tags: 标签列表
            notes: 备注

        Returns:
            hit_id
        """
        import uuid
        import time
        hit_id = f"txt_{uuid.uuid4().hex[:8]}"
        timestamp = int(time.time())

        # 保存文案文本
        memory_path = os.path.join(self._memory_dir, f"{hit_id}.json")
        memory = {
            "hit_id": hit_id,
            "text": text,
            "text_length": len(text),
            "product_name": product_name,
            "category": category,
            "hook_type": hook_type,
            "narrative_structure": narrative_structure,
            "tags": tags or [],
            "notes": notes,
            "source": "text_only",
            "imported_at": datetime.now().isoformat(),
        }
        self._write_json(memory_path, memory)

        # 更新索引
        index = self._read_json(self._index_path)
        index.append({
            "hit_id": hit_id,
            "name": product_name or f"爆款文案_{hit_id[:6]}",
            "category": category,
            "tags": tags or [],
            "has_video": False,
            "imported_at": timestamp,
            "notes": notes,
        })
        self._write_json(self._index_path, index)

        # 分析文案结构
        try:
            from adflow.analytics.hit_text_analyzer import HitTextAnalyzer
            analyzer = HitTextAnalyzer()
            analyzer.analyze("", existing_captions=text,
                             hit_metadata={"title": product_name})
        except Exception:
            pass

        import logging
        logging.getLogger("adflow.hit_library").info(
            "纯文本爆款已导入: %s (%d字) → %s",
                    product_name or "未命名", len(text), hit_id)
        return hit_id

    def delete(self, hit_id: str):
        """删除爆款记录及关联文件"""
        for d in [self._video_dir, self._memory_dir, self._thumb_dir]:
            for ext in ["", ".mp4", ".mov", ".avi", ".webm", ".json", ".jpg"]:
                p = os.path.join(d, f"{hit_id}{ext}")
                if os.path.exists(p):
                    os.remove(p)
        # 从索引移除
        index = self._read_json(self._index_path)
        index = [h for h in index if h.get("hit_id") != hit_id]
        self._write_json(self._index_path, index)

    # ═══════════════════════════════════
    # Prompt 注入
    # ═══════════════════════════════════

    def build_reference_context(self, hit_ids: list[str]) -> str:
        """构建爆款参考上下文 → 注入 AI prompt。

        选中哪些爆款作为参考，提取它们的因子特征和表现数据，
        帮助 LLM 理解"什么风格的视频效果好"。
        支持纯文本爆款（text_only）和视频爆款。
        """
        if not hit_ids:
            return ""

        lines = [
            "## 爆款参考（重点！拆结构、学节奏，不要抄内容）",
            "",
        ]

        for hid in hit_ids[:5]:
            mem = self.get_memory(hid)
            if not mem:
                continue
            name = mem.get("name", mem.get("product_name", hid))
            text = mem.get("text", mem.get("summary", ""))
            hook_type = mem.get("hook_type", "")
            structure = mem.get("narrative_structure", "")
            tags = mem.get("tags", [])
            perf = mem.get("performance", {})

            lines.append(f"### {name}")
            if hook_type:
                lines.append(f"- 钩子类型: {hook_type}")
            if structure:
                lines.append(f"- 结构: {structure}")
            if tags:
                lines.append(f"- 标签: {', '.join(tags)}")
            if text:
                lines.append(f"- 文案: {text[:300]}{'...' if len(text) > 300 else ''}")
            if perf:
                ctr = perf.get("ctr", 0)
                if ctr > 0:
                    lines.append(f"- 表现: CTR {ctr:.2f}%")
            if mem.get("summary"):
                lines.append(f"- 特征: {mem['summary']}")
            lines.append("")

        return "\n".join(lines)

    # ═══════════════════════════════════
    # 内部
    # ═══════════════════════════════════

    @staticmethod
    def _build_summary(factors: dict, performance: dict,
                       tags: list[str]) -> str:
        """从因子+表现生成一句话摘要"""
        parts = []
        rhythm = factors.get("rhythm", {})
        if rhythm:
            avg = rhythm.get("avg_shot_duration", 0)
            if avg:
                parts.append(f"平均镜头{avg:.1f}秒")
        copy_f = factors.get("copy", {})
        if copy_f:
            wps = copy_f.get("words_per_second", 0)
            if wps:
                parts.append(f"语速{wps:.1f}字/秒")
        struct = factors.get("structure", {})
        if struct:
            dur = struct.get("total_duration", 0)
            if dur:
                parts.append(f"总时长{dur:.0f}秒")
        if performance:
            ctr = performance.get("ctr", 0)
            if ctr:
                parts.append(f"CTR{ctr:.2f}%")

        return " | ".join(parts) if parts else "待分析"

    def _update_index(self, hit_id: str, **kwargs):
        index = self._read_json(self._index_path)
        for h in index:
            if h.get("hit_id") == hit_id:
                for k, v in kwargs.items():
                    if k == "notes":
                        h[k] = (v or "")[:100]
                    else:
                        h[k] = v
                break
        self._write_json(self._index_path, index)

    @staticmethod
    def _read_json(path: str):
        with open(path, "r", encoding="utf-8") as f:
            try:
                return json.load(f)
            except json.JSONDecodeError:
                return []

    @staticmethod
    def _write_json(path: str, data):
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)


# 全局实例
hit_library = HitLibrary()
