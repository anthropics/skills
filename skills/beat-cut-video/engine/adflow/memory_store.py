"""
本地规则记忆引擎
- 风格偏好积累（字体/色调/节奏/音色...）
- 投放效果记忆（哪些策略/钩子/风格效果好）
- 用户调教记录（手动修改反馈）
AI 出片时自动注入累积规则到 prompt
"""

import os, json
from datetime import datetime
from pathlib import Path
from typing import Optional



class MemoryStore:
    """本地记忆存储 — 单例"""

    _instance: Optional["MemoryStore"] = None

    def __new__(cls):
        if cls._instance is None:
            cls._instance = super().__new__(cls)
            cls._instance._init()
        return cls._instance

    def _init(self):
        root = Path(__file__).parent.parent.parent
        self._memory_dir = os.path.join(root, "data", "memory")
        os.makedirs(self._memory_dir, exist_ok=True)
        self._files = {
            "style": os.path.join(self._memory_dir, "style_memory.json"),
            "optimization": os.path.join(self._memory_dir, "optimization_memory.json"),
            "training": os.path.join(self._memory_dir, "training_log.json"),
            "rules": os.path.join(self._memory_dir, "rules.md"),
        }
        for f in self._files.values():
            if not os.path.exists(f):
                self._init_file(f)

    @staticmethod
    def _init_file(path: str):
        ext = os.path.splitext(path)[1]
        if ext == ".json":
            with open(path, "w", encoding="utf-8") as f:
                json.dump([], f, ensure_ascii=False, indent=2)
        elif ext == ".md":
            with open(path, "w", encoding="utf-8") as f:
                f.write("# AdFlow 规则记忆\n\n> 以下规则由用户调教和投放数据自动积累\n\n")

    # ============================================================
    # 风格记忆
    # ============================================================
    def add_style_feedback(self, name: str, data: dict, notes: str = ""):
        """记录一次风格调整偏好"""
        entry = {
            "time": datetime.now().isoformat(),
            "name": name,
            "data": data,
            "notes": notes,
        }
        self._append_json("style", entry)

    def get_style_memory(self, limit: int = 20) -> list[dict]:
        """获取最近风格偏好记录"""
        records = self._read_json("style")
        return records[-limit:]

    def get_style_summary(self) -> str:
        """生成风格记忆摘要 — 用于注入 AI prompt"""
        records = self.get_style_memory(10)
        if not records:
            return ""

        lines = ["## 用户风格偏好（从历史调整中积累）"]
        # 统计最常见的偏好
        font_sizes = []
        voices = []
        paces = []
        for r in records:
            d = r.get("data", {})
            if d.get("font_size"):
                font_sizes.append(d["font_size"])
            if d.get("voice"):
                voices.append(d["voice"])
            if d.get("pace"):
                paces.append(d["pace"])

        if font_sizes:
            avg_size = sum(font_sizes) / len(font_sizes)
            lines.append(f"- 偏好字号: ~{avg_size:.0f}px")
        if voices:
            from collections import Counter
            top_voice = Counter(voices).most_common(1)[0][0]
            lines.append(f"- 偏好音色: {top_voice}")
        if paces:
            top_pace = Counter(paces).most_common(1)[0][0]
            lines.append(f"- 偏好节奏: {top_pace}")

        lines.append(f"- 共 {len(records)} 条风格调教记录")
        return "\n".join(lines)

    # ============================================================
    # 投放优化记忆
    # ============================================================
    def get_optimization_memory(self, limit: int = 20) -> list[dict]:
        return self._read_json("optimization")[-limit:]

    def get_optimization_summary(self) -> str:
        """生成投放效果摘要"""
        records = self.get_optimization_memory(10)
        if not records:
            return ""

        lines = ["## 投放效果记忆"]
        for r in records[-5:]:
            m = r.get("metrics", {})
            ctr = m.get("ctr", 0)
            cvr = m.get("cvr", 0)
            lines.append(
                f"- [{r['time'][:10]}] {r.get('task_id','')[:8]} "
                f"CTR:{ctr:.2%} CVR:{cvr:.2%} | {r.get('insights','')[:80]}"
            )
        return "\n".join(lines)

    # ============================================================
    # 调教日志
    # ============================================================
    def add_training_log(self, category: str, content: str, feedback: str = ""):
        """记录用户调教反馈"""
        entry = {
            "time": datetime.now().isoformat(),
            "category": category,        # subtitle / color / pace / voice / strategy / script
            "content": content,           # 用户描述
            "feedback": feedback,         # AI 分析/回应
        }
        self._append_json("training", entry)

    def get_training_summary(self) -> str:
        """调教日志摘要"""
        records = self._read_json("training")[-15:]
        if not records:
            return ""

        lines = ["## 用户调教记录"]
        for r in records[-5:]:
            lines.append(f"- [{r['category']}] {r['content'][:100]}")
        return "\n".join(lines)

    # ============================================================
    # 规则文件 (Markdown, 直接编辑)
    # ============================================================
    def get_rules(self) -> str:
        """读取用户手写规则"""
        with open(self._files["rules"], "r", encoding="utf-8") as f:
            return f.read()

    # ============================================================
    # 组合输出 — 给 AI Agent 用的完整记忆上下文
    # ============================================================
    def build_context(self) -> str:
        """构建完整记忆上下文，注入到 AI prompt 中"""
        parts = []
        parts.append(self.get_rules())
        parts.append(self.get_style_summary())
        parts.append(self.get_optimization_summary())
        parts.append(self.get_training_summary())
        return "\n\n".join(p for p in parts if p.strip())

    # ============================================================
    # 工具方法
    # ============================================================
    def _read_json(self, key: str) -> list:
        with open(self._files[key], "r", encoding="utf-8") as f:
            try:
                return json.load(f)
            except json.JSONDecodeError:
                return []

    def _append_json(self, key: str, entry: dict):
        data = self._read_json(key)
        data.append(entry)
        # 保留最近 100 条
        if len(data) > 100:
            data = data[-100:]
        with open(self._files[key], "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)


# 全局实例
memory = MemoryStore()
