# -*- coding: utf-8 -*-
"""
BGM 库（简化版）— 上传 + 按列表顺序轮换

替代原 bgm_matcher 的 BPM/情绪/风格/品类四维评分匹配：
BGM 库小、类型趋同，无需智能匹配，退化为「扁平目录 + 文件名列表 + 顺序轮换」。

索引文件 bgm_index.json 存纯字符串数组（文件名 basename，顺序即轮换顺序）：
    ["the_mountain-happy-485567.mp3", "the_mountain-happy-happy-music-496549.mp3"]
"""
import json
import os
import shutil

from adflow.config_loader import config

AUDIO_EXTS = (".mp3", ".wav", ".m4a", ".ogg")


class BGMLibrary:
    """BGM 库：bgm_dir 下扁平存放音频，索引存文件名列表。"""

    def __init__(self, bgm_dir: str = ""):
        self.bgm_dir = bgm_dir or config.bgm_dir
        self.index_path = os.path.join(self.bgm_dir, "bgm_index.json")

    # ── 读取 ──
    def load(self) -> list[str]:
        """返回 basename 列表（保持顺序，剔除已不存在的文件）。兼容旧对象数组格式。"""
        raw = self._read_raw()
        names = []
        for e in raw:
            if isinstance(e, dict):
                fp = e.get("file_path", "") or e.get("file", "")
            else:
                fp = str(e)
            if not fp:
                continue
            base = os.path.basename(fp.replace("\\", "/"))
            if base and os.path.exists(os.path.join(self.bgm_dir, base)):
                names.append(base)
        return names

    def paths(self) -> list[str]:
        """绝对路径列表（渲染/轮换用），顺序同 load()。"""
        return [os.path.join(self.bgm_dir, b) for b in self.load()]

    def rotate(self, index: int) -> str:
        """按索引轮换取一个 BGM 绝对路径；空库返回 ""。"""
        ps = self.paths()
        return ps[index % len(ps)] if ps else ""

    # ── 写入 ──
    def save(self, basenames: list[str]) -> None:
        os.makedirs(self.bgm_dir, exist_ok=True)
        with open(self.index_path, "w", encoding="utf-8") as f:
            json.dump(basenames, f, ensure_ascii=False, indent=2)

    # ── 增删 ──
    def add(self, src_path: str) -> str:
        """复制音频到 bgm_dir 扁平根（已存在则不覆盖），入列并写回，返回 basename。"""
        os.makedirs(self.bgm_dir, exist_ok=True)
        base = os.path.basename(src_path)
        dest = os.path.join(self.bgm_dir, base)
        if not os.path.exists(dest):
            shutil.copy2(src_path, dest)
        names = self.load()
        if base not in names:
            names.append(base)
            self.save(names)
        return base

    def remove(self, basename: str) -> None:
        """删文件并从列表移除后写回。"""
        fpath = os.path.join(self.bgm_dir, basename)
        if os.path.exists(fpath):
            os.remove(fpath)
        self.save([b for b in self.load() if b != basename])

    # ── 内部 ──
    def _read_raw(self) -> list:
        if not os.path.exists(self.index_path):
            return []
        try:
            with open(self.index_path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except (json.JSONDecodeError, OSError):
            return []
        if isinstance(data, dict):
            data = data.get("bgm_library", [])
        return data if isinstance(data, list) else []
