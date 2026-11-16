# -*- coding: utf-8 -*-
"""
屏蔽词管理面板 — 添加/移除文案屏蔽词

数据文件: adflow/data/blocked_words.json
8大类默认词库 + 用户自定义词
"""
import json
import os

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QListWidget, QListWidgetItem, QLineEdit,
    QTabWidget, QMessageBox,
)
from PyQt6.QtCore import Qt


BLOCKED_WORDS_PATH = os.path.join(
    os.path.dirname(__file__), "..", "data", "blocked_words.json")


def load_blocked_words_context() -> str:
    """加载屏蔽词并构建 Prompt 上下文（不实例化 QWidget，供 Agent 层调用）"""
    try:
        with open(BLOCKED_WORDS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
    except Exception:
        data = {"categories": {}, "custom_words": []}

    categories = data.get("categories", {})
    custom = data.get("custom_words", [])
    lines = ["## 文案屏蔽词（强制执行，命中即替换）", ""]
    for cat_name, cat_data in categories.items():
        words = cat_data.get("words", [])
        if not words:
            continue
        reps = cat_data.get("replace", [])
        lines.append(f"### {cat_name}")
        lines.append(f"- 禁用: {', '.join(words[:20])}")
        if reps:
            lines.append(f"- 替代: {', '.join(reps[:10])}")
        lines.append("")
    if custom:
        lines.append("### 用户自定义屏蔽词")
        lines.append(f"- 禁用: {', '.join(custom)}")
    lines.append("\n以上词汇在文案中禁止出现，出现即替换为安全替代词。")
    return "\n".join(lines)


class BlockedWordsPanel(QWidget):
    """屏蔽词设置面板"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._data = {}
        self._load()
        self._setup_ui()

    def _load(self):
        try:
            with open(BLOCKED_WORDS_PATH, "r", encoding="utf-8") as f:
                self._data = json.load(f)
        except Exception:
            self._data = {"categories": {}, "custom_words": []}

    def _save(self):
        os.makedirs(os.path.dirname(BLOCKED_WORDS_PATH), exist_ok=True)
        with open(BLOCKED_WORDS_PATH, "w", encoding="utf-8") as f:
            json.dump(self._data, f, ensure_ascii=False, indent=2)

    def _setup_ui(self):
        layout = QVBoxLayout(self)

        # ── 顶部说明 ──
        layout.addWidget(QLabel(
            "AI生成的文案会自动屏蔽以下词汇。命中后替换为安全替代词。"
        ))
        layout.addWidget(QLabel(
            "8大类默认词库 + 自定义词。可在此面板添加/移除。"
        ))

        # ── 分类标签 ──
        self.tabs = QTabWidget()

        categories = self._data.get("categories", {})
        for cat_name, cat_data in categories.items():
            tab = self._build_category_tab(cat_name, cat_data)
            self.tabs.addTab(tab, cat_name)

        # 自定义词标签
        custom_tab = self._build_custom_tab()
        self.tabs.addTab(custom_tab, "自定义词")

        layout.addWidget(self.tabs)

        # ── 底部：快速添加 + 保存 ──
        bottom = QHBoxLayout()
        self.quick_input = QLineEdit()
        self.quick_input.setPlaceholderText("输入要屏蔽的词，回车添加...")
        self.quick_input.returnPressed.connect(self._quick_add)
        bottom.addWidget(self.quick_input)

        btn_save = QPushButton("💾 保存")
        btn_save.clicked.connect(self._on_save)
        bottom.addWidget(btn_save)
        layout.addLayout(bottom)

    def _build_category_tab(self, name: str, data: dict) -> QWidget:
        """构建一个分类标签页"""
        w = QWidget()
        layout = QVBoxLayout(w)

        layout.addWidget(QLabel(f"<b>{data.get('desc', '')}</b>"))

        # 禁用词列表
        layout.addWidget(QLabel("禁用词（点击选中后可按Delete删除）:"))
        word_list = QListWidget()
        for word in data.get("words", []):
            item = QListWidgetItem(word)
            item.setFlags(item.flags() | Qt.ItemFlag.ItemIsEditable)
            word_list.addItem(item)
        word_list.keyPressEvent = lambda e, wl=word_list, n=name: (
            self._on_delete_key(e, wl, n))
        layout.addWidget(word_list)

        # 添加按钮
        add_row = QHBoxLayout()
        self._cat_inputs = getattr(self, '_cat_inputs', {})
        inp = QLineEdit()
        inp.setPlaceholderText(f"添加{name}禁用词...")
        self._cat_inputs[name] = inp
        add_row.addWidget(inp)
        btn_add = QPushButton("添加")
        btn_add.clicked.connect(lambda: self._add_to_category(name))
        add_row.addWidget(btn_add)
        layout.addLayout(add_row)

        # 替代词
        reps = data.get("replace", [])
        if reps:
            layout.addWidget(QLabel(
                f"安全替代词: {', '.join(reps[:10])}"))

        return w

    def _build_custom_tab(self) -> QWidget:
        """自定义屏蔽词标签"""
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.addWidget(QLabel("<b>用户自定义屏蔽词</b>"))

        self.custom_list = QListWidget()
        for word in self._data.get("custom_words", []):
            self.custom_list.addItem(word)
        layout.addWidget(self.custom_list)

        add_row = QHBoxLayout()
        self.custom_input = QLineEdit()
        self.custom_input.setPlaceholderText("输入自定义屏蔽词...")
        self.custom_input.returnPressed.connect(self._add_custom)
        add_row.addWidget(self.custom_input)
        btn_add_custom = QPushButton("添加")
        btn_add_custom.clicked.connect(self._add_custom)
        add_row.addWidget(btn_add_custom)

        btn_remove_custom = QPushButton("删除选中")
        btn_remove_custom.clicked.connect(self._remove_custom)
        add_row.addWidget(btn_remove_custom)
        layout.addLayout(add_row)

        return w

    def _add_to_category(self, name: str):
        inp = self._cat_inputs.get(name)
        if not inp:
            return
        word = inp.text().strip()
        if not word:
            return
        cats = self._data.setdefault("categories", {})
        cats.setdefault(name, {}).setdefault("words", []).append(word)
        inp.clear()
        self._refresh()

    def _on_delete_key(self, event, word_list: QListWidget, cat_name: str):
        """Delete键删除选中词"""
        if event.key() == Qt.Key.Key_Delete:
            row = word_list.currentRow()
            if row >= 0:
                word = word_list.item(row).text()
                cats = self._data.get("categories", {})
                words = cats.get(cat_name, {}).get("words", [])
                if word in words:
                    words.remove(word)
                word_list.takeItem(row)
        else:
            QListWidget.keyPressEvent(word_list, event)

    def _add_custom(self):
        word = self.custom_input.text().strip()
        if not word:
            return
        self._data.setdefault("custom_words", []).append(word)
        self.custom_list.addItem(word)
        self.custom_input.clear()

    def _remove_custom(self):
        row = self.custom_list.currentRow()
        if row >= 0:
            word = self.custom_list.item(row).text()
            self._data.get("custom_words", []).remove(word)
            self.custom_list.takeItem(row)

    def _quick_add(self):
        """快速添加到自定义词"""
        word = self.quick_input.text().strip()
        if word:
            self._data.setdefault("custom_words", []).append(word)
            self.custom_list.addItem(word)
            self.quick_input.clear()

    def _on_save(self):
        self._save()
        QMessageBox.information(self, "已保存", "屏蔽词已更新。下次生成文案时生效。")

    def _refresh(self):
        """刷新UI（重新加载所有标签）"""
        self.tabs.clear()
        for cat_name, cat_data in self._data.get("categories", {}).items():
            tab = self._build_category_tab(cat_name, cat_data)
            self.tabs.addTab(tab, cat_name)
        self.tabs.addTab(self._build_custom_tab(), "自定义词")

    # ── 工具方法：构建Prompt注入上下文 ──

    def build_prompt_context(self) -> str:
        """构建注入Prompt的屏蔽词上下文"""
        categories = self._data.get("categories", {})
        custom = self._data.get("custom_words", [])

        lines = ["## 文案屏蔽词（强制执行，命中即替换）", ""]

        for cat_name, cat_data in categories.items():
            words = cat_data.get("words", [])
            if not words:
                continue
            reps = cat_data.get("replace", [])
            lines.append(f"### {cat_name}")
            lines.append(f"- 禁用: {', '.join(words[:20])}")
            if reps:
                lines.append(f"- 替代: {', '.join(reps[:10])}")
            lines.append("")

        if custom:
            lines.append("### 用户自定义屏蔽词")
            lines.append(f"- 禁用: {', '.join(custom)}")

        lines.append("\n以上词汇在文案中禁止出现，出现即替换为安全替代词。")
        return "\n".join(lines)
