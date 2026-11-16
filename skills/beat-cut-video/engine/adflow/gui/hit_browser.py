# -*- coding: utf-8 -*-
"""爆款浏览器 — 预览 + 多选参考素材"""

import os

from PyQt6.QtCore import Qt, QSize
from PyQt6.QtGui import QPixmap
from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QLabel, QPushButton,
    QListWidget, QListWidgetItem, QTextEdit, QSplitter,
    QLineEdit, QGroupBox, QMessageBox,
)


class HitBrowser(QDialog):
    """爆款浏览器弹窗 — 预览视频 + 选择参考"""

    def __init__(self, parent=None, multi_select: bool = True):
        super().__init__(parent)
        self.setWindowTitle("爆款素材库 — 选择参考")
        self.resize(900, 600)
        self._selected: list[str] = []

        from adflow.analytics.hit_library import hit_library
        self.lib = hit_library

        layout = QVBoxLayout(self)
        layout.setSpacing(10)

        # ── 搜索栏 ──
        search_row = QHBoxLayout()
        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("搜索爆款（名称/标签/备注）...")
        self.search_input.textChanged.connect(self._on_search)
        search_row.addWidget(self.search_input, 1)

        btn_all = QPushButton("全部")
        btn_all.clicked.connect(lambda: self._load_hits())
        btn_hit = QPushButton("只看爆款")
        btn_hit.setStyleSheet("color:#00d4aa;")
        btn_hit.clicked.connect(lambda: self._load_hits(tags=["hit"]))
        search_row.addWidget(btn_all)
        search_row.addWidget(btn_hit)
        layout.addLayout(search_row)

        # ── 主区域: 列表 + 详情 ──
        splitter = QSplitter(Qt.Orientation.Horizontal)

        # 左侧列表
        self.list_widget = QListWidget()
        self.list_widget.setIconSize(QSize(120, 68))
        self.list_widget.currentRowChanged.connect(self._on_select)
        self.list_widget.itemDoubleClicked.connect(self._preview_video)
        splitter.addWidget(self.list_widget)

        # 右侧详情
        right = QVBoxLayout()
        right.setSpacing(8)

        self.detail_name = QLabel("选择一个爆款查看详情")
        self.detail_name.setStyleSheet("font-size:14px; font-weight:700;")
        right.addWidget(self.detail_name)

        self.detail_tags = QLabel("")
        right.addWidget(self.detail_tags)

        self.detail_perf = QLabel("")
        self.detail_perf.setStyleSheet("color:#00d4aa; font-size:13px;")
        right.addWidget(self.detail_perf)

        self.detail_factors = QTextEdit()
        self.detail_factors.setReadOnly(True)
        self.detail_factors.setMaximumHeight(200)
        self.detail_factors.setPlaceholderText("点击爆款查看因子特征...")
        right.addWidget(self.detail_factors)

        btn_preview = QPushButton("▶ 播放预览")
        btn_preview.clicked.connect(self._preview_video)
        btn_preview.setStyleSheet(
            "QPushButton {background:#1a3a5c; color:white; padding:6px; "
            "border-radius:4px; font-weight:700;}")
        right.addWidget(btn_preview)

        right_widget = QGroupBox("详情")
        right_widget.setLayout(right)
        splitter.addWidget(right_widget)
        splitter.setSizes([400, 450])

        layout.addWidget(splitter, 1)

        # ── 底部按钮 ──
        bottom = QHBoxLayout()
        count_label = QLabel(f"共 {self.lib.count()} 条爆款")
        bottom.addWidget(count_label)
        bottom.addStretch()

        btn_ok = QPushButton("✓ 确认选择（注入Prompt参考）")
        btn_ok.setStyleSheet(
            "QPushButton {background:#1a6b3c; color:white; padding:8px 20px; "
            "border-radius:4px; font-weight:700;}")
        btn_ok.clicked.connect(self._confirm)
        bottom.addWidget(btn_ok)

        btn_cancel = QPushButton("取消")
        btn_cancel.clicked.connect(self.reject)
        bottom.addWidget(btn_cancel)

        layout.addLayout(bottom)

        # 初始加载
        self._load_hits()

    # ═══════════════════════════════════
    # 事件
    # ═══════════════════════════════════

    def _load_hits(self, tags: list[str] | None = None):
        """加载爆款列表"""
        kw = self.search_input.text().strip()
        hits = self.lib.list_hits(tags=tags, keyword=kw)

        self.list_widget.clear()
        self._hit_map = {}  # row → hit_id

        for i, h in enumerate(hits):
            name = h.get("name", "?")
            ctr = h.get("ctr", 0)
            p3s = h.get("play_3s", 0)
            tags_str = ", ".join(h.get("tags", [])[:3])

            text = f"{name}\n  CTR {ctr:.2f}% | 3s完播 {p3s:.1f}%"
            if tags_str:
                text += f" | {tags_str}"

            item = QListWidgetItem(text)
            item.setCheckState(Qt.CheckState.Unchecked)

            # 缩略图
            thumb = h.get("thumbnail", "")
            if thumb and os.path.exists(thumb):
                pix = QPixmap(thumb).scaled(
                    120, 68, Qt.AspectRatioMode.KeepAspectRatio,
                    Qt.TransformationMode.SmoothTransformation)
                item.setIcon(pix)

            item.setSizeHint(QSize(0, 80))
            self.list_widget.addItem(item)
            self._hit_map[i] = h

    def _on_select(self, row: int):
        if row < 0 or row not in self._hit_map:
            return
        h = self._hit_map[row]
        hid = h.get("hit_id", "")

        self.detail_name.setText(h.get("name", "?"))
        self.detail_tags.setText(
            f"标签: {', '.join(h.get('tags', [])) or '无'}")

        ctr = h.get("ctr", 0)
        p3s = h.get("play_3s", 0)
        self.detail_perf.setText(
            f"CTR: {ctr:.2f}% | 3s完播: {p3s:.1f}% | "
            f"备注: {h.get('notes', '')[:60]}"
        )

        # 因子详情
        mem = self.lib.get_memory(hid)
        if mem and mem.get("factors"):
            fd = mem["factors"]
            lines = []
            for cat in ["rhythm", "emotion", "copy", "structure"]:
                cat_data = fd.get(cat, {})
                if cat_data:
                    key_vals = ", ".join(
                        f"{k}={v}" for k, v in list(cat_data.items())[:4]
                        if not isinstance(v, list))
                    lines.append(f"  {cat}: {key_vals}")
            self.detail_factors.setText(
                "因子特征:\n" + "\n".join(lines) if lines else "暂无因子数据")
        else:
            self.detail_factors.setText("暂无因子数据（导入时未提取）")

    def _preview_video(self):
        """用系统默认播放器打开预览"""
        row = self.list_widget.currentRow()
        if row < 0 or row not in self._hit_map:
            QMessageBox.information(self, "提示", "请先选择一个爆款")
            return
        hid = self._hit_map[row].get("hit_id", "")
        path = self.lib.get_video_path(hid)
        if path and os.path.exists(path):
            os.startfile(path)
        else:
            QMessageBox.warning(self, "错误", "视频文件不存在")

    def _on_search(self):
        self._load_hits()

    def _confirm(self):
        """收集选中的爆款ID"""
        self._selected = []
        for row in range(self.list_widget.count()):
            item = self.list_widget.item(row)
            if item and item.checkState() == Qt.CheckState.Checked:
                if row in self._hit_map:
                    self._selected.append(self._hit_map[row].get("hit_id", ""))

        if not self._selected:
            QMessageBox.information(self, "提示", "请先勾选要参考的爆款（点击左侧复选框）")
            return

        self.accept()

    @property
    def selected_ids(self) -> list[str]:
        return self._selected
