# -*- coding: utf-8 -*-
"""
出片前审核弹窗 — 文案确认/驳回 + 配音选择 + AI配音试听

GUI对接: AI出片模块 → 启动前弹出此对话框
"""
import os
from PyQt6.QtWidgets import (
    QDialog, QVBoxLayout, QHBoxLayout, QTextEdit, QPushButton,
    QLabel, QComboBox, QSlider, QGroupBox, QMessageBox,
)
from PyQt6.QtCore import Qt, QUrl
from PyQt6.QtMultimedia import QMediaPlayer, QAudioOutput


class ReviewDialog(QDialog):
    """出片前审核弹窗

    功能:
      - 显示生成的文案 → 用户确认/驳回
      - 配音选择（下拉列表+试听按钮）
      - 语速控制（滑块 0.5x-2.0x）
    """

    def __init__(self, script_text: str = "", parent=None):
        super().__init__(parent)
        self.setWindowTitle("AI出片 — 审核文案")
        self.setMinimumSize(700, 600)
        self.approved = False
        self.closed = False  # 点 X 关闭（非驳回/确认），用于退回主界面改配置
        self.voice_id = ""
        self.speech_rate = 1.0
        self.shot_duration_ms = 2500
        self.bgm_file = ""
        self._player = None
        self._audio_output = None

        self._setup_ui(script_text)

    def _setup_ui(self, script_text: str):
        layout = QVBoxLayout(self)

        # ── 文案展示 ──
        layout.addWidget(QLabel("AI生成的文案（请审核）："))
        self.text_edit = QTextEdit()
        self.text_edit.setPlainText(script_text)
        self.text_edit.setReadOnly(False)   # 可手动编辑
        self.text_edit.setMinimumHeight(200)
        self.text_edit.setPlaceholderText("可直接修改文案内容...")
        layout.addWidget(self.text_edit)

        # ── 配音选择 + 试听 ──
        voice_group = QGroupBox("配音选择")
        voice_layout = QVBoxLayout(voice_group)

        voice_row = QHBoxLayout()
        voice_row.addWidget(QLabel("音色:"))
        self.voice_combo = QComboBox()
        self._load_voices()
        voice_row.addWidget(self.voice_combo)

        self.btn_audition = QPushButton("试听")
        self.btn_audition.clicked.connect(self._on_audition)
        voice_row.addWidget(self.btn_audition)
        voice_layout.addLayout(voice_row)

        # 语速滑块
        speed_row = QHBoxLayout()
        speed_row.addWidget(QLabel("语速:"))
        self.speed_slider = QSlider(Qt.Orientation.Horizontal)
        self.speed_slider.setRange(50, 200)
        self.speed_slider.setValue(100)
        self.speed_slider.setTickInterval(10)
        self.speed_label = QLabel("1.0x")
        self.speed_slider.valueChanged.connect(
            lambda v: self.speed_label.setText(f"{v/100:.1f}x"))
        speed_row.addWidget(self.speed_slider)
        speed_row.addWidget(self.speed_label)
        voice_layout.addLayout(speed_row)

        # 句间停顿（AI 自动=按镜头角色动态：开头快收尾慢）
        pause_row = QHBoxLayout()
        pause_row.addWidget(QLabel("句间停顿:"))
        self.pause_combo = QComboBox()
        self.pause_combo.addItem("AI 自动（按镜头角色）", 0)
        self.pause_combo.addItem("短（0.2 秒）", 200)
        self.pause_combo.addItem("标准（0.4 秒）", 400)
        self.pause_combo.addItem("长（0.7 秒）", 700)
        pause_row.addWidget(self.pause_combo)
        voice_layout.addLayout(pause_row)

        # 镜头时长（镜头数 = 配音 ÷ 镜头时长）
        shot_row = QHBoxLayout()
        shot_row.addWidget(QLabel("镜头时长:"))
        self.shot_combo = QComboBox()
        for s in [1.5, 2.0, 2.5, 3.0, 3.5, 4.0]:
            self.shot_combo.addItem(f"{s:.1f} 秒", int(s * 1000))
        self.shot_combo.setCurrentIndex(2)  # 默认 2.5 秒
        shot_row.addWidget(self.shot_combo)
        shot_row.addWidget(QLabel("（镜头数 = 配音 ÷ 镜头时长）"))
        voice_layout.addLayout(shot_row)

        # BGM 指定：自动轮换 / 库内某首
        bgm_row = QHBoxLayout()
        bgm_row.addWidget(QLabel("BGM:"))
        self.bgm_combo = QComboBox()
        self._load_bgms()
        bgm_row.addWidget(self.bgm_combo)
        voice_layout.addLayout(bgm_row)

        layout.addWidget(voice_group)

        # ── 按钮 ──
        btn_row = QHBoxLayout()
        self.btn_retry = QPushButton("再优化（重新生成）")
        self.btn_retry.setStyleSheet(
            "background-color: #f0ad4e; color: white; padding: 8px 16px;")
        self.btn_retry.clicked.connect(self._on_retry)

        self.btn_confirm = QPushButton("确认继续（开始混剪）")
        self.btn_confirm.setStyleSheet(
            "background-color: #5cb85c; color: white; padding: 8px 16px;")
        self.btn_confirm.clicked.connect(self._on_confirm)

        btn_row.addWidget(self.btn_retry)
        btn_row.addWidget(self.btn_confirm)
        layout.addLayout(btn_row)

    def _load_voices(self):
        """加载可用音色列表，第一项为AI自动选择"""
        # ── AI 自动选择（根据文案内容智能匹配音色）──
        self.voice_combo.addItem("🤖 AI 自动选择（根据文案匹配合适音色）", "")
        self.voice_combo.insertSeparator(1)
        try:
            from adflow.engine.voice_audition import VoiceAuditionService
            svc = VoiceAuditionService()
            voices = svc.list_voices()
            for v in voices:
                label = f"[{v.backend}] {v.name} ({v.gender}/{v.style})"
                self.voice_combo.addItem(label, v.voice_id)
        except Exception:
            self.voice_combo.addItem("默认（按配置自动选）", "")

    def _load_bgms(self):
        """加载 BGM 下拉：第一项自动轮换，其余为库内已上传 BGM"""
        self.bgm_combo.addItem("🤖 自动轮换", "")
        try:
            from adflow.engine.bgm_library import BGMLibrary
            for p in BGMLibrary().paths():
                self.bgm_combo.addItem(os.path.basename(p), p)
        except Exception:
            pass

    def _on_audition(self):
        """试听当前选中音色"""
        voice_id = self.voice_combo.currentData()
        if not voice_id:
            return
        try:
            from adflow.engine.voice_audition import VoiceAuditionService
            svc = VoiceAuditionService()
            path = svc.audition(voice_id)
            if path and os.path.exists(path):
                self._play_audio(path)
        except Exception as e:
            QMessageBox.warning(self, "试听失败", str(e))

    def _play_audio(self, path: str):
        """播放音频"""
        if self._player is None:
            self._player = QMediaPlayer()
            self._audio_output = QAudioOutput()
            self._player.setAudioOutput(self._audio_output)
        self._player.setSource(QUrl.fromLocalFile(path))
        self._player.play()

    def _on_retry(self):
        """驳回，重新生成"""
        self.approved = False
        self.reject()

    def _on_confirm(self):
        """确认继续"""
        self.approved = True
        self.voice_id = self.voice_combo.currentData() or ""
        self.speech_rate = self.speed_slider.value() / 100.0
        self.shot_duration_ms = self.shot_combo.currentData() or 2500
        self.bgm_file = self.bgm_combo.currentData() or ""
        self.accept()

    def closeEvent(self, event) -> None:
        """点 X 关闭时标记 closed=True（区分「再优化」按钮的程序 reject）"""
        if event.spontaneous():
            self.closed = True
        super().closeEvent(event)

    def get_params(self) -> dict:
        """获取用户选择的参数 + 编辑后的文案"""
        return {
            "approved": self.approved,
            "voice_id": self.voice_id,
            # 滑块停在默认 1.0x 时传 0，让 pipeline 走引擎默认语速（config tts.speech_rate）
            "speech_rate": 0.0 if abs(self.speech_rate - 1.0) < 1e-6 else self.speech_rate,
            "shot_duration_ms": self.shot_duration_ms,
            "bgm_file": self.bgm_file,
            # 句间停顿：0=AI 自动（按角色动态），>0=固定毫秒
            "pause_ms": self.pause_combo.currentData() or 0,
            "edited_text": self.text_edit.toPlainText() if not self.text_edit.isReadOnly() else "",
        }
