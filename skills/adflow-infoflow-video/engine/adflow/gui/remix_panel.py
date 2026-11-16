# -*- coding: utf-8 -*-
"""
AI出片 — 配音裂变面板

上传配音/视频 → 直接匹配素材混剪（爆款原声模式）
"""
import os
import subprocess
import tempfile
import time
from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton,
    QLabel, QGroupBox, QFileDialog, QLineEdit, QMessageBox, QTextEdit,
    QProgressBar,
)
from PyQt6.QtCore import QThread, pyqtSignal

_VIDEO_EXTS = ('.mp4', '.mov', '.mkv', '.avi', '.webm', '.m4v', '.flv')
_AUDIO_EXTS = ('.mp3', '.wav', '.m4a', '.aac', '.flac', '.ogg')


class RemixWorker(QThread):
    """后台线程：跑配音裂变 pipeline"""
    progress = pyqtSignal(str)
    done = pyqtSignal(object)  # PipelineResult
    error = pyqtSignal(str)

    def __init__(self, product, custom_text, custom_audio, review_params=None):
        super().__init__()
        self._product = product
        self._custom_text = custom_text
        self._custom_audio = custom_audio
        self._params = review_params or {}

    def run(self):
        try:
            # 在工作线程内创建 pipeline（DB 连接绑定创建线程，跨线程复用会 ProgrammingError）
            from adflow.agents.pipeline import AdPipeline
            pipeline = AdPipeline()
            result = pipeline.run(
                product=self._product,
                custom_text=self._custom_text,
                custom_audio=self._custom_audio,
                review_callback=None,
                voice_override=self._params.get("voice_id") or "",
                speech_rate_override=self._params.get("speech_rate") or 0.0,
                pause_ms_override=self._params.get("pause_ms") or 0,
                shot_duration_override=self._params.get("shot_duration_ms") or 0,
                bgm_file_override=self._params.get("bgm_file") or "",
                progress_callback=lambda msg: self.progress.emit(msg),
            )
            self.done.emit(result)
        except Exception as e:
            self.error.emit(str(e))


class RemixPanel(QWidget):
    """文案/配音裂变面板"""

    def __init__(self, parent=None):
        super().__init__(parent)
        self._custom_audio_path = ""
        self._setup_ui()

    # ═══════════════════════════════════════
    # UI 搭建
    # ═══════════════════════════════════════

    def _setup_ui(self):
        main = QVBoxLayout(self)

        # ── 配音裂变 ──
        grp_audio = QGroupBox("配音裂变 — 上传配音文件，直接混剪")
        audio_layout = QVBoxLayout(grp_audio)

        audio_row = QHBoxLayout()
        self.audio_path_label = QLineEdit()
        self.audio_path_label.setReadOnly(True)
        self.audio_path_label.setPlaceholderText("选择配音或视频文件（视频自动抽音轨）...")
        audio_row.addWidget(self.audio_path_label)

        btn_pick = QPushButton("浏览")
        btn_pick.clicked.connect(self._on_pick_audio)
        audio_row.addWidget(btn_pick)
        audio_layout.addLayout(audio_row)

        self.copy_input = QTextEdit()
        self.copy_input.setMaximumHeight(80)
        self.copy_input.setPlaceholderText(
            "可选：贴入配音对应的文案（字幕会用此文案，和配音一致；不填则 AI 生成字幕）")
        audio_layout.addWidget(self.copy_input)

        self.btn_audio = QPushButton("配音裂变 — 直接混剪")
        self.btn_audio.setStyleSheet(
            "background-color: #f0ad4e; color: white; padding: 8px; font-size: 14px;")
        self.btn_audio.clicked.connect(self._on_audio_remix)
        audio_layout.addWidget(self.btn_audio)

        main.addWidget(grp_audio)

        # ── 进度条 + 状态 ──
        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        main.addWidget(self.progress_bar)

        self.status_label = QLabel("就绪")
        self.status_label.setStyleSheet("color: #999;")
        main.addWidget(self.status_label)

    # ═══════════════════════════════════════
    # 逻辑
    # ═══════════════════════════════════════

    def _on_audio_remix(self):
        """配音裂变：弹窗审核 → 混剪"""
        if not self._custom_audio_path:
            QMessageBox.warning(self, "提示", "请先选择配音文件")
            return

        # ── 弹窗审核：文案可改（字幕=此文案，与配音对齐），配音/停顿/镜头时长可选 ──
        from adflow.gui.review_dialog import ReviewDialog
        dlg = ReviewDialog(
            self.copy_input.toPlainText().strip()
            or "（未填文案 — 将由 AI 生成字幕文案）",
            parent=self)
        if not dlg.exec():
            self.status_label.setText("已驳回")
            return
        params = dlg.get_params()
        # 弹窗里改过的文案优先（字幕与配音对齐用的就是它）
        edited = (params.get("edited_text") or "").strip()

        self.status_label.setText("配音裂变中...")
        self.progress_bar.setVisible(True)
        self.progress_bar.setRange(0, 0)  # 不确定进度
        self.btn_audio.setEnabled(False)

        from adflow.models import ProductProfile
        product = ProductProfile(
            name="配音裂变素材", category="通用",
            key_selling_points="用户配音", target_audience="泛人群",
            pain_points="", brand_tone="口语",
        )

        custom_text = edited or self.copy_input.toPlainText().strip()

        self.worker = RemixWorker(
            product, custom_text,
            self._custom_audio_path, review_params=params)
        self.worker.progress.connect(self._on_remix_progress)
        self.worker.done.connect(self._on_remix_finished)
        self.worker.error.connect(self._on_remix_error)
        self.worker.finished.connect(self.worker.deleteLater)
        self.worker.start()

    def _on_remix_progress(self, msg):
        self.status_label.setText(msg)

    def _on_remix_finished(self, result):
        self.btn_audio.setEnabled(True)
        self.progress_bar.setVisible(False)
        self.status_label.setText(
            f"{'成功' if result.success else '失败'}: "
            f"{len(result.variants)}个变体")

        if result.success:
            from adflow.config_loader import config
            msg_box = QMessageBox(self)
            msg_box.setWindowTitle("配音裂变完成")
            msg_box.setText(f"产出 {len(result.variants)} 个视频变体\n\n"
                            f"输出目录: {config.output_dir}")
            msg_box.setIcon(QMessageBox.Icon.Information)
            btn_open = msg_box.addButton("📂 打开目录", QMessageBox.ButtonRole.ActionRole)
            msg_box.addButton("关闭", QMessageBox.ButtonRole.RejectRole)
            msg_box.exec()
            if msg_box.clickedButton() == btn_open:
                self._open_output_dir()

    def _on_remix_error(self, error):
        self.btn_audio.setEnabled(True)
        self.progress_bar.setVisible(False)
        self.status_label.setText(f"❌ {error}")
        QMessageBox.critical(self, "错误", error)

    def _open_output_dir(self):
        import subprocess
        from datetime import datetime
        from adflow.config_loader import config
        folder = os.path.join(config.output_dir, datetime.now().strftime("%m%d"))
        if not os.path.exists(folder):
            os.makedirs(folder, exist_ok=True)
        subprocess.Popen(["explorer", folder])

    def _on_pick_audio(self):
        """浏览配音文件（视频文件自动抽音轨，直接用爆款原声）"""
        path, _ = QFileDialog.getOpenFileName(
            self, "选择配音/视频文件", "",
            "音频和视频 (*.mp3 *.wav *.m4a *.aac *.mp4 *.mov *.mkv *.avi *.webm);;"
            "音频文件 (*.mp3 *.wav *.m4a);;视频文件 (*.mp4 *.mov *.mkv *.avi);;所有文件 (*.*)")
        if not path:
            return
        if os.path.splitext(path)[1].lower() in _VIDEO_EXTS:
            # 视频文件 → ffmpeg 抽音轨成 mp3 再用（混剪引擎按纯音频处理配音）
            self.status_label.setText("正在抽取视频音轨...")
            audio_path = self._extract_audio(path)
            if not audio_path:
                self.status_label.setText("就绪")
                QMessageBox.warning(self, "抽音轨失败",
                                    f"无法从视频提取音轨：\n{path}")
                return
            self._custom_audio_path = audio_path
            self.audio_path_label.setText(
                f"{os.path.basename(path)}（已抽音轨）")
            self.status_label.setText("就绪")
        else:
            self._custom_audio_path = path
            self.audio_path_label.setText(os.path.basename(path))

    @staticmethod
    def _extract_audio(video_path: str) -> str:
        """ffmpeg 抽视频音轨 → 临时 mp3（失败返回空串）"""
        try:
            from adflow.utils.ffmpeg_finder import get_ffmpeg_cmd
            out = os.path.join(
                tempfile.gettempdir(), f"adflow_remix_{int(time.time())}.mp3")
            cmd = [get_ffmpeg_cmd(), "-y", "-i", video_path,
                   "-vn", "-acodec", "libmp3lame", "-q:a", "4", out]
            subprocess.run(cmd, capture_output=True, timeout=300)
            return out if os.path.exists(out) and os.path.getsize(out) > 0 else ""
        except Exception:
            return ""
