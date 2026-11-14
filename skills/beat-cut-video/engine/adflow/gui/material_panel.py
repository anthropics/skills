"""
素材库管理面板
- 素材导入（文件对话框 + 拖拽）
- 素材列表表格展示
- 标签编辑（预留）
"""

import os
import shutil
import logging
from datetime import datetime
from fractions import Fraction

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QTableWidget,
    QTableWidgetItem, QHeaderView, QFileDialog, QMessageBox,
    QLabel, QLineEdit, QProgressBar, QAbstractItemView,
    QDialog, QFormLayout, QDialogButtonBox, QComboBox, QCheckBox,
    QSpinBox,
)
from PyQt6.QtCore import Qt, QThread, pyqtSignal

from adflow.config_loader import config
from adflow.models import MaterialRecord
from adflow.db.material_repo import MaterialRepo


class MaterialImportWorker(QThread):
    """后台线程：批量导入素材文件"""
    progress = pyqtSignal(int)          # 当前进度 (0-100)
    done = pyqtSignal(int, int, str)    # (成功数, 失败数, 最后错误摘要)
    status_msg = pyqtSignal(str)         # 状态消息

    def __init__(self, file_paths: list[str]):
        super().__init__()
        self.file_paths = file_paths
        self._logger = logging.getLogger("adflow.import")

    def run(self) -> None:
        repo = MaterialRepo()
        materials_dir = config.materials_dir
        os.makedirs(materials_dir, exist_ok=True)

        success = 0
        failed = 0
        total = len(self.file_paths)
        errors: list[str] = []

        for i, src_path in enumerate(self.file_paths):
            try:
                # 跳过非视频文件
                ext = os.path.splitext(src_path)[1].lower()
                if ext not in (".mp4", ".mov", ".avi", ".mkv", ".webm", ".m4v", ".flv"):
                    failed += 1
                    msg = f"跳过非视频文件: {os.path.basename(src_path)} (格式: {ext})"
                    self.status_msg.emit(msg)
                    self._logger.warning(msg)
                    errors.append(msg)
                    continue

                # MD5 去重
                md5 = MaterialRepo.compute_md5(src_path)
                if existing := repo.get_by_md5(md5):
                    failed += 1
                    msg = f"重复素材，跳过: {os.path.basename(src_path)} (已存在MD5: {md5[:12]}...)"
                    self.status_msg.emit(msg)
                    self._logger.info(msg)
                    errors.append(msg)
                    continue

                # 复制到素材目录
                filename = f"{md5[:8]}_{os.path.basename(src_path)}"
                dest_path = os.path.join(materials_dir, filename)
                if not os.path.exists(dest_path):
                    shutil.copy2(src_path, dest_path)

                # 创建素材记录
                material = MaterialRecord(
                    file_path=dest_path,
                    original_filename=os.path.basename(src_path),
                    file_size_bytes=os.path.getsize(src_path),
                    md5_hash=md5,
                    source_project="手动导入",
                    imported_at=datetime.now().isoformat(),
                )

                # 尝试用 FFprobe 获取视频信息
                try:
                    self._probe_video(material)
                except Exception:
                    pass  # 非致命，保留默认值

                # 方向分类（竖屏/横屏/手机横拍竖看，只用元数据，毫秒级）
                try:
                    from adflow.engine.video_orientation import classify_orientation
                    material.orientation = classify_orientation(material.file_path)
                except Exception:
                    material.orientation = "unknown"

                repo.insert(material)
                success += 1
                msg = f"已导入: {material.original_filename}"
                self.status_msg.emit(msg)
                self._logger.info(msg)

            except Exception as e:
                failed += 1
                msg = f"导入失败: {os.path.basename(src_path)} — {e}"
                self.status_msg.emit(msg)
                self._logger.error(msg, exc_info=True)
                errors.append(msg)

            self.progress.emit(int((i + 1) / total * 100))

        # 汇总最后几条错误给完成信号
        error_summary = "\n".join(errors[-5:]) if errors else ""
        self.done.emit(success, failed, error_summary)

    @staticmethod
    def _probe_video(material: MaterialRecord) -> None:
        """调用 FFprobe 提取视频元信息"""
        import subprocess
        import json

        from adflow.utils.ffmpeg_finder import get_ffprobe_cmd
        cmd = [
            get_ffprobe_cmd(), "-v", "quiet", "-print_format", "json",
            "-show_format", "-show_streams", material.file_path,
        ]
        result = subprocess.run(cmd, capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=30)
        data = json.loads(result.stdout)

        # 查找视频流
        for stream in data.get("streams", []):
            if stream["codec_type"] == "video":
                material.duration_ms = int(float(stream.get("duration", 0)) * 1000)
                material.fps = float(Fraction(stream.get("r_frame_rate", "30/1")))
                material.width = stream.get("width", 1080)
                material.height = stream.get("height", 1920)
                break

        # 文件大小
        if fmt := data.get("format"):
            material.duration_ms = material.duration_ms or int(float(fmt.get("duration", 0)) * 1000)
            material.file_size_bytes = int(fmt.get("size", 0))


class OrientationBackfillWorker(QThread):
    """后台线程：给老库里 orientation=unknown 的素材补算方向（导入旧版本时没算过）"""
    progress = pyqtSignal(int)
    done = pyqtSignal(int, int)   # (更新数, 跳过数)

    def __init__(self, items: list[tuple[str, str]]):
        super().__init__()
        self.items = items  # [(material_id, file_path), ...]

    def run(self) -> None:
        from adflow.engine.video_orientation import classify_orientation
        repo = MaterialRepo()
        updates: list[tuple[str, str]] = []
        skipped = 0
        total = max(len(self.items), 1)
        for i, (mid, fp) in enumerate(self.items):
            try:
                if os.path.exists(fp):
                    updates.append((classify_orientation(fp), mid))
                else:
                    skipped += 1  # 文件已不在磁盘上，保持 unknown（匹配时永远跳过）
            except Exception:
                skipped += 1
            self.progress.emit(int((i + 1) / total * 100))
        repo.set_orientation_batch(updates)
        self.done.emit(len(updates), skipped)


class MaterialPanel(QWidget):
    """素材库管理面板"""

    def __init__(self):
        super().__init__()
        self.repo = MaterialRepo()
        self._materials: list[MaterialRecord] = []  # 当前列表缓存

        # 主布局
        layout = QVBoxLayout(self)

        # ---- 工具栏 ----
        toolbar = QHBoxLayout()

        self.btn_import = QPushButton("📥 导入素材")
        self.btn_import.clicked.connect(self.import_materials)
        toolbar.addWidget(self.btn_import)

        self.btn_refresh = QPushButton("🔄 刷新")
        self.btn_refresh.clicked.connect(self.refresh_list)
        toolbar.addWidget(self.btn_refresh)

        self.btn_orientation = QPushButton("🧭 补算方向")
        self.btn_orientation.clicked.connect(self._backfill_orientation)
        self.btn_orientation.setToolTip(
            "旧素材补算横竖屏方向（混剪时按画幅跳过不匹配素材；识别不出的直接跳过）")
        toolbar.addWidget(self.btn_orientation)

        self.btn_edit_tags = QPushButton("🏷 编辑标签")
        self.btn_edit_tags.clicked.connect(self._edit_tags)
        toolbar.addWidget(self.btn_edit_tags)

        self.btn_auto_tag = QPushButton("🤖 AI 打标")
        self.btn_auto_tag.clicked.connect(self._auto_tag_selected)
        self.btn_auto_tag.setToolTip("使用 AI 视觉模型自动分析选中的素材")
        toolbar.addWidget(self.btn_auto_tag)

        # 分隔
        sep = QLabel("│")
        sep.setStyleSheet("color: #ccc; font-size: 14px;")
        toolbar.addWidget(sep)

        self.btn_remove = QPushButton("🗑 移除选中")
        self.btn_remove.clicked.connect(self._remove_selected)
        self.btn_remove.setToolTip("从素材库中移除选中的素材（不删除原文件）")
        toolbar.addWidget(self.btn_remove)

        self.btn_clear = QPushButton("⚠ 清空全部")
        self.btn_clear.clicked.connect(self._clear_all)
        self.btn_clear.setToolTip("清空素材库中的所有素材记录")
        self.btn_clear.setStyleSheet("QPushButton { color: #cc0000; } QPushButton:hover { color: white; background-color: #cc0000; }")
        toolbar.addWidget(self.btn_clear)

        toolbar.addStretch()

        self.search_input = QLineEdit()
        self.search_input.setPlaceholderText("搜索标签...")
        self.search_input.setFixedWidth(250)
        self.search_input.returnPressed.connect(self._on_search)
        toolbar.addWidget(self.search_input)

        self.btn_search = QPushButton("搜索")
        self.btn_search.clicked.connect(self._on_search)
        toolbar.addWidget(self.btn_search)

        layout.addLayout(toolbar)

        # ---- 进度条 ----
        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        layout.addWidget(self.progress_bar)

        # ---- 状态标签 ----
        self.status_label = QLabel("就绪")
        self.status_label.setStyleSheet("color: #666;")
        layout.addWidget(self.status_label)

        # ---- 素材表格 ----
        self.table = QTableWidget()
        self.table.setColumnCount(11)
        self.table.setHorizontalHeaderLabels([
            "文件名", "时长(s)", "分辨率/方向", "场景", "景别", "情绪",
            "产品露出", "质量分", "表现分", "使用次数", "导入时间",
        ])
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.horizontalHeader().setSectionResizeMode(QHeaderView.ResizeMode.ResizeToContents)
        self.table.setSelectionBehavior(QAbstractItemView.SelectionBehavior.SelectRows)
        self.table.setEditTriggers(QAbstractItemView.EditTrigger.NoEditTriggers)
        self.table.setAlternatingRowColors(True)
        self.table.doubleClicked.connect(self._on_material_double_click)
        layout.addWidget(self.table)

        # 初始加载
        self.refresh_list()

        # 拖拽支持
        self.setAcceptDrops(True)

    # ---- 素材导入 ----

    def import_materials(self) -> None:
        """打开文件对话框选择素材"""
        files, _ = QFileDialog.getOpenFileNames(
            self, "选择素材文件",
            "",
            "视频文件 (*.mp4 *.mov *.avi *.mkv *.webm *.m4v *.flv);;所有文件 (*.*)",
        )
        if files:
            self._start_import(files)

    def _start_import(self, file_paths: list[str]) -> None:
        """启动后台导入线程"""
        self.btn_import.setEnabled(False)
        self.progress_bar.setVisible(True)
        self.progress_bar.setValue(0)

        self.worker = MaterialImportWorker(file_paths)
        self.worker.progress.connect(self.progress_bar.setValue)
        self.worker.status_msg.connect(self.status_label.setText)
        self.worker.done.connect(self._on_import_finished)
        self.worker.finished.connect(self.worker.deleteLater)
        self.worker.start()

    def _on_import_finished(self, success: int, failed: int, errors: str = "") -> None:
        """导入完成回调"""
        self.btn_import.setEnabled(True)
        self.progress_bar.setVisible(False)
        msg = f"导入完成: 成功 {success} 条, 失败/跳过 {failed} 条"
        if errors:
            msg += f"\n最后错误: {errors.split(chr(10))[-1] if errors else ''}"
        self.status_label.setText(msg)
        # 如果全部失败，弹窗显示详情
        if success == 0 and failed > 0 and errors:
            QMessageBox.warning(
                self, "导入失败详情",
                f"全部 {failed} 个文件导入失败:\n\n{errors}"
            )
        self.refresh_list()

    def _backfill_orientation(self) -> None:
        """给老库里 orientation=unknown 的素材补算方向"""
        items = [(m.material_id, m.file_path)
                 for m in self.repo.get_all(limit=0)
                 if m.orientation == "unknown"]
        if not items:
            self.status_label.setText("没有待补算的素材（方向都已识别）")
            return
        self.btn_orientation.setEnabled(False)
        self.progress_bar.setVisible(True)
        self.progress_bar.setValue(0)
        self.status_label.setText(f"补算方向: 0/{len(items)}")
        self._ori_worker = OrientationBackfillWorker(items)
        self._ori_worker.progress.connect(
            lambda v: (
                self.progress_bar.setValue(v),
                self.status_label.setText(
                    f"补算方向: {int(v / 100 * len(items))}/{len(items)}"),
            ))
        self._ori_worker.done.connect(self._on_orientation_done)
        self._ori_worker.finished.connect(self._ori_worker.deleteLater)
        self._ori_worker.start()

    def _on_orientation_done(self, updated: int, skipped: int) -> None:
        """补算完成回调"""
        self.btn_orientation.setEnabled(True)
        self.progress_bar.setVisible(False)
        self.status_label.setText(
            f"方向补算完成: 更新 {updated} 条, 跳过 {skipped} 条（文件缺失或识别失败）")
        self.refresh_list()

    # ---- 素材列表 ----

    def refresh_list(self) -> None:
        """刷新素材列表"""
        self._materials = self.repo.get_all(limit=500)
        self.table.setRowCount(len(self._materials))

        for row, mat in enumerate(self._materials):
            item0 = QTableWidgetItem(mat.original_filename)
            item0.setData(Qt.ItemDataRole.UserRole, mat.material_id)
            self.table.setItem(row, 0, item0)
            self.table.setItem(row, 1, QTableWidgetItem(f"{mat.duration_ms / 1000:.1f}"))
            ori_label = {"vertical": "竖", "landscape": "横",
                         "phone_rotated": "横拍竖看", "unknown": "未知"}.get(
                             mat.orientation, "未知")
            self.table.setItem(row, 2, QTableWidgetItem(
                f"{mat.width}x{mat.height} {ori_label}"))
            self.table.setItem(row, 3, QTableWidgetItem(mat.scene or "-"))
            self.table.setItem(row, 4, QTableWidgetItem(mat.shot_type or "-"))
            self.table.setItem(row, 5, QTableWidgetItem(mat.emotion or "-"))
            self.table.setItem(row, 6, QTableWidgetItem(mat.product_visibility or "-"))
            self.table.setItem(row, 7, QTableWidgetItem(f"{mat.auto_quality_score:.0f}"))
            self.table.setItem(row, 8, QTableWidgetItem(f"{mat.performance_score:.1f}"))
            self.table.setItem(row, 9, QTableWidgetItem(str(mat.use_count_total)))
            self.table.setItem(row, 10, QTableWidgetItem(mat.imported_at[:16] if mat.imported_at else "-"))

            # 低质量素材标红
            if mat.auto_quality_score < 30:
                for col in range(self.table.columnCount()):
                    item = self.table.item(row, col)
                    if item:
                        item.setForeground(Qt.GlobalColor.red)

    # ---- 行 → 素材反查（不受搜索过滤影响）----

    def _material_id_at_row(self, row: int) -> str:
        """从表格行第一列的 UserRole 取 material_id（全量/搜索通用，避免行号错位）"""
        item = self.table.item(row, 0)
        return (item.data(Qt.ItemDataRole.UserRole) if item else "") or ""

    def _material_by_row(self, row: int) -> MaterialRecord | None:
        """按表格行反查素材对象"""
        mid = self._material_id_at_row(row)
        return self.repo.get_by_id(mid) if mid else None

    # ---- 删除操作 ----

    def _remove_selected(self) -> None:
        """移除选中的素材"""
        rows = set()
        for idx in self.table.selectedIndexes():
            rows.add(idx.row())

        if not rows:
            QMessageBox.information(self, "提示", "请先在表格中选择要移除的素材")
            return

        reply = QMessageBox.question(
            self, "确认移除",
            f"确定要移除选中的 {len(rows)} 个素材吗？\n（仅删除数据库记录，不删除原文件）",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
        )
        if reply != QMessageBox.StandardButton.Yes:
            return

        removed = 0
        for row in rows:
            mat = self._material_by_row(row)
            if mat is None:
                continue
            try:
                self.repo.delete(mat.material_id)
                removed += 1
            except Exception as e:
                QMessageBox.warning(self, "删除失败", f"无法删除 {mat.original_filename}:\n{e}")

        self.status_label.setText(f"已移除 {removed} 个素材")
        self.refresh_list()

    def _clear_all(self) -> None:
        """清空全部素材"""
        count = self.repo.count()
        if count == 0:
            QMessageBox.information(self, "提示", "素材库已经是空的")
            return

        reply = QMessageBox.warning(
            self, "⚠ 确认清空",
            f"确定要清空素材库中的全部 {count} 个素材记录吗？\n\n"
            "此操作仅删除数据库记录，不会删除原文件。\n"
            "清空后 AI 出片将无法匹配素材！",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
            QMessageBox.StandardButton.No,
        )
        if reply != QMessageBox.StandardButton.Yes:
            return

        try:
            self.repo.delete_all()
            self.status_label.setText(f"已清空全部 {count} 个素材")
            self.refresh_list()
        except Exception as e:
            QMessageBox.critical(self, "清空失败", str(e))

    # ---- 搜索 ----

    def _on_search(self) -> None:
        """按标签搜索素材"""
        query = self.search_input.text().strip()
        if not query:
            self.refresh_list()
            return

        tags = [t.strip() for t in query.split(",") if t.strip()]
        materials = self.repo.search_by_tags(tags, limit=200)

        self.table.setRowCount(len(materials))
        for row, mat in enumerate(materials):
            item0 = QTableWidgetItem(mat.original_filename)
            item0.setData(Qt.ItemDataRole.UserRole, mat.material_id)
            self.table.setItem(row, 0, item0)
            self.table.setItem(row, 1, QTableWidgetItem(f"{mat.duration_ms / 1000:.1f}"))
            ori_label = {"vertical": "竖", "landscape": "横",
                         "phone_rotated": "横拍竖看", "unknown": "未知"}.get(
                             mat.orientation, "未知")
            self.table.setItem(row, 2, QTableWidgetItem(
                f"{mat.width}x{mat.height} {ori_label}"))
            self.table.setItem(row, 3, QTableWidgetItem(mat.scene or "-"))
            self.table.setItem(row, 4, QTableWidgetItem(mat.shot_type or "-"))
            self.table.setItem(row, 5, QTableWidgetItem(mat.emotion or "-"))
            self.table.setItem(row, 6, QTableWidgetItem(mat.product_visibility or "-"))
            self.table.setItem(row, 7, QTableWidgetItem(f"{mat.auto_quality_score:.0f}"))
            self.table.setItem(row, 8, QTableWidgetItem(f"{mat.performance_score:.1f}"))
            self.table.setItem(row, 9, QTableWidgetItem(str(mat.use_count_total)))
            self.table.setItem(row, 10, QTableWidgetItem(mat.imported_at[:16] if mat.imported_at else "-"))

        self.status_label.setText(f"搜索 [{query}] — 找到 {len(materials)} 条结果")

    # ---- 双击查看详情 ----

    def _on_material_double_click(self, index) -> None:
        """双击素材行查看详情"""
        row = index.row()
        mat = self._material_by_row(row)
        if mat is not None:
            QMessageBox.information(
                self, f"素材详情 — {mat.original_filename}",
                f"文件路径: {mat.file_path}\n"
                f"时长: {mat.duration_ms / 1000:.1f}s\n"
                f"分辨率: {mat.width}x{mat.height} @ {mat.fps}fps\n"
                f"大小: {mat.file_size_bytes / 1024 / 1024:.1f} MB\n"
                f"场景: {mat.scene or '-'}\n"
                f"景别: {mat.shot_type or '-'}\n"
                f"运镜: {mat.camera_movement or '-'}\n"
                f"情绪: {mat.emotion or '-'}\n"
                f"产品露出: {mat.product_visibility or '-'}\n"
                f"节奏: {mat.pace or '-'}\n"
                f"质量分: {mat.auto_quality_score:.0f} | 表现分: {mat.performance_score:.1f}\n"
                f"使用次数: {mat.use_count_total} (近30天: {mat.use_count_30d})\n"
                f"标签: {mat.tags}"
            )

    # ---- 标签编辑 ----

    def _edit_tags(self) -> None:
        """打开选中素材的标签编辑对话框"""
        rows = set(idx.row() for idx in self.table.selectedIndexes())
        if not rows:
            QMessageBox.information(self, "提示", "请先在表格中选中一个素材")
            return

        row = list(rows)[0]
        mat = self._material_by_row(row)
        if mat is None:
            return

        dialog = TagEditDialog(mat, self)
        if dialog.exec() == QDialog.DialogCode.Accepted:
            self.refresh_list()
            self.status_label.setText(f"标签已更新: {mat.original_filename}")

    def _auto_tag_selected(self) -> None:
        """对选中的素材批量执行 AI 自动打标（支持多选 + 进度显示）"""
        from PyQt6.QtWidgets import QProgressBar, QApplication

        rows = sorted(set(idx.row() for idx in self.table.selectedIndexes()))
        if not rows:
            QMessageBox.information(self, "提示", "请先在表格中选中素材（可多选）")
            return

        # 收集有效素材
        materials = []
        for row in rows:
            mat = self._material_by_row(row)
            if mat is not None:
                materials.append(mat)
        if not materials:
            return

        n = len(materials)
        reply = QMessageBox.question(
            self, "确认 AI 打标",
            f"将对 {n} 个素材使用 AI 视觉模型自动打标。\n"
            f"预计消耗约 {n} 次 API 调用，是否继续？",
            QMessageBox.StandardButton.Yes | QMessageBox.StandardButton.No,
        )
        if reply != QMessageBox.StandardButton.Yes:
            return

        self.btn_auto_tag.setEnabled(False)

        # 显示进度条
        progress = QProgressBar()
        progress.setRange(0, n)
        progress.setVisible(True)
        # 把进度条塞到状态区域（替换 status_label 位置）
        old_status_text = self.status_label.text()
        self.status_label.hide()

        from adflow.tagger.auto_tagger import tag_material_sync

        done, failed = 0, 0
        errors = []

        for i, mat in enumerate(materials):
            pct = int((i + 1) / n * 100)
            progress.setValue(i + 1)
            self.status_label.setText(
                f"AI打标 {i+1}/{n} ({pct}%) — {mat.original_filename[:30]}..."
            )
            self.status_label.show()
            QApplication.processEvents()  # 刷新UI

            try:
                tag_material_sync(mat.material_id, mat.file_path)
                done += 1
            except Exception as e:
                failed += 1
                errors.append(f"{mat.original_filename[:30]}: {e}")

        # 清理进度条，恢复状态
        self.status_label.setText(
            f"AI 打标完成: {done}成功 {failed}失败"
            + (f" | {'; '.join(errors[:2])}" if errors else "")
        )
        self.btn_auto_tag.setEnabled(True)
        self.refresh_list()

        if failed > 0:
            QMessageBox.warning(
                self, "部分失败",
                f"{done}/{n} 成功, {failed} 失败\n\n"
                + "\n".join(errors[:5])
            )

    # ---- 拖拽导入 ----

    def dragEnterEvent(self, event):
        if event.mimeData().hasUrls():
            event.acceptProposedAction()

    def dropEvent(self, event):
        files = []
        for url in event.mimeData().urls():
            path = url.toLocalFile()
            if os.path.isfile(path):
                files.append(path)
        if files:
            self._start_import(files)


# ============================================================
# 标签编辑对话框
# ============================================================

class TagEditDialog(QDialog):
    """素材标签编辑对话框（中文显示）"""

    # ── 英文值→中文名映射 ──
    _CN = {
        # 场景
        "indoor_studio": "室内影棚", "indoor_home": "室内家居",
        "indoor_office": "室内办公", "indoor_kitchen": "室内厨房",
        "indoor_bathroom": "室内浴室", "indoor_store": "室内店铺",
        "indoor_gym": "室内健身房", "indoor_other": "室内其他",
        "outdoor_street": "室外街景", "outdoor_nature": "室外自然",
        "outdoor_urban": "室外城市", "green_screen": "绿幕",
        # 景别
        "extreme_closeup": "大特写", "closeup": "特写",
        "medium_closeup": "近景", "medium": "中景",
        "medium_wide": "中全景", "wide": "全景", "extreme_wide": "远景",
        # 运镜
        "static": "固定", "pan": "横摇", "tilt": "竖摇",
        "zoom_in": "推近", "zoom_out": "拉远",
        "tracking": "跟拍", "handheld": "手持", "aerial": "航拍",
        # 情绪
        "neutral": "中性", "excited": "激动", "happy": "开心",
        "calm": "平静", "serious": "严肃", "urgent": "紧迫",
        "curious": "好奇", "trust": "信任", "surprise": "惊讶", "anxious": "焦虑",
        # 产品露出
        "none": "无产品", "partial": "部分露出", "full": "完整露出",
        "packaging": "包装展示", "usage": "使用场景",
        "before_after": "前后对比", "text_logo": "文字Logo",
        # 人物身份
        "no_person": "无人物", "host": "主播", "customer": "顾客",
        "expert": "专家", "actor": "演员",
        # 光线
        "natural": "自然光", "studio": "影棚光", "bright": "明亮",
        "dim": "昏暗", "backlit": "逆光", "warm": "暖色调",
        "cool": "冷色调", "high_contrast": "高对比",
        # 节奏
        "medium": "中速", "fast": "快节奏", "slow": "慢节奏",
        # 质量
        "clean": "清晰", "blurry": "模糊", "shaky": "抖动",
        "overexposed": "过曝", "underexposed": "欠曝",
        "noisy": "噪点", "watermark": "有水印",
        # 素材类型
        "product_shoot": "产品拍摄", "scenario_shoot": "场景拍摄",
        "ugc_style": "UGC风格", "stock_footage": "素材库",
        "screen_record": "录屏", "animation": "动画", "text_card": "文字卡片",
    }

    # ── 中文显示列表(第一个是"未知") ──
    @classmethod
    def _cn_items(cls, values: list[str]) -> list[str]:
        """英文值列表 → 中文显示列表"""
        result = ["未知"] if "" in values else []
        for v in values:
            if v:
                result.append(cls._CN.get(v, v))
        return result

    @classmethod
    def _cn_to_en(cls, cn_text: str, values: list[str]) -> str:
        """中文显示 → 英文值（反向查找）"""
        for v in values:
            if cls._CN.get(v, v) == cn_text:
                return v
        return values[0] if values else ""

    def __init__(self, material: MaterialRecord, parent=None):
        super().__init__(parent)
        self.material = material
        self.setWindowTitle(f"编辑标签 — {material.original_filename}")
        self.setMinimumWidth(520)

        layout = QFormLayout(self)

        # 所有可选值列表（英文原值，供保存时反向查找）
        _SC = ["", "indoor_studio","indoor_home","indoor_office","indoor_kitchen",
               "indoor_bathroom","indoor_store","indoor_gym","indoor_other",
               "outdoor_street","outdoor_nature","outdoor_urban","green_screen"]
        _SH = ["", "extreme_closeup","closeup","medium_closeup","medium",
               "medium_wide","wide","extreme_wide"]
        _CM = ["", "static","pan","tilt","zoom_in","zoom_out","tracking","handheld","aerial"]
        _EM = ["neutral","excited","happy","calm","serious","urgent",
               "curious","trust","surprise","anxious"]
        _PV = ["none","partial","full","packaging","usage","before_after","text_logo"]
        _PR = ["no_person","host","customer","expert","actor"]
        _LI = ["", "natural","studio","bright","dim","backlit","warm","cool","high_contrast"]
        _PA = ["medium","fast","slow"]
        _QF = ["clean","blurry","shaky","overexposed","underexposed","noisy","watermark"]
        _MC = ["", "product_shoot","scenario_shoot","ugc_style",
               "stock_footage","screen_record","animation","text_card"]

        # 场景
        self.cb_scene = QComboBox()
        self.cb_scene.addItems(self._cn_items(_SC))
        cur = self._CN.get(material.scene, material.scene or "未知")
        self.cb_scene.setCurrentText(cur)
        self._scene_vals = _SC
        layout.addRow("场景:", self.cb_scene)

        # 景别
        self.cb_shot = QComboBox()
        self.cb_shot.addItems(self._cn_items(_SH))
        self.cb_shot.setCurrentText(self._CN.get(material.shot_type, material.shot_type or "未知"))
        self._shot_vals = _SH
        layout.addRow("景别:", self.cb_shot)

        # 运镜
        self.cb_camera = QComboBox()
        self.cb_camera.addItems(self._cn_items(_CM))
        self.cb_camera.setCurrentText(self._CN.get(material.camera_movement, material.camera_movement or "未知"))
        self._camera_vals = _CM
        layout.addRow("运镜:", self.cb_camera)

        # 情绪
        self.cb_emotion = QComboBox()
        self.cb_emotion.addItems(self._cn_items(_EM))
        self.cb_emotion.setCurrentText(self._CN.get(material.emotion, material.emotion or "中性"))
        self._emotion_vals = _EM
        layout.addRow("情绪:", self.cb_emotion)

        # 产品露出
        self.cb_product_vis = QComboBox()
        self.cb_product_vis.addItems(self._cn_items(_PV))
        self.cb_product_vis.setCurrentText(
            self._CN.get(material.product_visibility, material.product_visibility or "无产品"))
        self._product_vis_vals = _PV
        layout.addRow("产品露出:", self.cb_product_vis)

        # 有人物
        self.chk_has_person = QCheckBox()
        self.chk_has_person.setChecked(material.has_person)
        layout.addRow("有人物:", self.chk_has_person)

        # 人物数量
        self.spin_person_count = QSpinBox()
        self.spin_person_count.setRange(0, 20)
        self.spin_person_count.setValue(material.person_count)
        layout.addRow("人物数量:", self.spin_person_count)

        # 人物身份
        self.cb_person_role = QComboBox()
        self.cb_person_role.addItems(self._cn_items(_PR))
        self.cb_person_role.setCurrentText(
            self._CN.get(material.person_role, material.person_role or "无人物"))
        self._person_role_vals = _PR
        layout.addRow("人物身份:", self.cb_person_role)

        # 光线
        self.cb_lighting = QComboBox()
        self.cb_lighting.addItems(self._cn_items(_LI))
        self.cb_lighting.setCurrentText(self._CN.get(material.lighting, material.lighting or "未知"))
        self._lighting_vals = _LI
        layout.addRow("光线:", self.cb_lighting)

        # 节奏
        self.cb_pace = QComboBox()
        self.cb_pace.addItems(self._cn_items(_PA))
        self.cb_pace.setCurrentText(self._CN.get(material.pace, material.pace or "中速"))
        self._pace_vals = _PA
        layout.addRow("节奏:", self.cb_pace)

        # 质量标记
        self.cb_quality = QComboBox()
        self.cb_quality.addItems(self._cn_items(_QF))
        self.cb_quality.setCurrentText(self._CN.get(material.quality_flags, material.quality_flags or "清晰"))
        self._quality_vals = _QF
        layout.addRow("质量:", self.cb_quality)

        # 素材类型
        self.cb_category = QComboBox()
        self.cb_category.addItems(self._cn_items(_MC))
        self.cb_category.setCurrentText(
            self._CN.get(material.material_category, material.material_category or "未知"))
        self._category_vals = _MC
        layout.addRow("类型:", self.cb_category)

        # 自由标签
        self.edit_tags = QLineEdit()
        self.edit_tags.setText(material.tags.replace("[", "").replace("]", "").replace('"', ""))
        self.edit_tags.setPlaceholderText("逗号分隔，如：夏天, 美白, 护肤")
        layout.addRow("自由标签:", self.edit_tags)

        # 按钮
        buttons = QDialogButtonBox(
            QDialogButtonBox.StandardButton.Ok |
            QDialogButtonBox.StandardButton.Cancel
        )
        buttons.accepted.connect(self._save_and_accept)
        buttons.rejected.connect(self.reject)
        layout.addRow(buttons)

    def _save_and_accept(self) -> None:
        """保存标签到数据库"""
        from adflow.db.material_repo import MaterialRepo
        repo = MaterialRepo()

        # 中文显示 → 英文原值
        scene = self._cn_to_en(self.cb_scene.currentText(), self._scene_vals)
        shot = self._cn_to_en(self.cb_shot.currentText(), self._shot_vals)
        camera = self._cn_to_en(self.cb_camera.currentText(), self._camera_vals)
        emotion = self._cn_to_en(self.cb_emotion.currentText(), self._emotion_vals)
        product = self._cn_to_en(self.cb_product_vis.currentText(), self._product_vis_vals)
        person_role = self._cn_to_en(self.cb_person_role.currentText(), self._person_role_vals)
        lighting = self._cn_to_en(self.cb_lighting.currentText(), self._lighting_vals)
        pace = self._cn_to_en(self.cb_pace.currentText(), self._pace_vals)
        quality = self._cn_to_en(self.cb_quality.currentText(), self._quality_vals)
        category = self._cn_to_en(self.cb_category.currentText(), self._category_vals)

        repo = MaterialRepo()
        repo.update_auto_tags(
            self.material.material_id,
            scene=scene, shot_type=shot, camera_movement=camera,
            emotion=emotion, product_visibility=product,
            has_person=self.chk_has_person.isChecked(),
            person_count=str(self.spin_person_count.value()),
            person_role=person_role,
            lighting=lighting, pace=pace,
            quality_flags=quality, material_category=category,
        )

        # 自由标签
        tags_text = self.edit_tags.text().strip()
        if tags_text:
            tags = [t.strip() for t in tags_text.split(",") if t.strip()]
            repo.update_tags(self.material.material_id, tags)

        # 更新质量评分
        from adflow.tagger.quality_scorer import score_quality
        mat = repo.get_by_id(self.material.material_id)
        if mat:
            qr = score_quality(
                width=mat.width, height=mat.height,
                duration_ms=mat.duration_ms,
                has_audio=mat.has_bgm or mat.has_dialogue,
                quality_flags=self.cb_quality.currentText(),
            )
            repo.update_auto_tags(self.material.material_id, auto_quality_score=qr.total_score)

        self.accept()
