"""
任务管理面板 — AI Agent 全流程自动出片
- 输入产品信息 → 一键运行 Pipeline
- 显示执行进度和中间结果
- 查看历史任务和成品
"""

import json
import os
from datetime import datetime

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QLineEdit, QTextEdit, QSpinBox, QGroupBox, QFormLayout,
    QListWidget, QListWidgetItem, QMessageBox, QProgressBar,
    QAbstractItemView, QFileDialog, QComboBox, QCheckBox,
)
from PyQt6.QtCore import Qt, QThread, pyqtSignal

from adflow.config_loader import config
from adflow.models import ProductProfile
from adflow.db.project_repo import ProjectRepo
from adflow.db.material_repo import MaterialRepo
from adflow.agents.pipeline import AdPipeline, PipelineResult, PipelineCancelled


class PipelineWorker(QThread):
    """后台线程：执行 Pipeline（分两阶段：生成→审核→混剪）"""
    progress = pyqtSignal(str)
    review_ready = pyqtSignal(str)      # 文案已生成，需要审核
    done = pyqtSignal(object)           # PipelineResult
    error = pyqtSignal(str)
    cancelled = pyqtSignal()            # 用户主动停止

    def __init__(
        self,
        product_name: str,
        category: str,
        selling_points: list[str],
        target_audience: str,
        pain_points: list[str],
        platform: str,
        variant_count: int,
        style_name: str = "",
        ref_hit_ids: list[str] | None = None,
        custom_text: str = "",
        name_prefix: str = "",
        low_quality_rules=None,
        aspect_ratio: str = "portrait",
    ):
        super().__init__()
        self.product_name = product_name
        self.category = category
        self.selling_points = selling_points
        self.target_audience = target_audience
        self.pain_points = pain_points
        self.platform = platform
        self.variant_count = variant_count
        self.style_name = style_name
        self.ref_hit_ids = ref_hit_ids or []
        self.custom_text = custom_text
        self.name_prefix = name_prefix
        self.low_quality_rules = low_quality_rules
        self.aspect_ratio = aspect_ratio
        self._review_approved = False
        self._review_params = {}
        self._edited_text = ""
        self._cancelled = False

    def approve(self, params: dict):
        """审核通过，继续混剪"""
        self._review_approved = True
        self._review_params = params
        # 用户编辑了文案 → 存下来
        self._edited_text = params.get("edited_text", "")

    def cancel(self) -> None:
        """协作式取消：让阻塞中的审核/时间轴回调退出，线程自然结束（不用 terminate()）"""
        self._cancelled = True

    def run(self) -> None:
        try:
            pipeline = AdPipeline()
            product = ProductProfile(
                name=self.product_name,
                category=self.category,
                key_selling_points=json.dumps(self.selling_points, ensure_ascii=False),
                target_audience=self.target_audience,
                pain_points=json.dumps(self.pain_points, ensure_ascii=False),
                brand_tone="亲切口语",
            )

            # 审核回调
            def review_callback(script_text: str) -> bool:
                self.review_ready.emit(script_text)
                self._review_approved = False
                while not self._review_approved and not self._cancelled:
                    self.msleep(200)
                if self._cancelled:
                    return False
                review_callback.params = dict(self._review_params)
                return True
            review_callback.params = {}

            # 时间轴编辑已删除（2026-10-17 小白化）。
            # 音色/语速/手改文案不再在调用时提前求值（审核弹窗弹出前求值会传空），
            # 由 pipeline 在审核通过后从 review_callback.params 读取。

            result = pipeline.run(
                product=product,
                platform=self.platform,
                variant_count=self.variant_count,
                progress_callback=lambda msg: self.progress.emit(msg),
                style_name=self.style_name,
                ref_hit_ids=self.ref_hit_ids,
                review_callback=review_callback,
                custom_text=self.custom_text,
                name_prefix=self.name_prefix,
                low_quality_rules=self.low_quality_rules,
                aspect_ratio=self.aspect_ratio,
                should_cancel=lambda: self._cancelled,
            )
            if result.cancelled:
                self.cancelled.emit()
            elif not self._cancelled:
                self.done.emit(result)
        except PipelineCancelled:
            # 兜底：pipeline 理论上已在内部捕获并 return，此处防御未来改动
            self.cancelled.emit()
        except Exception as e:
            self.error.emit(str(e))


class ProjectPanel(QWidget):
    """任务管理面板"""

    def __init__(self):
        super().__init__()
        self.project_repo = ProjectRepo()
        self.material_repo = MaterialRepo()

        main_layout = QHBoxLayout(self)

        # ---- 左侧：新建任务表单 ----
        left = QWidget()
        left_layout = QVBoxLayout(left)
        left_layout.setContentsMargins(0, 0, 0, 0)

        # 产品信息
        product_group = QGroupBox("产品信息")
        product_form = QFormLayout(product_group)

        # 导入/导出按钮行
        io_layout = QHBoxLayout()
        self.btn_export = QPushButton("📤 导出配置")
        self.btn_export.setToolTip("将当前产品信息保存为 JSON 文件，下次可直接导入")
        self.btn_export.clicked.connect(self._export_config)
        io_layout.addWidget(self.btn_export)

        self.btn_import = QPushButton("📥 导入配置")
        self.btn_import.setToolTip("从之前导出的 JSON 文件加载产品信息")
        self.btn_import.clicked.connect(self._import_config)
        io_layout.addWidget(self.btn_import)
        io_layout.addStretch()
        product_form.addRow(io_layout)

        self.input_name = QLineEdit()
        self.input_name.setPlaceholderText("如：XX品牌无花果干")
        product_form.addRow("产品名称:", self.input_name)

        self.input_category = QLineEdit()
        self.input_category.setPlaceholderText("如：零食、护肤品")
        product_form.addRow("品类:", self.input_category)

        self.input_selling_points = QTextEdit()
        self.input_selling_points.setMaximumHeight(100)
        self.input_selling_points.setPlaceholderText(
            "产品优势（种子池，用来扩散不是限制）：\n"
            "· 卖点：高纤低糖、独立包装\n"
            "· 优惠：买一送一\n"
            "· 产地：新疆\n"
            "· 痛点：便秘、控糖\n"
            "· 竞品对比：比榴莲低糖40%")
        product_form.addRow("产品优势:", self.input_selling_points)

        # 使用人群/场景已删（2026-10-18 小白化：留空=不限，AI 自己扩展，无需手填）

        self.input_hit_text = QTextEdit()
        self.input_hit_text.setMaximumHeight(60)
        self.input_hit_text.setPlaceholderText(
            "爆款文案参考（目前跑得好的角度，可参考但不要照抄）：\n"
            "如：便秘人群的救星，吃2颗就通了"
        )
        product_form.addRow("爆款文案:", self.input_hit_text)

        left_layout.addWidget(product_group)

        # 投放设置
        deploy_group = QGroupBox("投放设置")
        deploy_form = QFormLayout(deploy_group)

        self.variant_count_label = QLabel("变体数量:")
        self.spin_variants = QSpinBox()
        self.spin_variants.setRange(1, 200)
        self.spin_variants.setValue(5)
        deploy_form.addRow(self.variant_count_label, self.spin_variants)

        # 风格模板下拉已删（2026-10-18 小白化：永远走 AI 自动，style_name 传空串）

        self.copy_mode_combo = QComboBox()
        self.copy_mode_combo.addItem("创造（从产品信息生成）", "create")
        self.copy_mode_combo.addItem("用爆款（直接用爆款文案）", "use_hit")
        self.copy_mode_combo.setCurrentIndex(1)  # 默认用爆款（2026-10-18：小白最常用）
        # 微改/仿写已下线（2026-10-17 小白化：代码路径保留，改回 addItem 即可恢复）
        deploy_form.addRow("文案裂变方式:", self.copy_mode_combo)
        self.copy_mode_combo.currentIndexChanged.connect(
            self._update_variant_count_label)
        self._update_variant_count_label()

        self.name_prefix_input = QLineEdit()
        self.name_prefix_input.setPlaceholderText("留空=默认日期命名；如「视频」→ 视频01/视频02…")
        deploy_form.addRow("视频命名前缀:", self.name_prefix_input)

        # ── 画幅（固定输出；混剪时自动跳过方向不匹配的素材）──
        self.aspect_combo = QComboBox()
        self.aspect_combo.addItem("竖屏 9:16（推荐）", "portrait")
        self.aspect_combo.addItem("横屏 16:9", "landscape")
        self.aspect_combo.setToolTip(
            "竖屏输出只用竖屏素材（横拍竖看的自动回正）；横屏素材默认跳过，不够时才拿来兜底")
        deploy_form.addRow("画幅:", self.aspect_combo)

        # ── 智能去重过滤（软排除，不删库；2026-10-17 三个细分勾选合并成一个默认开）──
        self.lq_filter_cb = QCheckBox("智能去重过滤（短镜头/重复镜头/画面相似）")
        self.lq_filter_cb.setChecked(True)
        self.lq_filter_cb.setToolTip(
            "出片时自动排除：<2.5s 短镜头、重复镜头（md5/场景组合）、画面相似镜头（pHash）")
        deploy_form.addRow(self.lq_filter_cb)

        # 预估视频数按钮已删（2026-10-18 小白化：出片时过滤照常生效，无需提前预估）

        left_layout.addWidget(deploy_group)

        # 素材库状态
        mat_label = QLabel(f"素材库: {self.material_repo.count()} 条可用素材")
        mat_label.setStyleSheet("color: #666; font-size: 12px;")
        left_layout.addWidget(mat_label)

        # 生成按钮
        self.btn_generate = QPushButton("🚀 启动 AI 自动出片")
        self.btn_generate.setStyleSheet("""
            QPushButton {
                background-color: #4a90d9; color: white;
                font-size: 16px; font-weight: bold;
                padding: 12px 24px; border-radius: 8px;
            }
            QPushButton:hover { background-color: #357abd; }
            QPushButton:disabled { background-color: #ccc; }
        """)
        self.btn_generate.clicked.connect(self._run_pipeline)
        left_layout.addWidget(self.btn_generate)

        # 停止按钮（出片过程中显示，点击协作式中断）
        self.btn_stop = QPushButton("⏹ 停止出片")
        self.btn_stop.setStyleSheet("""
            QPushButton {
                background-color: #d94a4a; color: white;
                font-size: 16px; font-weight: bold;
                padding: 12px 24px; border-radius: 8px;
            }
            QPushButton:hover { background-color: #bd3535; }
            QPushButton:disabled { background-color: #ccc; }
        """)
        self.btn_stop.setVisible(False)
        self.btn_stop.clicked.connect(self._on_stop)
        left_layout.addWidget(self.btn_stop)

        # 进度
        self.progress_bar = QProgressBar()
        self.progress_bar.setVisible(False)
        left_layout.addWidget(self.progress_bar)

        # 参考爆款按钮已删（2026-10-18 小白化：_ref_hit_ids 恒空列表，走纯 AI 生成）
        self._ref_hit_ids: list[str] = []

        self.status_label = QLabel("就绪")
        self.status_label.setStyleSheet("color: #666;")
        self.status_label.setWordWrap(True)  # 长进度文本换行，避免出片时撑宽窗口
        left_layout.addWidget(self.status_label)

        # 打开输出目录
        self.btn_open_output = QPushButton("📂 打开输出目录")
        self.btn_open_output.setToolTip("在资源管理器中打开 AI 出片的输出文件夹")
        self.btn_open_output.clicked.connect(self._open_output_dir)
        left_layout.addWidget(self.btn_open_output)

        left_layout.addStretch()
        self._last_task_id: str | None = None

        main_layout.addWidget(left)

        # ---- 右侧：任务历史 ----
        right = QWidget()
        right_layout = QVBoxLayout(right)
        right_layout.setContentsMargins(0, 0, 0, 0)

        right_layout.addWidget(QLabel("<b>任务历史</b>"))

        self.task_list = QListWidget()
        self.task_list.setSelectionMode(QAbstractItemView.SelectionMode.SingleSelection)
        self.task_list.doubleClicked.connect(self._on_task_double_click)
        right_layout.addWidget(self.task_list)

        btn_refresh = QPushButton("🔄 刷新")
        btn_refresh.clicked.connect(self._refresh_task_list)
        right_layout.addWidget(btn_refresh)

        main_layout.addWidget(right)
        main_layout.setStretchFactor(left, 3)
        main_layout.setStretchFactor(right, 2)

        # 初始加载
        self._refresh_task_list()

    # ---- 导入/导出配置 ----

    def _export_config(self) -> None:
        """将当前表单内容导出为 JSON 文件"""
        name = self.input_name.text().strip()
        if not name:
            QMessageBox.warning(self, "内容为空", "请至少填写产品名称后再导出")
            return

        data = {
            "product_name": name,
            "category": self.input_category.text().strip(),
            "selling_points": [
                s.strip() for s in self.input_selling_points.toPlainText().split("\n")
                if s.strip()
            ],
            "hit_text": [
                s.strip() for s in self.input_hit_text.toPlainText().split("\n")
                if s.strip()
            ],
            "variant_count": self.spin_variants.value(),
            "name_prefix": self.name_prefix_input.text().strip(),
            "aspect_ratio": self.aspect_combo.currentData(),
            "low_quality": {
                "enabled": self.lq_filter_cb.isChecked(),
            },
        }

        file_path, _ = QFileDialog.getSaveFileName(
            self, "导出产品配置",
            f"{name}.json",
            "JSON 文件 (*.json);;所有文件 (*.*)",
        )
        if not file_path:
            return

        with open(file_path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)

        self.status_label.setText(f"已导出: {file_path}")

    def _import_config(self) -> None:
        """从 JSON 文件加载产品配置"""
        file_path, _ = QFileDialog.getOpenFileName(
            self, "导入产品配置",
            "",
            "JSON 文件 (*.json);;所有文件 (*.*)",
        )
        if not file_path:
            return

        try:
            with open(file_path, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception as e:
            QMessageBox.critical(self, "导入失败", f"无法读取 JSON 文件:\n{e}")
            return

        # 填充表单
        self.input_name.setText(data.get("product_name", ""))
        self.input_category.setText(data.get("category", ""))
        self.input_selling_points.setPlainText(
            "\n".join(data.get("selling_points", []))
        )
        self.input_hit_text.setPlainText(
            "\n".join(data.get("hit_text", []))
        )
        if "variant_count" in data:
            self.spin_variants.setValue(data["variant_count"])
        self.name_prefix_input.setText(data.get("name_prefix", ""))
        _aspect = data.get("aspect_ratio", "portrait")
        idx = self.aspect_combo.findData(_aspect)
        if idx >= 0:
            self.aspect_combo.setCurrentIndex(idx)
        _lq = data.get("low_quality", {}) or {}
        # 兼容旧配置（细分勾选时代）：任一旧开关开启即视为开启
        _lq_enabled = _lq.get(
            "enabled",
            bool(_lq.get("exclude") or _lq.get("filter_short") or _lq.get("dedup")))
        self.lq_filter_cb.setChecked(_lq_enabled)

        self.status_label.setText(f"已导入: {os.path.basename(file_path)}")

    # ---- 执行 Pipeline ----
    # 预估视频数相关（_estimate_videos/_on_phash_progress/_on_estimate_done/
    # _on_estimate_error/PhashEstimateWorker）已删（2026-10-18 小白化）

    def _update_variant_count_label(self) -> None:
        """文案裂变方式切换时同步数量标签语义：用爆款=视频数量，其它=变体数量。"""
        if self.copy_mode_combo.currentData() == "use_hit":
            self.variant_count_label.setText("视频数量:")
            self.spin_variants.setToolTip(
                "文案固定为爆款原文，此数=出片条数（差异：配音男女交替 + 画面不重复）")
        else:
            self.variant_count_label.setText("变体数量:")
            self.spin_variants.setToolTip("生成几份不同文案")

    def _run_pipeline(self) -> None:
        """启动 AI 自动出片"""
        # 验证输入
        name = self.input_name.text().strip()
        if not name:
            QMessageBox.warning(self, "输入不完整", "请输入产品名称")
            return

        if self.material_repo.count() == 0:
            QMessageBox.warning(self, "无素材", "请先在素材库中导入素材")
            return

        category = self.input_category.text().strip()
        selling_points = [
            s.strip() for s in self.input_selling_points.toPlainText().split("\n")
            if s.strip()
        ]
        audience = ""  # 人群字段已删（2026-10-18），空=不限，AI 自行扩展
        pain_points = [
            s.strip() for s in self.input_hit_text.toPlainText().split("\n")
            if s.strip()
        ]
        platform = "ocean_engine"
        variant_count = self.spin_variants.value()
        name_prefix = self.name_prefix_input.text().strip()

        # ── 智能去重过滤（勾选=三条规则全开；未勾选 → None=不过滤）──
        low_quality_rules = None
        if self.lq_filter_cb.isChecked():
            from adflow.engine.low_quality_filter import LowQualityRules
            low_quality_rules = LowQualityRules(
                filter_short=True,
                dedup_md5=True,
                dedup_similar=True,
                dedup_visual=True,
            )

        # ── 文案裂变方式：创造 / 用爆款（微改/仿写已删，2026-10-17 小白化）──
        copy_mode = self.copy_mode_combo.currentData()
        custom_text = ""
        if copy_mode != "create":
            # 用爆款：把「爆款文案」字段拼接成一段，跳过写文案 LLM
            custom_text = "".join(pain_points)

        # 禁用按钮，显示进度
        self.btn_generate.setEnabled(False)
        self.btn_stop.setVisible(True)
        self.progress_bar.setVisible(True)
        self.progress_bar.setRange(0, 0)  # 不确定进度
        self.status_label.setText("Pipeline 启动中...")

        # 后台执行
        self.worker = PipelineWorker(
            product_name=name,
            category=category,
            selling_points=selling_points,
            target_audience=audience,
            pain_points=pain_points,
            platform=platform,
            variant_count=variant_count,
            style_name="",  # 风格模板已删（2026-10-18），空=AI 自动
            ref_hit_ids=self._ref_hit_ids,
            custom_text=custom_text,
            name_prefix=name_prefix,
            low_quality_rules=low_quality_rules,
            aspect_ratio=self.aspect_combo.currentData() or "portrait",
        )
        self.worker.progress.connect(self._on_progress)
        self.worker.review_ready.connect(self._on_review_ready)
        self.worker.done.connect(self._on_finished)
        self.worker.error.connect(self._on_error)
        self.worker.cancelled.connect(self._on_cancelled)
        self.worker.finished.connect(self.worker.deleteLater)
        self.worker.start()

    def _on_review_ready(self, script_text: str) -> None:
        """文案已生成，弹出审核弹窗"""
        from adflow.gui.review_dialog import ReviewDialog
        self.progress_bar.setVisible(False)
        dlg = ReviewDialog(script_text, parent=self)
        dlg.exec()
        params = dlg.get_params()
        if dlg.closed:
            # 点 X 关闭：停止出片，退回主界面修改配置（不重新生成）
            self.worker.cancel()
        elif params["approved"]:
            self.status_label.setText("审核通过，继续配音+混剪...")
            self.progress_bar.setVisible(True)
            self.btn_stop.setVisible(True)
            self.worker.approve(params)
        else:
            self.status_label.setText("审核驳回，重新生成文案...")
            # 驳回后重新启动（协作式取消，避免 terminate() 强杀）
            self.worker.cancel()
            self._retry_generate()

    def _retry_generate(self):
        """驳回后自动重新生成"""
        if hasattr(self, 'worker') and self.worker.isRunning():
            self.worker.cancel()
            self.worker.wait(2000)
        self.progress_bar.setVisible(False)
        self.status_label.setText("重新生成中...")
        self._run_pipeline()

    def _on_progress(self, msg: str) -> None:
        self.status_label.setText(msg)

    def _on_finished(self, result: PipelineResult) -> None:
        self.btn_generate.setEnabled(True)
        self.btn_stop.setVisible(False)
        self.progress_bar.setVisible(False)
        self._refresh_task_list()

        if result.success:
            self._last_task_id = result.task_id
            self.status_label.setText(f"✅ 完成! 产出 {len(result.variants)} 个视频变体")

            # 自动记录到调教日志
            try:
                from adflow.memory_store import memory
                memory.add_training_log(
                    category="strategy",
                    content=f"{result.strategy.narrative_type} / {result.strategy.hook_type}",
                    feedback=f"产出 {len(result.variants)} 个变体",
                )
            except Exception:
                pass

            # 拼接详情
            detail = (
                f"策略: {result.strategy.narrative_type} / {result.strategy.hook_type}\n\n"
                f"生成 {len(result.scripts)} 个分镜脚本, {len(result.variants)} 个视频变体\n\n"
            )
            # ── 镜头重复度 ──
            rs = result.repetition_stats if hasattr(result, 'repetition_stats') else {}
            if rs:
                detail += (
                    f"📊 镜头重复度: {rs.get('unique_materials',0)}/{rs.get('total_shots',0)} 唯一 "
                    f"({rs.get('rate',0)}%)\n"
                    f"   素材库共{rs.get('material_total',0)}个镜头, "
                    f"复用{rs.get('reused',0)}个\n\n"
                )
            if result.warnings:
                detail += "⚠ 警告:\n" + "\n".join(result.warnings[:10]) + "\n\n"
            detail += f"输出目录: {config.output_dir}\\{result.task_id}\\"

            # 出片完成弹窗（导出剪映/Premiere、编辑时间轴已删，2026-10-17 小白化）
            msg_box = QMessageBox(self)
            msg_box.setWindowTitle("出片完成")
            msg_box.setText(detail)
            msg_box.setIcon(QMessageBox.Icon.Information)
            btn_open = msg_box.addButton("📂 打开目录", QMessageBox.ButtonRole.ActionRole)
            btn_close = msg_box.addButton("关闭", QMessageBox.ButtonRole.RejectRole)
            msg_box.exec()

            clicked = msg_box.clickedButton()
            if clicked == btn_open:
                self._open_output_dir()
        else:
            self.status_label.setText("❌ 执行失败")
            QMessageBox.critical(
                self, "执行失败",
                "\n".join(result.errors) if result.errors else "未知错误"
            )

    def _on_error(self, error: str) -> None:
        self.btn_generate.setEnabled(True)
        self.btn_stop.setVisible(False)
        self.progress_bar.setVisible(False)
        self.status_label.setText(f"❌ {error}")
        QMessageBox.critical(self, "错误", error)

    def _on_stop(self) -> None:
        """点击停止按钮：协作式取消出片"""
        if hasattr(self, "worker") and self.worker.isRunning():
            self.worker.cancel()
            self.status_label.setText("正在停止...")

    def _on_cancelled(self) -> None:
        """出片已被停止：恢复 UI 可再次出片"""
        self.btn_generate.setEnabled(True)
        self.btn_stop.setVisible(False)
        self.progress_bar.setVisible(False)
        self.status_label.setText("⏹ 已停止")
        self._refresh_task_list()

    # _select_ref_hits 已删（2026-10-18 小白化：参考爆款选择下线）

    def _open_output_dir(self) -> None:
        """打开当日输出目录（按日期组织: output/0729/）"""
        import subprocess
        from datetime import datetime

        today = datetime.now().strftime("%m%d")
        folder = os.path.join(config.output_dir, today)

        if not os.path.exists(folder):
            os.makedirs(folder, exist_ok=True)

        subprocess.Popen(["explorer", folder])

    # _refresh_style_combo 已删（2026-10-18 小白化：风格下拉随风格模板一起下线）

    # ---- 任务历史 ----

    def _refresh_task_list(self) -> None:
        """刷新任务历史列表"""
        self.task_list.clear()
        tasks = self.project_repo.get_all_tasks(limit=50)
        for task in tasks:
            status_icon = {"pending": "⏳", "running": "🔄", "done": "✅", "failed": "❌"}
            icon = status_icon.get(task.status, "❓")
            label = f"{icon} {task.created_at[:16]} | {task.platform} | {task.status}"
            item = QListWidgetItem(label)
            item.setData(Qt.ItemDataRole.UserRole, task.task_id)
            self.task_list.addItem(item)

    def _on_task_double_click(self) -> None:
        """双击查看任务详情"""
        item = self.task_list.currentItem()
        if not item:
            return

        task_id = item.data(Qt.ItemDataRole.UserRole)
        task = self.project_repo.get_task(task_id)
        if not task:
            return

        strategy = self.project_repo.get_strategy_by_task(task_id)
        variants = self.project_repo.get_variants_by_task(task_id)
        scripts = self.project_repo.get_scripts_by_task(task_id)

        info = f"任务ID: {task.task_id}\n"
        info += f"状态: {task.status}\n"
        info += f"平台: {task.platform}\n"
        info += f"目标时长: {task.target_duration_ms / 1000:.0f}s\n\n"

        if strategy:
            info += f"策略: {strategy.narrative_type}\n"
            info += f"钩子: {strategy.hook_type}\n"
            info += f"节奏: {strategy.pace_style}\n"
            info += f"核心信息: {strategy.key_message}\n\n"

        info += f"脚本数: {len(scripts)}\n"
        info += f"成品变体数: {len(variants)}\n\n"

        for v in variants:
            info += (
                f"[{v.status}] {v.output_file}\n"
                f"  合规: {'✓' if v.compliance_check_passed else '✗'}\n"
            )

        QMessageBox.information(self, f"任务详情 — {task_id}", info)
