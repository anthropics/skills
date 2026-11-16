"""
设置面板
- 🎯 预设 / 🎵 BGM / 🎨 调色 / 🔤 字幕 / 🎙️ 配音 / 🎬 风格
- 六合一设置，支持保存加载预设、剪映草稿风格导入
"""

import os, json
from datetime import datetime

from PyQt6.QtWidgets import (
    QWidget, QVBoxLayout, QHBoxLayout, QPushButton, QLabel,
    QLineEdit, QTextEdit, QSpinBox, QComboBox,
    QFormLayout, QListWidget, QListWidgetItem,
    QMessageBox, QFileDialog,
    QTabWidget, QSlider, QColorDialog, QCheckBox, QDialog,
    QTextBrowser,
)
from PyQt6.QtCore import Qt, QSize

from adflow.config_loader import config
from adflow.engine.bgm_library import BGMLibrary, AUDIO_EXTS


class SettingsPanel(QWidget):
    """设置面板"""

    def __init__(self):
        super().__init__()
        layout = QVBoxLayout(self)

        # 嵌套标签页
        self.tabs = QTabWidget()

        self.tabs.addTab(self._build_api_tab(), "🔌 API/模型")
        self.tabs.addTab(self._build_bgm_tab(), "🎵 BGM")
        self.tabs.addTab(self._build_color_tab(), "🎨 调色")
        self.tabs.addTab(self._build_subtitle_tab(), "🔤 字幕")
        # 🎙️ 配音已移到AI文案审核弹窗，设置面板不再显示
        self.tabs.addTab(self._build_style_tab(), "🎬 风格")

        # 屏蔽词管理
        from adflow.gui.blocked_words_panel import BlockedWordsPanel
        self.blocked_words_panel = BlockedWordsPanel()
        self.tabs.addTab(self.blocked_words_panel, "🚫 屏蔽词")

        layout.addWidget(self.tabs)

        # 底部保存按钮
        btn_row = QHBoxLayout()
        btn_save = QPushButton("💾 保存所有设置")
        btn_save.setStyleSheet(
            "QPushButton { background-color: #4a90d9; color: white; "
            "font-size: 14px; padding: 10px 20px; border-radius: 6px; }"
            "QPushButton:hover { background-color: #357abd; }"
        )
        btn_save.clicked.connect(self._save_all)
        btn_row.addStretch()
        btn_row.addWidget(btn_save)
        layout.addLayout(btn_row)

        self.status_label = QLabel("")
        layout.addWidget(self.status_label)

    # ============================================================
    # 🔌 API / 模型
    # ============================================================
    # 配音平台 → 需要的环境变量（edge 免费免 Key；qwen3-tts 是本地自动兜底不进选择）
    _TTS_KEY_MAP: dict[str, list[str]] = {
        "volcano": ["VOLCANO_TTS_APP_ID", "VOLCANO_TTS_TOKEN"],
        "minimax": ["MINIMAX_API_KEY", "MINIMAX_GROUP_ID"],
        "cosyvoice": ["DASHSCOPE_API_KEY"],
        "edge": [],
    }

    # 取 Key 小白教程（LLM 与 TTS 共用一份，键 = 平台 id；没进表的 = 不需要 Key）
    _TUTORIALS: dict[str, dict] = {
        "dashscope": {
            "title": "阿里百炼（推荐，注册就送免费额度）",
            "steps": [
                "打开 <a href='https://bailian.console.aliyun.com'>百炼控制台（点这里直达）</a>，手机号注册/登录，支付宝扫码也行",
                "第一次进会让你「开通模型服务」— 点同意开通，免费",
                "鼠标移到右上角头像 → 点「API-KEY」",
                "点「创建我的 API-KEY」→ 复制 sk- 开头那串",
                "回到本页，粘到上面 API Key 框 → 点「💾 保存所有设置」",
            ],
        },
        "deepseek": {
            "title": "DeepSeek（便宜，按用量扣费）",
            "steps": [
                "打开 <a href='https://platform.deepseek.com'>DeepSeek 开放平台（点这里直达）</a>，手机号注册登录",
                "点左侧「充值」，先充 10 元（不充值调不了）",
                "点左侧「API Keys」→「创建 API key」",
                "马上复制弹出来的 key（只显示这一次，关掉就看不到了）",
                "回到本页粘贴 → 保存",
            ],
        },
        "moonshot": {
            "title": "Moonshot（Kimi 家的）",
            "steps": [
                "打开 <a href='https://platform.moonshot.cn'>Moonshot 开放平台（点这里直达）</a>，注册登录",
                "点左侧「API Key 管理」→ 点「新建」",
                "复制 key（账户要有余额才能调用，先充值）",
                "回到本页粘贴 → 保存",
            ],
        },
        "openai": {
            "title": "OpenAI 兼容（进阶用法）",
            "steps": [
                "这个是给有自己的接口地址/中转站的人用的，需要自己改网址和 Key",
                "没有特殊需求的话，选上面的阿里百炼或 DeepSeek 就够了",
            ],
        },
        "volcano": {
            "title": "火山引擎（剪映同源音色）",
            "steps": [
                "打开 <a href='https://console.volcengine.com'>火山引擎控制台（点这里直达）</a>，注册并实名认证",
                "在顶部搜索框搜「语音技术」，进语音技术控制台",
                "开通「语音合成大模型」服务",
                "点「应用管理」→ 创建应用 → 复制 App ID",
                "在应用详情里点「获取访问令牌」→ 复制 Access Token",
                "两个一起填到上面两个框 → 保存",
            ],
        },
        "minimax": {
            "title": "MiniMax",
            "steps": [
                "打开 <a href='https://platform.minimaxi.com'>MiniMax 开放平台（点这里直达）</a>，注册登录",
                "进「账户管理」→「接口密钥」→「创建新密钥」→ 马上复制（只显示一次）",
                "同一片页面里能看到 Group ID，一起复制",
                "两个都填到上面 → 保存",
            ],
        },
        "cosyvoice": {
            "title": "阿里 CosyVoice（和百炼用同一个 Key）",
            "steps": [
                "照上面「阿里百炼」的教程拿一个 API Key（就是同一个）",
                "填到本页「API Key（与阿里百炼共用）」框 → 保存",
            ],
        },
    }

    def _build_api_tab(self) -> QWidget:
        from adflow.api.llm_adapter import _DEFAULT_PROVIDERS

        w = QWidget()
        layout = QVBoxLayout(w)
        layout.addWidget(QLabel("<b>API / 模型</b> — 选平台、填 Key，保存后立即生效"))

        # ── AI 文案模型 ──
        layout.addWidget(QLabel("<b>🤖 AI 文案模型</b>"))
        form_llm = QFormLayout()

        self.api_llm_combo = QComboBox()
        llm_labels = {
            "dashscope": "阿里百炼（Qwen，推荐）",
            "deepseek": "DeepSeek",
            "moonshot": "Moonshot（月之暗面）",
            "openai": "OpenAI 兼容",
            "ollama": "本地 Ollama（免费，无需 Key）",
        }
        for name, p in _DEFAULT_PROVIDERS.items():
            self.api_llm_combo.addItem(llm_labels.get(name, name), name)
        active_llm = config.get("llm.active", "dashscope")
        idx = self.api_llm_combo.findData(active_llm)
        if idx >= 0:
            self.api_llm_combo.setCurrentIndex(idx)
        self.api_llm_combo.currentIndexChanged.connect(self._on_llm_platform_changed)
        form_llm.addRow("平台:", self.api_llm_combo)

        self.api_llm_key_label = QLabel("API Key:")
        self.api_llm_key = QLineEdit()
        self.api_llm_key.setEchoMode(QLineEdit.EchoMode.Password)
        form_llm.addRow(self.api_llm_key_label, self.api_llm_key)
        layout.addLayout(form_llm)

        # ── 配音 TTS ──
        layout.addWidget(QLabel("<b>🔊 配音（TTS）</b>"))
        form_tts = QFormLayout()

        self.api_tts_combo = QComboBox()
        tts_labels = {
            "volcano": "火山引擎（剪映同源音色）",
            "minimax": "MiniMax",
            "cosyvoice": "阿里 CosyVoice",
            "edge": "微软 Edge（免费，无需 Key）",
        }
        for name, label in tts_labels.items():
            self.api_tts_combo.addItem(label, name)
        active_tts = config.get("tts.backend", "volcano")
        idx = self.api_tts_combo.findData(active_tts)
        if idx >= 0:
            self.api_tts_combo.setCurrentIndex(idx)
        self.api_tts_combo.currentIndexChanged.connect(self._on_tts_platform_changed)
        form_tts.addRow("平台:", self.api_tts_combo)

        # 各平台 Key 输入框按需显示
        self._tts_key_rows: dict[str, tuple[QLabel, QLineEdit]] = {}
        for env_name, label, secret in [
            ("VOLCANO_TTS_APP_ID", "App ID:", True),
            ("VOLCANO_TTS_TOKEN", "Access Token:", True),
            ("MINIMAX_API_KEY", "API Key:", True),
            ("MINIMAX_GROUP_ID", "Group ID:", False),
            ("DASHSCOPE_API_KEY", "API Key（与阿里百炼共用）:", True),
        ]:
            lbl = QLabel(label)
            edit = QLineEdit()
            if secret:
                edit.setEchoMode(QLineEdit.EchoMode.Password)
            form_tts.addRow(lbl, edit)
            self._tts_key_rows[env_name] = (lbl, edit)

        self.api_tts_hint = QLabel("")
        self.api_tts_hint.setStyleSheet("color: #888; font-size: 12px;")
        form_tts.addRow(self.api_tts_hint)
        layout.addLayout(form_tts)

        # ── 测试按钮 ──
        btn_row = QHBoxLayout()
        self.btn_test_llm = QPushButton("🔌 测试 AI 模型")
        self.btn_test_llm.setToolTip("保存当前配置并发一条最小请求验证")
        self.btn_test_llm.clicked.connect(self._test_llm)
        btn_row.addWidget(self.btn_test_llm)
        self.btn_test_tts = QPushButton("🔊 测试配音")
        self.btn_test_tts.setToolTip("保存当前配置并合成一句测试音频验证")
        self.btn_test_tts.clicked.connect(self._test_tts)
        btn_row.addWidget(self.btn_test_tts)
        btn_row.addStretch()
        layout.addLayout(btn_row)

        # ── 取 Key 小白教程：跟着当前选中的平台走 ──
        layout.addWidget(QLabel("<b>📖 不知道 Key 哪来？照下面教程一步步拿</b>"))
        self.api_tutorial = QTextBrowser()
        self.api_tutorial.setOpenExternalLinks(True)
        self.api_tutorial.setMaximumHeight(200)
        self.api_tutorial.setStyleSheet(
            "QTextBrowser {background:#2b2b2b; color:#ddd; font-size:12px;"
            "border:1px solid #444; border-radius:6px; padding:4px 8px;}")
        layout.addWidget(self.api_tutorial)

        layout.addStretch()
        self._on_llm_platform_changed()
        self._on_tts_platform_changed()
        return w

    def _on_llm_platform_changed(self):
        from adflow.api.llm_adapter import _DEFAULT_PROVIDERS
        name = self.api_llm_combo.currentData() or "dashscope"
        p = _DEFAULT_PROVIDERS.get(name)
        if name == "ollama" or not p or not p.api_key_env:
            self.api_llm_key_label.setText("API Key:")
            self.api_llm_key.setVisible(False)
            self.api_llm_key_label.setVisible(False)
        else:
            self.api_llm_key_label.setText(f"API Key（{p.api_key_env}）:")
            self.api_llm_key_label.setVisible(True)
            self.api_llm_key.setVisible(True)
            self._set_key_placeholder(self.api_llm_key, p.api_key_env)
        self._refresh_tutorial()

    def _on_tts_platform_changed(self):
        name = self.api_tts_combo.currentData() or "volcano"
        visible = self._TTS_KEY_MAP.get(name, [])
        for env_name, (lbl, edit) in self._tts_key_rows.items():
            show = env_name in visible
            lbl.setVisible(show)
            edit.setVisible(show)
            if show:
                self._set_key_placeholder(edit, env_name)
        self.api_tts_hint.setText("免费，无需配置" if name == "edge" else "")
        self._refresh_tutorial()

    def _refresh_tutorial(self):
        """按当前选中的 AI 平台 + 配音平台拼取 Key 教程"""
        def _block(key: str, kind: str) -> str:
            t = self._TUTORIALS.get(key)
            if not t:
                return ""
            steps = "".join(f"<li>{s}</li>" for s in t["steps"])
            return f"<h4>{kind}：{t['title']}</h4><ol>{steps}</ol>"

        llm = self.api_llm_combo.currentData() or "dashscope"
        tts = self.api_tts_combo.currentData() or "volcano"
        html = _block(llm, "🤖 AI 文案") + _block(tts, "🔊 配音")
        self.api_tutorial.setHtml(
            html or "<p>当前选的平台都不需要 Key，直接点上面的测试按钮就行。</p>")

    @staticmethod
    def _set_key_placeholder(edit: QLineEdit, env_name: str):
        import os as _os
        if _os.environ.get(env_name):
            edit.setPlaceholderText("已配置 ✓（留空保持不变）")
        else:
            edit.setPlaceholderText("未配置，请输入")

    def _save_api_to_config(self, silent: bool = False):
        """保存 API 设置：平台写 config.yaml，Key 写 .env（留空不动）"""
        from adflow.api.llm_adapter import _DEFAULT_PROVIDERS

        env_updates: dict[str, str] = {}
        llm_name = self.api_llm_combo.currentData() or "dashscope"
        config.set("llm.active", llm_name)
        p = _DEFAULT_PROVIDERS.get(llm_name)
        if p:
            config.set("llm.model", p.default_model)
            config.set("llm.base_url", p.base_url)
            config.set("llm.api_key_env", p.api_key_env)
            key = self.api_llm_key.text().strip()
            if key and p.api_key_env:
                env_updates[p.api_key_env] = key

        tts_name = self.api_tts_combo.currentData() or "volcano"
        config.set("tts.backend", tts_name)
        for env_name, (_, edit) in self._tts_key_rows.items():
            val = edit.text().strip()
            if val:
                env_updates[env_name] = val

        if env_updates:
            config.save_env(env_updates)
            if "DASHSCOPE_API_KEY" in env_updates:
                config.set("llm.api_key", env_updates["DASHSCOPE_API_KEY"])
            elif llm_name == "dashscope" and "DASHSCOPE_API_KEY" not in env_updates:
                import os as _os
                existing = _os.environ.get("DASHSCOPE_API_KEY", "")
                if existing:
                    config.set("llm.api_key", existing)

        # 清空输入框并刷新占位提示（已写入的不回显明文）
        self.api_llm_key.clear()
        for _, edit in self._tts_key_rows.values():
            edit.clear()
        self._on_llm_platform_changed()
        self._on_tts_platform_changed()
        if not silent:
            self.status_label.setText(f"✅ API 设置已保存：AI={llm_name}，配音={tts_name}")

    def _test_llm(self):
        self._save_api_to_config(silent=True)
        self.btn_test_llm.setEnabled(False)
        self.status_label.setText("AI 模型测试中...")

        def _run():
            from openai import OpenAI
            from adflow.api.llm_adapter import get_llm_config
            api_key, base_url, model = get_llm_config()
            client = OpenAI(api_key=api_key or "ollama", base_url=base_url, timeout=30)
            resp = client.chat.completions.create(
                model=model,
                messages=[{"role": "user", "content": "只回复两个字母: OK"}],
                max_tokens=8,
            )
            reply = (resp.choices[0].message.content or "").strip() if resp.choices else ""
            return f"✅ AI 模型连接成功（{model}）回复: {reply or '(空)'}"

        self._llm_tester = _make_test_runner(
            _run, self.btn_test_llm,
            lambda msg: self.status_label.setText(str(msg)),
            lambda err: self.status_label.setText(f"❌ AI 模型测试失败: {err}"),
        )

    def _test_tts(self):
        self._save_api_to_config(silent=True)
        self.btn_test_tts.setEnabled(False)
        self.status_label.setText("配音测试中（合成一句音频）...")

        def _run():
            from adflow.engine.tts_engine import create_tts_engine
            eng = create_tts_engine(backend="")
            out = eng.synthesize("配音连接测试")
            if not os.path.exists(out) or os.path.getsize(out) < 100:
                raise RuntimeError("合成的音频文件为空")
            return f"✅ 配音合成成功（{eng.backend_name}）"

        self._tts_tester = _make_test_runner(
            _run, self.btn_test_tts,
            lambda msg: self.status_label.setText(str(msg)),
            lambda err: self.status_label.setText(f"❌ 配音测试失败: {err}"),
        )

    # ============================================================
    # 🎵 BGM
    # ============================================================
    def _build_bgm_tab(self) -> QWidget:
        w = QWidget()
        layout = QVBoxLayout(w)

        # 顶部操作栏
        top_row = QHBoxLayout()
        top_row.addWidget(QLabel(f"<b>BGM 库</b>"))
        top_row.addStretch()
        btn_open_bgm = QPushButton("📁 打开BGM文件夹")
        btn_open_bgm.setStyleSheet(
            "QPushButton {background:#3a3a3a; color:#ccc; padding:6px 12px; border-radius:4px;}"
            "QPushButton:hover {background:#555;}")
        btn_open_bgm.clicked.connect(lambda: self._open_dir("bgm"))
        top_row.addWidget(btn_open_bgm)
        layout.addLayout(top_row)

        self.bgm_list = QListWidget()
        self.bgm_list.setMaximumHeight(150)
        layout.addWidget(self.bgm_list)

        row = QHBoxLayout()
        btn_add_bgm = QPushButton("➕ 添加 BGM")
        btn_add_bgm.clicked.connect(self._add_bgm)
        row.addWidget(btn_add_bgm)

        btn_del_bgm = QPushButton("🗑 移除")
        btn_del_bgm.clicked.connect(self._remove_bgm)
        row.addWidget(btn_del_bgm)

        btn_refresh_bgm = QPushButton("🔄 刷新")
        btn_refresh_bgm.clicked.connect(self._refresh_bgm_list)
        row.addWidget(btn_refresh_bgm)
        row.addStretch()
        layout.addLayout(row)

        # AI 自动轮换开关
        self.bgm_auto = QCheckBox("🤖 自动轮换 BGM（按列表顺序轮流用）")
        self.bgm_auto.setChecked(config.get("bgm.enabled", True))
        layout.addWidget(self.bgm_auto)

        self._refresh_bgm_list()
        return w

    # ============================================================
    # 🎨 调色
    # ============================================================
    def _build_color_tab(self) -> QWidget:
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.addWidget(QLabel("<b>调色预设</b> — 导出时应用 FFmpeg 调色滤镜（选\"否\"则 AI 自动）"))

        self.color_auto = QCheckBox("否 = AI 自动（勾选后忽略以下参数）")
        layout.addWidget(self.color_auto)

        form = QFormLayout()
        self.c_brightness = self._make_slider(-0.5, 0.5, 0.0, "0.00")
        form.addRow("亮度:", self.c_brightness)
        self.c_contrast = self._make_slider(0.5, 2.0, 1.0, "0.00")
        form.addRow("对比度:", self.c_contrast)
        self.c_saturation = self._make_slider(0.0, 3.0, 1.0, "0.00")
        form.addRow("饱和度:", self.c_saturation)
        self.c_temperature = self._make_slider(-1.0, 1.0, 0.0, "0.00")
        form.addRow("色温:", self.c_temperature)
        layout.addLayout(form)

        # 剪映调色导入
        btn_import_capcut = QPushButton("📥 从剪映草稿导入调色")
        btn_import_capcut.clicked.connect(self._import_color_from_capcut)
        layout.addWidget(btn_import_capcut)

        layout.addStretch()
        self._load_color_from_config()
        return w

    # ============================================================
    # 🔤 字幕
    # ============================================================
    def _build_subtitle_tab(self) -> QWidget:
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.addWidget(QLabel("<b>字幕样式</b>"))

        form = QFormLayout()

        row_font = QHBoxLayout()
        self.sub_font = QLineEdit()
        row_font.addWidget(self.sub_font)
        btn_font = QPushButton("浏览...")
        btn_font.clicked.connect(lambda: self._browse_font(self.sub_font))
        row_font.addWidget(btn_font)
        form.addRow("字体路径:", row_font)

        self.sub_size = QSpinBox()
        self.sub_size.setRange(12, 200)
        form.addRow("字号:", self.sub_size)

        row_color = QHBoxLayout()
        self.sub_color = QLineEdit()
        row_color.addWidget(self.sub_color)
        btn_color = QPushButton("选色")
        btn_color.clicked.connect(lambda: self._pick_color(self.sub_color))
        row_color.addWidget(btn_color)
        form.addRow("文字颜色:", row_color)

        row_stroke = QHBoxLayout()
        self.sub_stroke_color = QLineEdit()
        row_stroke.addWidget(self.sub_stroke_color)
        btn_sc = QPushButton("选色")
        btn_sc.clicked.connect(lambda: self._pick_color(self.sub_stroke_color))
        row_stroke.addWidget(btn_sc)
        form.addRow("描边颜色:", row_stroke)

        self.sub_stroke_w = QSpinBox()
        self.sub_stroke_w.setRange(0, 10)
        form.addRow("描边宽度:", self.sub_stroke_w)

        self.sub_safe_bottom = QSpinBox()
        self.sub_safe_bottom.setRange(20, 500)
        form.addRow("底部安全区(px):", self.sub_safe_bottom)

        self.sub_highlight_color = QLineEdit()
        form.addRow("高亮色:", self.sub_highlight_color)

        self.sub_cta_color = QLineEdit()
        form.addRow("CTA色:", self.sub_cta_color)

        layout.addLayout(form)

        # 预览
        self.sub_preview = QLabel("预览文字效果")
        self.sub_preview.setAlignment(Qt.AlignmentFlag.AlignCenter)
        self.sub_preview.setMinimumHeight(60)
        self.sub_preview.setStyleSheet("background: #333; color: white; font-size: 36px; border-radius: 8px;")
        layout.addWidget(self.sub_preview)

        layout.addStretch()
        self._load_subtitle_from_config()
        return w

    # ============================================================
    # 🎙️ 配音
    # ============================================================

    # ============================================================
    # 🎬 风格
    # ============================================================
    def _build_style_tab(self) -> QWidget:
        w = QWidget()
        layout = QVBoxLayout(w)
        layout.addWidget(QLabel("<b>风格规则集</b> — AI 出片时可选择，不选则 AI 自己决定"))

        self.style_list = QListWidget()
        self.style_list.currentRowChanged.connect(self._on_style_selected)
        layout.addWidget(self.style_list)

        form = QFormLayout()
        self.style_name = QLineEdit()
        form.addRow("风格名称:", self.style_name)

        self.style_pace = QComboBox()
        self.style_pace.addItems(["", "fast", "medium", "slow"])
        self.style_pace.setItemText(0, "否 = AI 自动")
        form.addRow("节奏:", self.style_pace)

        self.style_transition = QComboBox()
        self.style_transition.addItems(["", "cut", "dissolve", "zoom", "slide"])
        self.style_transition.setItemText(0, "否 = AI 自动")
        form.addRow("转场:", self.style_transition)

        self.style_anim = QComboBox()
        self.style_anim.addItems(["", "fade", "slide", "bounce", "zoom"])
        self.style_anim.setItemText(0, "否 = AI 自动")
        form.addRow("入场动画:", self.style_anim)

        layout.addLayout(form)

        # 规则文本框
        layout.addWidget(QLabel("<b>规则（Markdown）</b> — 自由写，AI 会参考"))
        self.style_rules = QTextEdit()
        self.style_rules.setMaximumHeight(100)
        self.style_rules.setPlaceholderText("例: 字幕不超过15字\n色调偏暖\nBGM用电子风\n每2-3秒切一次镜头")
        layout.addWidget(self.style_rules)

        # 参考案例
        layout.addWidget(QLabel("<b>参考案例</b> — 把出片效果好/审美好的视频作为案例"))
        case_row = QHBoxLayout()
        self.style_case_combo = QComboBox()
        self.style_case_combo.setToolTip("从历史出片中选一个作为参考案例")
        case_row.addWidget(self.style_case_combo)
        self.style_case_notes = QLineEdit()
        self.style_case_notes.setPlaceholderText("这个案例好在哪？（如: 字体好/节奏好/色调好）")
        case_row.addWidget(self.style_case_notes)
        layout.addLayout(case_row)

        btn_add_case = QPushButton("➕ 添加为参考案例")
        btn_add_case.clicked.connect(self._add_case)
        layout.addWidget(btn_add_case)

        self.style_case_list = QListWidget()
        self.style_case_list.setMaximumHeight(80)
        layout.addWidget(self.style_case_list)

        row = QHBoxLayout()
        btn_save_style = QPushButton("💾 保存规则集")
        btn_save_style.clicked.connect(self._save_style)
        row.addWidget(btn_save_style)
        btn_del_style = QPushButton("🗑 删除")
        btn_del_style.clicked.connect(self._delete_style)
        row.addWidget(btn_del_style)
        btn_rm_case = QPushButton("🗑 移除选中案例")
        btn_rm_case.clicked.connect(self._remove_case)
        row.addWidget(btn_rm_case)
        btn_capcut_style = QPushButton("📥 从剪映导入")
        btn_capcut_style.clicked.connect(self._import_style_from_capcut)
        row.addWidget(btn_capcut_style)
        btn_save_memory = QPushButton("🧠 保存到记忆")
        btn_save_memory.setToolTip("将当前所有设置积累到本地规则记忆")
        btn_save_memory.clicked.connect(self._save_to_memory)
        row.addWidget(btn_save_memory)
        row.addStretch()
        layout.addLayout(row)

        self._refresh_style_list()
        self._refresh_case_combo()
        return w

    # ============================================================
    # 工具方法
    # ============================================================
    @staticmethod
    def _make_slider(min_v: float, max_v: float, default: float, fmt: str) -> QWidget:
        """创建带标签的浮点滑块"""
        w = QWidget()
        row = QHBoxLayout(w)
        row.setContentsMargins(0, 0, 0, 0)
        slider = QSlider(Qt.Orientation.Horizontal)
        slider.setRange(0, 100)
        slider.setValue(int((default - min_v) / (max_v - min_v) * 100))
        label = QLabel(f"{default:{fmt}}")
        slider.valueChanged.connect(
            lambda v: label.setText(f"{min_v + (v / 100.0) * (max_v - min_v):{fmt}}")
        )
        row.addWidget(slider)
        row.addWidget(label)
        w.slider = slider
        w.label = label
        w.get_value = lambda: min_v + (slider.value() / 100.0) * (max_v - min_v)
        w.set_value = lambda val: slider.setValue(
            int(min(100, max(0, (val - min_v) / (max_v - min_v) * 100)))
        )
        return w

    @staticmethod
    def _browse_font(target: QLineEdit) -> None:
        f, _ = QFileDialog.getOpenFileName(None, "选择字体", "C:/Windows/Fonts/",
                                             "字体文件 (*.ttf *.ttc *.otf)")
        if f:
            target.setText(f)

    @staticmethod
    def _pick_color(target: QLineEdit) -> None:
        c = QColorDialog.getColor()
        if c.isValid():
            target.setText(c.name())

    # ============================================================
    # 配置加载/保存
    # ============================================================
    def _load_subtitle_from_config(self):
        sub = config.editing_config.get("subtitle", {})
        self.sub_font.setText(sub.get("font", ""))
        self.sub_size.setValue(sub.get("font_size", 48))
        self.sub_color.setText(sub.get("color", "white"))
        self.sub_stroke_color.setText(sub.get("stroke_color", "black"))
        self.sub_stroke_w.setValue(sub.get("stroke_width", 2))
        self.sub_safe_bottom.setValue(sub.get("safe_margin_bottom", 120))
        self.sub_highlight_color.setText("#FFD700")
        self.sub_cta_color.setText("#FF4444")

    def _save_subtitle_to_config(self):
        config.set("editing.subtitle.font", self.sub_font.text())
        config.set("editing.subtitle.font_size", self.sub_size.value())
        config.set("editing.subtitle.color", self.sub_color.text())
        config.set("editing.subtitle.stroke_color", self.sub_stroke_color.text())
        config.set("editing.subtitle.stroke_width", self.sub_stroke_w.value())
        config.set("editing.subtitle.safe_margin_bottom", self.sub_safe_bottom.value())

    def _load_color_from_config(self):
        cg = config.color_grade_config
        self.c_brightness.set_value(cg.get("brightness", 0.0))
        self.c_contrast.set_value(cg.get("contrast", 0.0))
        self.c_saturation.set_value(cg.get("saturation", 0.0))
        self.c_temperature.set_value(cg.get("temperature", 0.0))

    def _save_color_to_config(self):
        if not self.color_auto.isChecked():
            config.set("color_grade.brightness", self.c_brightness.get_value())
            config.set("color_grade.contrast", self.c_contrast.get_value())
            config.set("color_grade.saturation", self.c_saturation.get_value())
            config.set("color_grade.temperature", self.c_temperature.get_value())

    def _save_all(self):
        self._save_api_to_config(silent=True)
        self._save_subtitle_to_config()
        self._save_color_to_config()
        config.set("bgm.enabled", self.bgm_auto.isChecked())
        config.save()
        self.status_label.setText("✅ 设置已保存")

    # ============================================================
    # 预设 CRUD
    # ============================================================
    # ============================================================
    # 工具
    # ============================================================
    def _open_dir(self, folder: str):
        """打开指定文件夹"""
        import subprocess
        if folder == "bgm":
            path = config.bgm_dir
        else:
            path = config.materials_dir
        os.makedirs(path, exist_ok=True)
        subprocess.Popen(["explorer", os.path.abspath(path)])

    # ============================================================
    # BGM 管理
    # ============================================================
    def _bgm_library(self) -> "BGMLibrary":
        return BGMLibrary()

    def _refresh_bgm_list(self):
        self.bgm_list.clear()
        lib = self._bgm_library()
        names = lib.load()
        # 扁平扫描 bgm_dir，未入库的音频自动补录（去重后写回）
        if os.path.isdir(config.bgm_dir):
            added = False
            for fn in sorted(os.listdir(config.bgm_dir)):
                if fn.lower().endswith(AUDIO_EXTS) and fn not in names:
                    names.append(fn)
                    added = True
            if added:
                lib.save(names)
        self._bgm_data = names
        for b in names:
            self.bgm_list.addItem(os.path.splitext(b)[0])

    def _add_bgm(self):
        files, _ = QFileDialog.getOpenFileNames(
            self, "添加 BGM", "", "音频文件 (*.mp3 *.wav *.m4a)")
        lib = self._bgm_library()
        for src in files:
            lib.add(src)
        self._refresh_bgm_list()
        self.status_label.setText(f"已添加 {len(files)} 个 BGM")

    def _remove_bgm(self):
        idx = self.bgm_list.currentRow()
        if idx < 0 or idx >= len(self._bgm_data):
            return
        name = self._bgm_data[idx]
        reply = QMessageBox.question(self, "确认", f"移除 {os.path.splitext(name)[0]}？")
        if reply == QMessageBox.StandardButton.Yes:
            self._bgm_library().remove(name)
            self._refresh_bgm_list()

    # ============================================================
    # 风格 CRUD
    # ============================================================
    def _style_dir(self):
        d = os.path.join(os.path.dirname(os.path.dirname(os.path.dirname(__file__))), "styles")
        os.makedirs(d, exist_ok=True)
        return d

    def _refresh_style_list(self):
        self.style_list.clear()
        self._style_data = []
        for f in sorted(os.listdir(self._style_dir())):
            if f.endswith(".json"):
                self.style_list.addItem(f.replace(".json", ""))

    def _on_style_selected(self, idx):
        self._style_data = []
        style_dir = self._style_dir()
        for f in sorted(os.listdir(style_dir)):
            if f.endswith(".json"):
                self._style_data.append(f.replace(".json", ""))
        if idx < 0 or idx >= len(self._style_data):
            return
        path = os.path.join(style_dir, f"{self._style_data[idx]}.json")
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        self.style_name.setText(data.get("name", ""))
        self.style_pace.setCurrentText(data.get("pace", ""))
        self.style_transition.setCurrentText(data.get("transition", ""))
        self.style_anim.setCurrentText(data.get("animation_in", ""))
        self.style_rules.setPlainText(data.get("rules", ""))
        # 案例
        self._cases = data.get("cases", [])
        self.style_case_list.clear()
        for c in self._cases:
            self.style_case_list.addItem(
                f"{c.get('label','?')}: {c.get('notes','')[:60]} [{c.get('task_id','')[:8]}]"
            )

    def _save_style(self):
        name = self.style_name.text().strip()
        if not name:
            return QMessageBox.warning(self, "提示", "请输入风格名称")
        data = {
            "name": name,
            "pace": self.style_pace.currentText(),
            "transition": self.style_transition.currentText(),
            "animation_in": self.style_anim.currentText(),
            "rules": self.style_rules.toPlainText(),
            "cases": getattr(self, '_cases', []),
            "updated": datetime.now().isoformat(),
        }
        # 保留创建时间
        old_path = os.path.join(self._style_dir(), f"{name}.json")
        if os.path.exists(old_path):
            try:
                with open(old_path, "r", encoding="utf-8") as f:
                    old = json.load(f)
                if old.get("created"):
                    data["created"] = old["created"]
            except Exception:
                pass
        if "created" not in data:
            data["created"] = datetime.now().isoformat()

        path = os.path.join(self._style_dir(), f"{name}.json")
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
        self._refresh_style_list()
        self.status_label.setText(f"规则集已保存: {name}")

    def _delete_style(self):
        idx = self.style_list.currentRow()
        if idx < 0:
            return
        name = self._style_data[idx]
        os.remove(os.path.join(self._style_dir(), f"{name}.json"))
        self._refresh_style_list()

    def _refresh_case_combo(self):
        """刷新参考案例下拉框（从历史出片任务中获取）"""
        self.style_case_combo.clear()
        self.style_case_combo.addItem("选择历史出片...", "")
        try:
            from adflow.db.project_repo import ProjectRepo
            repo = ProjectRepo()
            tasks = repo.get_all_tasks(limit=30)
            for t in tasks:
                label = f"{t.created_at[:16]} | {t.status} | {t.task_id[:8]}"
                self.style_case_combo.addItem(label, t.task_id)
        except Exception:
            pass

    def _add_case(self):
        task_id = self.style_case_combo.currentData()
        notes = self.style_case_notes.text().strip()
        if not task_id:
            return QMessageBox.information(self, "提示", "请先选择历史出片任务")
        if not hasattr(self, '_cases'):
            self._cases = []
        self._cases.append({
            "task_id": task_id,
            "notes": notes,
            "added": datetime.now().isoformat(),
            "label": f"案例{len(self._cases) + 1}",
        })
        self.style_case_list.clear()
        for c in self._cases:
            self.style_case_list.addItem(
                f"{c.get('label','?')}: {c.get('notes','')[:60]} [{c.get('task_id','')[:8]}]"
            )
        self.status_label.setText(f"已添加案例{len(self._cases)}")

    def _remove_case(self):
        row = self.style_case_list.currentRow()
        if row < 0 or not hasattr(self, '_cases'):
            return
        del self._cases[row]
        self.style_case_list.clear()
        for c in self._cases:
            self.style_case_list.addItem(
                f"{c.get('label','?')}: {c.get('notes','')[:60]} [{c.get('task_id','')[:8]}]"
            )

    # ============================================================
    # 剪映导入入口（Phase 2 实现）
    # ============================================================
    def _save_to_memory(self):
        """将当前所有设置积累到本地规则记忆"""
        from adflow.memory_store import memory

        data = {
            "font_size": self.sub_size.value(),
            "font_color": self.sub_color.text(),
            "subtitle_bottom": self.sub_safe_bottom.value(),
            "pace": self.style_pace.currentText(),
            "transition": self.style_transition.currentText(),
            "brightness": self.c_brightness.get_value(),
            "contrast": self.c_contrast.get_value(),
            "saturation": self.c_saturation.get_value(),
        }

        memory.add_style_feedback(
            name=self.style_name.text() or f"记忆_{datetime.now():%m%d_%H%M}",
            data=data,
            notes="从设置面板手动保存",
        )
        self.status_label.setText("✅ 已保存到本地记忆，AI 以后会自动参考这些偏好")

    def _import_color_from_capcut(self):
        QMessageBox.information(self, "剪映导入",
            "请到 🎬 风格 标签使用\"从剪映草稿导入风格\"功能\n"
            "可一次性导入调色+字体+节奏等全部参数。")

    def _import_style_from_capcut(self):
        """从剪映草稿导入风格（可选择草稿）"""
        try:
            from adflow.capcut_import.capcut_importer import (
                import_style_from_capcut, list_capcut_drafts,
            )

            drafts = list_capcut_drafts()
            if not drafts:
                QMessageBox.information(self, "未找到草稿",
                    "系统中未找到剪映/CapCut草稿。\n"
                    "请在剪映中创建或打开过草稿后重试。")
                return

            # 弹草稿选择对话框
            dialog = _CapcutDraftPicker(drafts, self)
            if dialog.exec() != QDialog.DialogCode.Accepted:
                return

            draft_path = dialog.selected_path
            style = import_style_from_capcut(draft_path)
            if style:
                self.style_name.setText(style.name)
                self.style_pace.setCurrentText(style.pace)
                self.style_transition.setCurrentText(style.transition)
                self.style_anim.setCurrentText(style.animation_in)
                self.status_label.setText(f"已从剪映导入: {style.name}")
        except ImportError:
            QMessageBox.information(self, "未安装",
                "需要安装 pyjianyingdraft 库:\npip install pyjianyingdraft")
        except Exception as e:
            QMessageBox.warning(self, "导入失败", str(e))


# ═══════════════════════════════════════
# 测试连接辅助
# ═══════════════════════════════════════

def _make_test_runner(fn, button, on_ok, on_err):
    """后台跑 fn，结束后恢复按钮可用；返回 TaskRunner（需保持引用防 GC）"""
    from adflow.gui.task_runner import TaskRunner

    runner = TaskRunner(fn)

    def _ok(msg):
        button.setEnabled(True)
        on_ok(msg)

    def _fail(err):
        button.setEnabled(True)
        on_err(err)

    runner.succeeded.connect(_ok)
    runner.failed.connect(_fail)
    runner.start()
    return runner


# ═══════════════════════════════════════
# 剪映草稿选择对话框
# ═══════════════════════════════════════

class _CapcutDraftPicker(QDialog):
    """剪映草稿浏览器 — 列出所有草稿供选择"""

    def __init__(self, drafts: list[dict], parent=None):
        super().__init__(parent)
        self.setWindowTitle("选择剪映草稿")
        self.resize(550, 400)
        self.selected_path = ""

        layout = QVBoxLayout(self)
        layout.setSpacing(10)

        info = QLabel(f"找到 {len(drafts)} 个剪映草稿，选择要导入风格的草稿：")
        info.setStyleSheet("font-size:12px;")
        layout.addWidget(info)

        # 列表
        self.list_widget = QListWidget()
        self.list_widget.setAlternatingRowColors(True)
        for d in drafts:
            name = d.get("name", "未命名")
            path = d.get("path", "")
            mtime = d.get("modified", 0)
            from datetime import datetime
            date_str = datetime.fromtimestamp(mtime).strftime("%m/%d %H:%M") if mtime else ""
            text = f"{name}"
            if date_str:
                text += f"    [{date_str}]"
            item = QListWidgetItem(text)
            item.setData(Qt.ItemDataRole.UserRole, path)
            item.setSizeHint(item.sizeHint() + QSize(0, 6))
            self.list_widget.addItem(item)

        self.list_widget.setCurrentRow(0)
        self.list_widget.itemDoubleClicked.connect(self.accept)
        layout.addWidget(self.list_widget, 1)

        # 按钮
        btn_row = QHBoxLayout()
        btn_ok = QPushButton("✓ 导入此草稿风格")
        btn_ok.setStyleSheet(
            "QPushButton {background:#4a90d9; color:white; padding:8px 20px; "
            "border-radius:4px; font-weight:700;}")
        btn_ok.clicked.connect(self.accept)
        btn_cancel = QPushButton("取消")
        btn_cancel.clicked.connect(self.reject)
        btn_row.addStretch()
        btn_row.addWidget(btn_ok)
        btn_row.addWidget(btn_cancel)
        layout.addLayout(btn_row)

    def accept(self):
        item = self.list_widget.currentItem()
        if item:
            self.selected_path = item.data(Qt.ItemDataRole.UserRole)
        super().accept()
