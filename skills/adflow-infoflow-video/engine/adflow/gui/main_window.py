"""
AdFlow 管理面板 — 主窗口
- 标签页导航：素材库 / AI出片 / 文案裂变 / 设置 / 因子分析
- 状态栏显示数据库路径和素材总数
"""

from PyQt6.QtWidgets import (
    QMainWindow, QTabWidget, QStatusBar, QMessageBox,
)
from PyQt6.QtGui import QAction

from adflow.gui.material_panel import MaterialPanel
# 手动剪辑已移除 — AdFlow 专注 AI 出片，专业剪辑用剪映
from adflow.gui.project_panel import ProjectPanel
from adflow.gui.settings_panel import SettingsPanel
# 因子分析已移除（2026-10-17 小白化：不影响出片质量，analytics_panel.py 代码保留）


class MainWindow(QMainWindow):
    """AdFlow 主窗口"""

    def __init__(self):
        super().__init__()
        self.setWindowTitle("AdFlow — 信息流广告 AI Agent 剪辑系统")
        self.resize(1280, 860)

        # 中央标签页
        self.tabs = QTabWidget()
        self.setCentralWidget(self.tabs)

        # 素材库面板
        self.material_panel = MaterialPanel()
        self.tabs.addTab(self.material_panel, "📦 素材库")

        # 任务管理面板（AI Agent Pipeline）
        self.project_panel = ProjectPanel()
        self.tabs.addTab(self.project_panel, "🤖 AI 出片")

        # 文案/配音裂变面板（独立标签，pipeline 由 worker 线程内自建，避免跨线程 SQLite）
        from adflow.gui.remix_panel import RemixPanel
        self.remix_panel = RemixPanel()
        self.tabs.addTab(self.remix_panel, "🔄 文案/配音裂变")

        # 设置面板
        self.settings_panel = SettingsPanel()
        self.tabs.addTab(self.settings_panel, "⚙️ 设置")

        # 状态栏
        self.status_bar = QStatusBar()
        self.setStatusBar(self.status_bar)
        self._refresh_status()

        # 菜单栏
        self._setup_menu()

    def _setup_menu(self) -> None:
        """创建菜单栏"""
        menu_bar = self.menuBar()

        # 文件菜单
        file_menu = menu_bar.addMenu("文件(&F)")
        import_action = QAction("导入素材(&I)", self)
        import_action.setShortcut("Ctrl+I")
        import_action.triggered.connect(self.material_panel.import_materials)
        file_menu.addAction(import_action)
        file_menu.addSeparator()
        exit_action = QAction("退出(&Q)", self)
        exit_action.setShortcut("Ctrl+Q")
        exit_action.triggered.connect(self.close)
        file_menu.addAction(exit_action)

        # 工具菜单
        tools_menu = menu_bar.addMenu("工具(&T)")
        refresh_action = QAction("刷新素材列表(&R)", self)
        refresh_action.setShortcut("F5")
        refresh_action.triggered.connect(self.material_panel.refresh_list)
        tools_menu.addAction(refresh_action)

        # 帮助菜单
        help_menu = menu_bar.addMenu("帮助(&H)")
        about_action = QAction("关于 AdFlow(&A)", self)
        about_action.triggered.connect(self._show_about)
        help_menu.addAction(about_action)

    def _show_about(self) -> None:
        QMessageBox.about(
            self, "关于 AdFlow",
            "AdFlow v0.1.0\n\n"
            "信息流广告 AI Agent 自动剪辑系统\n"
            "素材管理 · Agent Pipeline · 投放闭环 · 自动优化"
        )

    def _refresh_status(self) -> None:
        """刷新状态栏"""
        try:
            from adflow.db.material_repo import MaterialRepo
            repo = MaterialRepo()
            count = repo.count()
            from adflow.config_loader import config
            db = config.db_path
        except Exception:
            count = 0
            db = "未连接"
        self.status_bar.showMessage(f"素材总数: {count}  |  数据库: {db}")

    def closeEvent(self, event):
        """关闭窗口时清理数据库连接"""
        from adflow.db.connection import reset_db_instance
        reset_db_instance()
        event.accept()
