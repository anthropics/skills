"""
AdFlow 入口 — 启动 PyQt6 管理面板
用法: python main.py
"""

import sys
import os
import logging
import traceback

# ── 全局异常捕获：保存完整堆栈到文件 ──
def _global_excepthook(exc_type, exc_value, tb):
    tb_text = "".join(traceback.format_exception(exc_type, exc_value, tb))
    logging.critical("未捕获异常:\n%s", tb_text)
    crash_path = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "data", "logs", "crash.log")
    os.makedirs(os.path.dirname(crash_path), exist_ok=True)
    with open(crash_path, "a", encoding="utf-8") as f:
        f.write(f"\n{'='*60}\n{tb_text}")
    traceback.print_exception(exc_type, exc_value, tb)
sys.excepthook = _global_excepthook

# 确保项目根目录在 Python path 中
project_root = os.path.dirname(os.path.abspath(__file__))
if project_root not in sys.path:
    sys.path.insert(0, project_root)

from PyQt6.QtWidgets import QApplication, QMessageBox
from PyQt6.QtCore import Qt

from adflow.config_loader import config
from adflow.gui.main_window import MainWindow


def _setup_logging() -> None:
    """配置日志"""
    log_dir = os.path.join(project_root, "data", "logs")
    os.makedirs(log_dir, exist_ok=True)
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
        handlers=[
            logging.FileHandler(os.path.join(log_dir, "adflow.log"), encoding="utf-8"),
            logging.StreamHandler(),
        ],
    )


def _health_check() -> dict:
    """启动前环境检查，返回状态字典"""
    result = {
        "ffmpeg": False, "ffprobe": False, "api_key": False,
        "db": False, "warnings": [], "errors": [],
    }

    # FFmpeg
    from adflow.utils.ffmpeg_finder import check_ffmpeg
    ffmpeg_status = check_ffmpeg()
    result["ffmpeg"] = ffmpeg_status.get("ffmpeg_available", False)
    result["ffprobe"] = ffmpeg_status.get("ffprobe_available", False)
    if not result["ffmpeg"]:
        result["warnings"].append(
            "FFmpeg 未找到 — 剪辑功能和视频探测将不可用。\n"
            "运行 python install_ffmpeg.py 自动安装，或手动下载放到 adflow/ffmpeg/ 目录"
        )

    # API Key（按设置页当前选择的平台检查）
    api_key = ""
    try:
        from adflow.api.llm_adapter import get_llm_config
        api_key, _, _ = get_llm_config()
    except Exception:
        pass
    result["api_key"] = bool(api_key)
    if not result["api_key"]:
        result["warnings"].append(
            "AI 模型未配置 — AI 出片功能将不可用。\n"
            "请到「设置 → 🔌 API/模型」选择平台并填写 API Key"
        )

    # 数据库
    try:
        from adflow.db.connection import get_db
        db = get_db()
        result["db"] = True
    except Exception as e:
        result["errors"].append(f"数据库初始化失败: {e}")

    return result


def main():
    # 加载配置
    config.load()
    config.ensure_dirs()
    _setup_logging()
    logger = logging.getLogger("adflow")
    logger.info("AdFlow 启动中...")

    # 健康检查
    health = _health_check()

    # 启动 GUI
    app = QApplication(sys.argv)
    app.setApplicationName("AdFlow")
    app.setOrganizationName("AdFlow")

    # 全局样式
    app.setStyleSheet("""
        QMainWindow { background-color: #f5f5f5; }
        QTableWidget { font-size: 13px; gridline-color: #ddd; }
        QTableWidget::item { padding: 4px 8px; }
        QHeaderView::section {
            background-color: #e8e8e8;
            padding: 6px 8px;
            font-weight: bold;
            border: none;
            border-bottom: 2px solid #ccc;
        }
        QPushButton {
            padding: 6px 16px;
            border: 1px solid #ccc;
            border-radius: 4px;
            background-color: #fff;
            font-size: 13px;
        }
        QPushButton:hover { background-color: #e8f0fe; border-color: #4a90d9; }
        QPushButton:disabled { background-color: #eee; color: #999; }
        QLineEdit {
            padding: 6px 10px;
            border: 1px solid #ccc;
            border-radius: 4px;
            font-size: 13px;
        }
        QTabWidget::pane { border: 1px solid #ccc; background: #fff; }
        QTabBar::tab {
            padding: 8px 20px;
            border: 1px solid #ccc;
            border-bottom: none;
            background: #e8e8e8;
            margin-right: 2px;
        }
        QTabBar::tab:selected { background: #fff; border-bottom: 2px solid #4a90d9; }
        QStatusBar { background: #e8e8e8; border-top: 1px solid #ccc; }
    """)

    # ── 预下载 CLIP 模型（后台线程，不阻塞启动）──
    import threading
    def _preload_models():
        try:
            from adflow.engine.smart_mixer import SmartMixer
            SmartMixer.preload_clip()
        except Exception:
            pass
    threading.Thread(target=_preload_models, daemon=True).start()

    window = MainWindow()

    # 启动后显示健康检查结果
    if health["errors"]:
        QMessageBox.critical(
            window, "启动错误",
            "以下错误导致 AdFlow 无法正常启动:\n\n" + "\n".join(health["errors"]),
        )
        logger.error(f"启动失败: {health['errors']}")
        sys.exit(1)

    if health["warnings"]:
        QMessageBox.warning(
            window, "环境提示",
            "以下功能受限:\n\n" + "\n\n".join(health["warnings"]),
        )
        for w in health["warnings"]:
            logger.warning(w)

    status_parts = []
    if health["ffmpeg"]:
        status_parts.append("FFmpeg ✓")
    else:
        status_parts.append("FFmpeg ✗")
    if health["api_key"]:
        status_parts.append("AI ✓")
    else:
        status_parts.append("AI ✗")

    window.status_bar.showMessage(
        f"AdFlow v0.2.0  |  {' | '.join(status_parts)}  |  {config.db_path}"
    )

    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
