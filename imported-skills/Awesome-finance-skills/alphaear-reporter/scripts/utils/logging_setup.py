import os
import sys
from datetime import datetime
from typing import Optional

from loguru import logger


def setup_file_logging(
    run_id: str,
    log_dir: str = "logs",
    level: str = "INFO",
    retention: str = "10 days",
    rotation: str = "20 MB",
) -> str:
    """Configure Loguru to log to stderr + a per-run file.

    Returns the log file path.
    """
    os.makedirs(log_dir, exist_ok=True)

    # Remove default handler to avoid duplicate logs.
    logger.remove()

    # Console
    logger.add(sys.stderr, level=level, backtrace=False, diagnose=False)

    # File (safe for multi-thread via enqueue)
    log_path = os.path.join(log_dir, f"signalflux_{run_id}.log")
    logger.add(
        log_path,
        level=level,
        rotation=rotation,
        retention=retention,
        enqueue=True,
        backtrace=True,
        diagnose=False,
        encoding="utf-8",
    )
    return log_path


def make_run_id(prefix: Optional[str] = None) -> str:
    ts = datetime.now().strftime("%Y%m%d_%H%M%S")
    return f"{prefix}_{ts}" if prefix else ts
