"""
FFmpeg / FFprobe 自动发现
- 搜索顺序：项目目录 → PATH → 常见安装路径
- 返回可执行文件的绝对路径
"""

import os
import shutil
import subprocess
from pathlib import Path
from functools import lru_cache


# 常见 Windows 安装路径
_COMMON_PATHS = [
    # 项目内
    None,  # 占位，动态计算
    # scoop
    os.path.expandvars(r"%USERPROFILE%\scoop\shims"),
    # winget
    os.path.expandvars(r"%LOCALAPPDATA%\Microsoft\WinGet\Packages"),
    # 手动安装常见路径
    r"C:\ffmpeg\bin",
    r"C:\Program Files\ffmpeg\bin",
    r"C:\Program Files (x86)\ffmpeg\bin",
    # chocolatey
    r"C:\ProgramData\chocolatey\bin",
    # 环境变量
    os.environ.get("FFMPEG_PATH", ""),
]


def _get_project_ffmpeg_dir() -> str:
    """获取项目内的 ffmpeg 目录"""
    root = Path(__file__).parent.parent.parent  # adflow/utils/ → adflow/ → project root
    ffmpeg_root = root / "ffmpeg"
    if ffmpeg_root.exists():
        # 搜索 bin 目录（适配 BtbN builds 的目录结构）
        for subdir in ffmpeg_root.iterdir():
            if subdir.is_dir():
                bin_dir = subdir / "bin"
                if bin_dir.exists():
                    return str(bin_dir)
    return ""


@lru_cache(maxsize=1)
def find_ffmpeg() -> str:
    """查找 ffmpeg.exe 的绝对路径"""
    exe_name = "ffmpeg.exe"

    # 1. 项目目录
    proj_dir = _get_project_ffmpeg_dir()
    if proj_dir:
        path = os.path.join(proj_dir, exe_name)
        if os.path.isfile(path):
            return path

    # 2. PATH 中查找
    found = shutil.which("ffmpeg")
    if found:
        return found

    # 3. 常见路径
    for base in _COMMON_PATHS:
        if not base:
            continue
        path = os.path.join(base, exe_name)
        if os.path.isfile(path):
            return path

        # 也检查子目录
        if os.path.isdir(base):
            for root, dirs, files in os.walk(base):
                if exe_name in files:
                    return os.path.join(root, exe_name)
                if root.count(os.sep) - base.count(os.sep) > 3:  # 不要搜太深（限 3 层目录）
                    break

    return ""


@lru_cache(maxsize=1)
def find_ffprobe() -> str:
    """查找 ffprobe.exe 的绝对路径"""
    exe_name = "ffprobe.exe"

    # 1. 与 ffmpeg 同目录
    ffmpeg_path = find_ffmpeg()
    if ffmpeg_path:
        probe_path = os.path.join(os.path.dirname(ffmpeg_path), exe_name)
        if os.path.isfile(probe_path):
            return probe_path

    # 2. PATH 中查找
    found = shutil.which("ffprobe")
    if found:
        return found

    return ""


def get_ffmpeg_cmd() -> str:
    """获取 ffmpeg 命令路径（用于 subprocess）"""
    return find_ffmpeg() or "ffmpeg"


def get_ffprobe_cmd() -> str:
    """获取 ffprobe 命令路径（用于 subprocess）"""
    return find_ffprobe() or "ffprobe"


def is_ffmpeg_available() -> bool:
    """检查 FFmpeg 是否可用"""
    return bool(find_ffmpeg())


def is_ffprobe_available() -> bool:
    """检查 FFprobe 是否可用"""
    return bool(find_ffprobe())


def check_ffmpeg() -> dict:
    """完整检查 FFmpeg 状态，返回详情"""
    ffmpeg = find_ffmpeg()
    ffprobe = find_ffprobe()

    result = {
        "ffmpeg_available": bool(ffmpeg),
        "ffprobe_available": bool(ffprobe),
        "ffmpeg_path": ffmpeg or "未找到",
        "ffprobe_path": ffprobe or "未找到",
    }

    if ffmpeg:
        try:
            r = subprocess.run([ffmpeg, "-version"], capture_output=True, text=True, encoding="utf-8", errors="replace", timeout=10)
            result["ffmpeg_version"] = r.stdout.split("\n")[0] if r.stdout else "未知"
        except Exception:
            result["ffmpeg_version"] = "无法检测"

    return result
