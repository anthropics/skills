#!/usr/bin/env python3
"""Video Downloader Dependency Checker — Verify all requirements are met."""

import shutil
import subprocess
import sys
from pathlib import Path


def check(name, found, version=None, install_hint=None):
    if found:
        ver = f" ({version})" if version else ""
        print(f"  [OK]  {name}{ver}")
    else:
        hint = f" -> {install_hint}" if install_hint else ""
        print(f"  [--]  {name} — NOT FOUND{hint}")
    return found


def get_cmd_version(cmd, args=None):
    try:
        result = subprocess.run(
            [cmd] + (args or ["--version"]),
            capture_output=True, text=True, timeout=5,
        )
        return result.stdout.strip().splitlines()[0] if result.returncode == 0 else None
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None


def main():
    print("=" * 50)
    print("  Video Downloader — Dependency Check")
    print("=" * 50)
    all_ok = True

    # --- Python ---
    print(f"\nPython")
    py_ver = sys.version.split()[0]
    py_ok = sys.version_info >= (3, 10)
    if not check("Python 3.10+", py_ok, py_ver, "Install Python 3.10+ from python.org"):
        all_ok = False

    # --- CLI tools ---
    print(f"\nCLI Tools")

    ytdlp_ver = get_cmd_version("yt-dlp")
    if not check("yt-dlp", ytdlp_ver, ytdlp_ver, "pip install yt-dlp"):
        all_ok = False

    ffmpeg_ver = get_cmd_version("ffmpeg", ["-version"])
    if ffmpeg_ver:
        ffmpeg_ver = ffmpeg_ver.split("version ")[-1].split(" ")[0] if "version" in ffmpeg_ver else ffmpeg_ver[:40]
    if not check("ffmpeg", ffmpeg_ver, ffmpeg_ver, "brew install ffmpeg (macOS) / sudo apt install ffmpeg (Linux)"):
        all_ok = False

    ffprobe_ver = get_cmd_version("ffprobe", ["-version"])
    if not check("ffprobe", ffprobe_ver, install_hint="Included with ffmpeg"):
        all_ok = False

    # --- Skill installation ---
    print(f"\nClaude Code Skill")
    skill_path = Path.home() / ".claude" / "skills" / "video-downloader" / "SKILL.md"
    check("Skill installed", skill_path.exists(), str(skill_path) if skill_path.exists() else None,
          "Copy files to ~/.claude/skills/video-downloader/")

    # --- Summary ---
    print("\n" + "=" * 50)
    if all_ok:
        print("  All good! Ready to use Video Downloader.")
    else:
        print("  Some dependencies are missing.")
        print("  Quick install:")
        print("    pip install yt-dlp")
        print("    brew install ffmpeg  (macOS)")
    print("=" * 50)

    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
