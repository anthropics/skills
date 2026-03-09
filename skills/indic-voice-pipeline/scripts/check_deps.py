#!/usr/bin/env python3
"""Whisper Transcribe Dependency Checker — Verify all requirements are met."""

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
            capture_output=True, text=True, timeout=10,
        )
        return result.stdout.strip().splitlines()[0] if result.returncode == 0 else None
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None


def check_python_package(pkg_name):
    try:
        result = subprocess.run(
            [sys.executable, "-c", f"import {pkg_name}; print({pkg_name}.__version__ if hasattr({pkg_name}, '__version__') else 'installed')"],
            capture_output=True, text=True, timeout=10,
        )
        if result.returncode == 0:
            return result.stdout.strip()
        return None
    except (FileNotFoundError, subprocess.TimeoutExpired):
        return None


def main():
    print("=" * 50)
    print("  Whisper Transcribe — Dependency Check")
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

    ffmpeg_ver = get_cmd_version("ffmpeg", ["-version"])
    if ffmpeg_ver:
        ffmpeg_ver = ffmpeg_ver.split("version ")[-1].split(" ")[0] if "version" in ffmpeg_ver else ffmpeg_ver[:40]
    if not check("ffmpeg", ffmpeg_ver, ffmpeg_ver, "brew install ffmpeg"):
        all_ok = False

    ffprobe_ver = get_cmd_version("ffprobe", ["-version"])
    if not check("ffprobe", ffprobe_ver, install_hint="Included with ffmpeg"):
        all_ok = False

    # --- Python packages ---
    print(f"\nPython Packages")

    whisper_ver = check_python_package("whisper")
    if not check("openai-whisper", whisper_ver, whisper_ver, "pip install openai-whisper"):
        all_ok = False

    torch_ver = check_python_package("torch")
    if not check("torch (PyTorch)", torch_ver, torch_ver, "pip install torch"):
        all_ok = False

    transformers_ver = check_python_package("transformers")
    if not check("transformers (HuggingFace)", transformers_ver, transformers_ver, "pip install transformers accelerate"):
        all_ok = False

    # --- Skill installation ---
    print(f"\nClaude Code Skill")
    skill_path = Path.home() / ".claude" / "skills" / "whisper-transcribe" / "SKILL.md"
    check("Skill installed", skill_path.exists(), str(skill_path) if skill_path.exists() else None,
          "Copy files to ~/.claude/skills/whisper-transcribe/")

    # --- Summary ---
    print("\n" + "=" * 50)
    if all_ok:
        print("  All good! Ready to use Whisper Transcribe.")
    else:
        print("  Some dependencies are missing.")
        print("  Quick install:")
        print("    pip install openai-whisper")
        print("    brew install ffmpeg  (macOS)")
    print("=" * 50)

    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
