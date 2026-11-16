# -*- coding: utf-8 -*-
"""AdFlow skill 一键装环境。

用法:
    python setup_env.py --deps     装 Python 依赖（走清华镜像，国内快）
    python setup_env.py --ffmpeg   下载安装 ffmpeg（约 80MB，一次性）
    python setup_env.py --all      上面两样都装

装完跑 python check_env.py 复查。
"""
import os
import subprocess
import sys
import urllib.request
import zipfile

sys.stdout.reconfigure(errors="replace")

SKILL_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ENGINE = os.path.join(SKILL_ROOT, "engine")

# gyan.dev 的 ffmpeg 稳定版（Windows 通用，解压即用）
FFMPEG_URL = "https://www.gyan.dev/ffmpeg/builds/ffmpeg-release-essentials.zip"
MIRROR = "https://pypi.tuna.tsinghua.edu.cn/simple"


def install_deps():
    print("第 1 步: 安装 Python 依赖（走清华镜像，几分钟）...")
    req = os.path.join(ENGINE, "requirements.txt")
    if not os.path.isfile(req):
        print("[X] 找不到 " + req)
        sys.exit(1)
    cmd = [sys.executable, "-m", "pip", "install", "-r", req,
           "-i", MIRROR, "--disable-pip-version-check"]
    r = subprocess.call(cmd)
    if r != 0:
        print("\n镜像装失败，换官方源再试一次...")
        r = subprocess.call(
            [sys.executable, "-m", "pip", "install", "-r", req,
             "--disable-pip-version-check"])
    if r != 0:
        print("[X] 依赖安装失败。把上面报错那段截图发给 Claude 看原因")
        sys.exit(1)
    print("[OK] Python 依赖装好了")


def install_ffmpeg():
    # 已装就跳过
    from shutil import which
    if which("ffmpeg"):
        print("[OK] ffmpeg 已在系统里，不用重复安装")
        return
    ff_root = os.path.join(ENGINE, "ffmpeg")
    if os.path.isdir(ff_root):
        for sub in os.listdir(ff_root):
            if os.path.isfile(os.path.join(ff_root, sub, "bin", "ffmpeg.exe")):
                print("[OK] ffmpeg 已装在 engine/ffmpeg 里，不用重复安装")
                return

    print("第 2 步: 下载 ffmpeg（约 80MB，耐心等进度）...")
    zip_path = os.path.join(ENGINE, "ffmpeg_download.zip")

    def _progress(block_num: int, block_size: int, total: int):
        # urlretrieve 回调只有 3 个参数（block_num/block_size/total）
        done = min(block_num * block_size, total)
        print("\r下载中 %d%% (%d / %d MB)" % (
            done * 100 // max(total, 1), done // 1048576,
            total // 1048576), end="")

    try:
        urllib.request.urlretrieve(FFMPEG_URL, zip_path, _progress)
        print()
    except Exception as e:
        print("\n[X] 下载失败: %s" % e)
        print("手动装法（也简单）: 看 references/beginner-guide.md 的 ffmpeg 一节")
        sys.exit(1)

    print("解压中...")
    try:
        with zipfile.ZipFile(zip_path) as zf:
            zf.extractall(ff_root)
    except Exception as e:
        print("[X] 解压失败: %s" % e)
        sys.exit(1)
    finally:
        try:
            os.remove(zip_path)
        except OSError:
            pass

    # 确认解压出了 bin/ffmpeg.exe（zip 内是 ffmpeg-x.x-essentials_build/bin/...）
    found = False
    for root, _dirs, files in os.walk(ff_root):
        if "ffmpeg.exe" in files:
            found = True
            break
    if found:
        print("[OK] ffmpeg 装好了，位置: " + ff_root)
    else:
        print("[X] 解压完成但没找到 ffmpeg.exe，手动装法看 "
              "references/beginner-guide.md")
        sys.exit(1)


def main():
    args = sys.argv[1:]
    if not args or args == ["--all"]:
        install_deps()
        install_ffmpeg()
    elif "--deps" in args:
        install_deps()
    elif "--ffmpeg" in args:
        install_ffmpeg()
    else:
        print(__doc__)
        sys.exit(1)
    print("\n最后一步: 跑 python check_env.py 复查，全 [OK] 就能出片了")


if __name__ == "__main__":
    main()
