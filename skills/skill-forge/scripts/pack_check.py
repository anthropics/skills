# -*- coding: utf-8 -*-
"""pack_check.py — 本技能自己出包 + 出包后验收（一条命令做到底，别再每次手写打包脚本）

用法：
  python scripts/pack_check.py                 # 用 SKILL.md 里的 version 出包
  python scripts/pack_check.py --version 2.1.0
  python scripts/pack_check.py --out <目录>     # zip 落点（默认技能目录的上一级）
  python scripts/pack_check.py --skip-tests    # 只出包（不建议；验收才算完）

它干六件事（顺序不能换）：
  1. 干净副本：排除运行产物与登录态（chrome_profile/recordings/evidence/produced/logs/test 生成物/*.bak*）
  2. 打 zip 到 --out，命名 forge-<version>_<md5前5>.zip，**平铺无顶层目录**（平台路径层级限制）
  3. 解压到临时目录，确认包里没有 profile/录制/证据条目
  4. 在解压副本上真跑五套测试 + 全部 .mjs 语法检查（缺 Chrome 时 hud/multitab 测试自我 SKIP）
  5. 脱敏 grep：邮箱/手机/Windows 用户路径 + 品牌/内部词，必须 0 命中
  6. 死文件检查：scripts/ 与 templates/ 下每个文件至少被别的文件引用一次

任一检查不过 → 退出码 1，并打印是哪一项。只扫文件清单不算验过。
"""
import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import zipfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)                      # 技能根目录
DEFAULT_OUT = os.path.dirname(ROOT)               # 默认 zip 落技能目录上一级（工作区根）

INCLUDE = ["SKILL.md", "功能台账.md", "_meta.json",
           "scripts", "templates", "assets", "references", "test"]
# 运行产物与测试现场生成物（zip/xlsx 由 run_node_test 现场生成，平台禁二进制不进包）
EXCLUDE_DIRS = {"chrome_profile", "recordings", "evidence", "produced", "logs",
                "__pycache__", "node_modules", "_out"}
EXCLUDE_GLOBS = ["*.bak*", "_t_*", "_tmp*", "_hud_profile", "_profile",
                 "big.zip", "roundtrip.zip", "mini.xlsx", "*.pyc"]

NODE_CANDIDATES = [os.environ.get("SF_NODE"), shutil.which("node")]
PYTHON_CANDIDATES = [sys.executable, shutil.which("python")]

# PII：邮箱 / 手机号 / Windows 用户路径（二进制与超 2MB 文件跳过）
PII = re.compile(r"[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.(com|cn)|\b1[3-9]\d{9}\b|[A-Za-z]:\\Users")
PII_OK = re.compile(r"example\.com|<你的|占位")
# 品牌与内部词：公开包必须 0 命中（防内网词回流）。下面是示例词，换成你自己的敏感词再用
BRAND = re.compile(r"示例品牌甲|example-brand|internal-project-x")


def first_existing(paths):
    for p in paths:
        if p and os.path.exists(p):
            return p
    return None


def build_stage(stage):
    """干净副本：直接放 stage 根（平铺，无顶层目录——平台限制路径 ≤3 段）"""
    for item in INCLUDE:
        src = os.path.join(ROOT, item)
        if not os.path.exists(src):
            continue
        dst = os.path.join(stage, item)
        if os.path.isdir(src):
            shutil.copytree(src, dst, ignore=shutil.ignore_patterns(*EXCLUDE_DIRS, *EXCLUDE_GLOBS))
        else:
            shutil.copy2(src, dst)
    # 包里给一份空台账，避免带上真实链路名
    with open(os.path.join(stage, "台账.csv"), "w", encoding="utf-8") as f:
        f.write("链路,版本,状态,最后变动,zip,失败次数,备注\r\n")
    return stage


def run(cmd, cwd):
    try:
        env = dict(os.environ)
        env["SF_NO_SHOT"] = "1"   # 验收跑测试时不生成截图，免得证据混进包的检查范围
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, env=env,
                           encoding="utf-8", errors="replace", timeout=900)
        out = (r.stdout or "").strip().splitlines()
        return r.returncode, (out[-1] if out else ""), (r.stderr or "")[-300:]
    except FileNotFoundError:
        return 127, "命令不存在", ""
    except subprocess.TimeoutExpired:
        return 124, "超时", ""


def main():
    # Windows 控制台默认 GBK，打 ✓/✗ 直接崩：强制 UTF-8 输出
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
        sys.stderr.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser()
    ap.add_argument("--version")
    ap.add_argument("--out", default=DEFAULT_OUT)
    ap.add_argument("--skip-tests", action="store_true")
    args = ap.parse_args()

    # 版本从 SKILL.md frontmatter 读（语义化 x.y.z），--version 可覆盖
    skill_md = open(os.path.join(ROOT, "SKILL.md"), encoding="utf-8").read()
    m = re.search(r"^version:\s*(\S+)", skill_md, re.M)
    version = args.version or (m.group(1) if m else "0.0.0")
    node = first_existing(NODE_CANDIDATES)
    py = first_existing(PYTHON_CANDIDATES)
    fails = []

    stage = tempfile.mkdtemp(prefix="forge_pack_")
    try:
        build_stage(stage)
        os.makedirs(args.out, exist_ok=True)
        tmp = os.path.join(args.out, f"forge-{version}.tmp.zip")
        # 不用 shutil.make_archive：Windows 下它写 "\" 分隔的条目名，平台要求 "/"（禁用 Compress-Archive 同理）
        with zipfile.ZipFile(tmp, "w", zipfile.ZIP_DEFLATED) as zf:
            for root, _dirs, files in os.walk(stage):
                for f in sorted(files):
                    fp = os.path.join(root, f)
                    zf.write(fp, os.path.relpath(fp, stage).replace(os.sep, "/"))
        md5 = hashlib.md5(open(tmp, "rb").read()).hexdigest()
        final = os.path.join(args.out, f"forge-{version}_{md5[:5]}.zip")
        os.replace(tmp, final)
        size = os.path.getsize(final)
        with zipfile.ZipFile(final) as z:
            names = [n for n in z.namelist() if not n.endswith("/")]
            leaked = [n for n in names if any(x in n for x in
                      ("chrome_profile", "recordings/", "evidence/", "produced/", "logs/"))]
            wrapped = [n for n in names if n.startswith("/") or ".." in n or "\\" in n]
            deep = [n for n in names if n.count("/") > 2]
            print(f"包：{os.path.basename(final)}")
            print(f"大小 {size/1024:.0f} KB｜MD5 {md5}｜文件 {len(names)}")
            if leaked:
                fails.append(f"包内混入运行产物：{leaked[:5]}")
                print(f"✗ 包内混入运行产物：{leaked[:5]}")
            if wrapped or deep:
                fails.append(f"包条目路径不合规（须平铺且 ≤3 段）：{(wrapped + deep)[:5]}")
                print(f"✗ 包条目路径不合规（须平铺且 ≤3 段）：{(wrapped + deep)[:5]}")
            verify = os.path.join(stage, "verify")
            z.extractall(verify)
        V = verify

        # == 元数据 / 免责声明（缺一项就是 FAIL）==
        print("== 元数据与免责 ==")
        vs = open(os.path.join(V, "SKILL.md"), encoding="utf-8").read()
        fm = vs.split("---")[1] if vs.startswith("---") else ""
        miss_fm = [k for k in ("author:", "source:", "license:", "risk-level:", "allowed-tools:", "permissions:", "forbidden:") if k not in fm]
        if miss_fm:
            fails.append(f"SKILL.md frontmatter 缺 {miss_fm}")
            print(f"  ✗ SKILL.md frontmatter 缺 {miss_fm}")
        else:
            print("  ✓ frontmatter：author/source/license/risk-level/allowed-tools/permissions/forbidden 齐")
        if "使用范围与免责声明" not in vs or "数据与责任切割" not in vs:
            fails.append("SKILL.md 缺免责声明（使用范围与免责声明 / 数据与责任切割）")
            print("  ✗ SKILL.md 缺免责声明")
        else:
            print("  ✓ 免责声明：使用范围与免责 + 数据与责任切割 已在正文")
        if "≥ 22" not in vs:
            fails.append("SKILL.md 未写 Node ≥ 22（用内置 WebSocket 的硬要求）")
            print("  ✗ SKILL.md 未写 Node ≥ 22")
        else:
            print("  ✓ 依赖说明：Node ≥ 22 / Python 标准库 / 零第三方包 已写")
        if not re.search(r'^build: "\d{14}"', vs, re.M):
            fails.append("SKILL.md 缺 build 时间戳（14 位）")
            print("  ✗ SKILL.md 缺 build 时间戳")
        else:
            print("  ✓ 版本：语义化 version + build 时间戳双轨")

        if not args.skip_tests:
            print("== 解压副本跑测试 ==")
            suites = []
            if node:
                suites += [[node, "test/run_node_test.mjs"], [node, "test/run_forge_v2_test.mjs"],
                           [node, "test/run_hud_test.mjs"], [node, "test/run_multitab_test.mjs"]]
            else:
                fails.append("找不到 node，测试没跑")
            suites += [[py, "-I", "test/run_offline_test.py"]]
            for cmd in suites:
                code, last, err = run(cmd, V)
                print(f"  {os.path.basename(cmd[-1])} → exit={code} | {last or err}")
                if code != 0:
                    fails.append(f"{os.path.basename(cmd[-1])} exit={code}")

            bad_syntax = 0
            if node:
                for d in ("scripts", "test", "assets"):
                    p = os.path.join(V, d)
                    if not os.path.isdir(p):
                        continue
                    for f in sorted(os.listdir(p)):
                        if f.endswith(".mjs"):
                            code, _, err = run([node, "--check", os.path.join(d, f)], V)
                            if code != 0:
                                bad_syntax += 1
                                print(f"  语法 FAIL {d}/{f}: {err[:120]}")
            print(f"  语法失败数={bad_syntax}")
            if bad_syntax:
                fails.append(f"{bad_syntax} 个 .mjs 语法错")

        # 扫的是包内容本身，不是跑过测试的解压目录——测试会在解压目录里现场生成 zip/xlsx，别误伤
        BIN_EXT = {".png", ".jpg", ".jpeg", ".gif", ".webp", ".ico", ".zip", ".xlsx",
                   ".xls", ".docx", ".pdf", ".db", ".woff", ".woff2", ".ttf"}
        hits, bin_hits = [], []
        texts = {}
        with zipfile.ZipFile(final) as z:
            znames = [n for n in z.namelist() if not n.endswith("/")]
            for n in znames:
                if n == "scripts/pack_check.py":
                    continue  # 检测器自己带着品牌词正则定义，跳过自身（真回流会在别的文件命中）
                if os.path.splitext(n)[1].lower() in BIN_EXT:
                    bin_hits.append(n)  # 平台上传会静默丢弃二进制条目
                    continue
                data = z.read(n)
                if len(data) > 2_000_000:
                    continue
                txt = data.decode("utf-8", errors="ignore")
                if n.endswith((".md", ".mjs", ".py", ".json")):
                    texts[n] = txt
                for i, line in enumerate(txt.splitlines(), 1):
                    if (PII.search(line) and not PII_OK.search(line)) or BRAND.search(line):
                        hits.append(f"{n}:{i}: {line.strip()[:100]}")
        if bin_hits:
            for b in bin_hits:
                print(f"  ✗ 二进制条目（平台会静默丢弃）：{b}")
            fails.append(f"包内含二进制（平台上传会静默丢弃）：{bin_hits}")
        print(f"== 脱敏（PII + 品牌/内部词）：命中 {len(hits)} 处 ==")
        for h in hits[:8]:
            print("  " + h)
        if hits:
            fails.append(f"脱敏命中 {len(hits)} 处")

        dead = []
        for d in ("scripts", "templates"):
            for n in znames:
                prefix = d + "/"
                if not n.startswith(prefix) or "/" in n[len(prefix):]:
                    continue  # 只查 scripts/ 与 templates/ 顶层文件
                base_name = n[len(prefix):]
                if not base_name.endswith((".mjs", ".py", ".md")):
                    continue
                if not any(base_name in v for k, v in texts.items() if k != n):
                    dead.append(n)
        print("== 死文件（没人引用）==", dead if dead else "无")
        if dead:
            fails.append(f"死文件：{dead}")
    finally:
        shutil.rmtree(stage, ignore_errors=True)

    if fails:
        print("\n✗ 验收没过：")
        for f in fails:
            print("  - " + f)
        return 1
    print("\n✓ 出包 + 验收全过（测试 / 语法 / 脱敏 / 死文件 / 包内无运行产物 / 平铺无二进制）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
