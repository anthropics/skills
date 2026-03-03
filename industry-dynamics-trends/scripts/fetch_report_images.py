#!/usr/bin/env python3
"""
行业动态报告配图拉取脚本 v2 — 三级策略降级
========================================
策略 A（HTML 解析）：直接 HTTP 获取页面，解析 og:image / twitter:image / 大图 src。
策略 B（浏览器渲染）：可选，需安装 playwright；渲染 JS 页面后提取图片 URL 或截图。
策略 C（截图兜底）：Browser 截图保存为本地图片，报告中作为配图使用。

每条策略内部均有超时 + 重试 + 失败即跳过。
脚本通过 manifest.json 描述任务，AI 生成 manifest，人工或 CI 执行脚本。

manifest.json 格式（放在 assets/images/<report_slug>/manifest.json）：
[
  {
    "filename": "01-quickcut.png",
    "label": "Adobe Firefly Quick Cut 界面",
    "image_url": "https://...",          // 直链图片 URL（已知时填）
    "source_url": "https://blog.adobe.com/..." // 来源页 URL（未知 image_url 时用）
  },
  {
    "filename": "02-codex.png",
    "label": "Figma Codex 工作流",
    "image_url": null,
    "source_url": "https://www.figma.com/blog/..."
  }
]

执行：
  python3 scripts/fetch_report_images.py --report 2026-03-ai-for-design
  python3 scripts/fetch_report_images.py --report 2026-03-ai-for-design --strategy b  # 强制 playwright
  python3 scripts/fetch_report_images.py --report 2026-03-ai-for-design --dry-run     # 只打印计划
"""
from __future__ import annotations

import argparse
import json
import re
import sys
import time
from html.parser import HTMLParser
from pathlib import Path
from typing import Optional
from urllib.parse import urljoin, urlparse

# ── 可选依赖 ──────────────────────────────────────────────────────────────────
try:
    import requests
    from requests.adapters import HTTPAdapter
    HAS_REQUESTS = True
except ImportError:
    HAS_REQUESTS = False

try:
    from playwright.sync_api import sync_playwright
    HAS_PLAYWRIGHT = True
except ImportError:
    HAS_PLAYWRIGHT = False

# ── 常量 ──────────────────────────────────────────────────────────────────────
UA = "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0 Safari/537.36"
DEFAULT_TIMEOUT = 12
DEFAULT_MAX_RETRIES = 2
RETRY_DELAY = 2   # 秒，线性退避（第 n 次重试等 n * RETRY_DELAY 秒）

# ── 工具函数 ──────────────────────────────────────────────────────────────────

def log(msg: str, err: bool = False) -> None:
    print(msg, file=sys.stderr if err else sys.stdout, flush=True)


def with_retry(fn, max_retries: int, label: str):
    """执行 fn()，失败后最多重试 max_retries 次；成功返回结果，全部失败返回 None。"""
    for attempt in range(max_retries + 1):
        if attempt > 0:
            wait = RETRY_DELAY * attempt
            log(f"    retry {attempt}/{max_retries} (wait {wait}s)…")
            time.sleep(wait)
        try:
            result = fn()
            if result is not None:
                return result
        except Exception as e:
            log(f"    attempt {attempt + 1} error [{label}]: {e}", err=True)
    return None


def http_get_bytes(url: str, timeout: int) -> Optional[bytes]:
    """HTTP GET，返回内容字节；失败返回 None。"""
    if HAS_REQUESTS:
        s = requests.Session()
        s.mount("https://", HTTPAdapter(max_retries=0))
        s.headers.update({"User-Agent": UA})
        r = s.get(url, timeout=timeout, stream=True)
        r.raise_for_status()
        return r.content
    else:
        import urllib.request
        req = urllib.request.Request(url, headers={"User-Agent": UA})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return resp.read()


def http_get_text(url: str, timeout: int) -> Optional[str]:
    """HTTP GET HTML 文本。"""
    raw = http_get_bytes(url, timeout)
    if raw is None:
        return None
    for enc in ("utf-8", "latin-1"):
        try:
            return raw.decode(enc)
        except UnicodeDecodeError:
            continue
    return raw.decode("utf-8", errors="replace")


# ── HTML 解析：提取图片 URL ────────────────────────────────────────────────────

class ImageExtractor(HTMLParser):
    """从 HTML 中提取 og:image、twitter:image、最大 <img src>。"""

    def __init__(self, base_url: str):
        super().__init__()
        self.base_url = base_url
        self.og_image: Optional[str] = None
        self.twitter_image: Optional[str] = None
        self.imgs: list[str] = []

    def handle_starttag(self, tag: str, attrs):
        d = dict(attrs)
        if tag == "meta":
            prop = d.get("property", "") or d.get("name", "")
            content = d.get("content", "")
            if prop == "og:image" and content:
                self.og_image = urljoin(self.base_url, content)
            elif prop in ("twitter:image", "twitter:image:src") and content:
                self.twitter_image = urljoin(self.base_url, content)
        elif tag == "img":
            src = d.get("src", "")
            if src and not src.startswith("data:"):
                self.imgs.append(urljoin(self.base_url, src))

    def best(self) -> Optional[str]:
        """返回最优图片 URL：og > twitter > 首个非 SVG/icon img。"""
        if self.og_image:
            return self.og_image
        if self.twitter_image:
            return self.twitter_image
        for img in self.imgs:
            p = urlparse(img).path.lower()
            if not any(p.endswith(x) for x in (".svg", ".ico", ".gif")):
                return img
        return None


# ── 三级策略 ──────────────────────────────────────────────────────────────────

def strategy_a_direct(image_url: str, dest: Path, timeout: int, max_retries: int) -> bool:
    """A0：已知图片直链，直接下载。"""
    def _fetch():
        data = http_get_bytes(image_url, timeout)
        if data and len(data) > 500:
            dest.write_bytes(data)
            return True
        return None
    result = with_retry(_fetch, max_retries, f"A0 direct {image_url[:60]}")
    return result is True


def strategy_a_parse(source_url: str, dest: Path, timeout: int, max_retries: int) -> bool:
    """A1：HTTP 获取页面 HTML，解析 og:image 等，再下载图片。"""
    def _find_url():
        html = http_get_text(source_url, timeout)
        if not html:
            return None
        parser = ImageExtractor(source_url)
        parser.feed(html)
        return parser.best()

    log(f"  [A] HTML parse: {source_url[:80]}")
    img_url = with_retry(_find_url, max_retries, f"A parse {source_url[:60]}")
    if not img_url:
        log("  [A] no image URL found in HTML", err=True)
        return False
    log(f"  [A] found image URL: {img_url[:80]}")
    return strategy_a_direct(img_url, dest, timeout, max_retries)


def strategy_b_playwright(source_url: str, dest: Path, timeout: int, max_retries: int) -> bool:
    """B：Playwright 渲染页面，提取 og:image（JS 渲染后），失败则截图兜底。"""
    if not HAS_PLAYWRIGHT:
        log("  [B] playwright not installed, skip", err=True)
        return False

    log(f"  [B] playwright: {source_url[:80]}")

    def _run():
        with sync_playwright() as pw:
            browser = pw.chromium.launch(headless=True)
            page = browser.new_page(user_agent=UA)
            page.goto(source_url, timeout=timeout * 1000, wait_until="domcontentloaded")
            page.wait_for_timeout(2000)  # 等 JS 渲染

            # 尝试提取 og:image
            og = page.evaluate(
                "() => (document.querySelector('meta[property=\"og:image\"]') || {}).content"
            )
            if og:
                img_url = urljoin(source_url, og)
                browser.close()
                log(f"  [B] og:image from rendered DOM: {img_url[:80]}")
                return ("url", img_url)

            # 兜底：截图
            screenshot = page.screenshot(full_page=False, type="png")
            browser.close()
            if screenshot and len(screenshot) > 1000:
                dest.write_bytes(screenshot)
                return ("screenshot", str(dest))
            return None

    result = with_retry(_run, max_retries, f"B playwright {source_url[:60]}")
    if result is None:
        return False
    kind, val = result
    if kind == "url":
        return strategy_a_direct(val, dest, timeout, max_retries)
    # kind == "screenshot"：已写入 dest
    log(f"  [B] screenshot saved: {dest.name}")
    return True


def strategy_c_skip(label: str) -> bool:
    """C：三级均失败，跳过并记录，不写文件。"""
    log(f"  [C] all strategies failed for [{label}], skip (暂无可用配图)")
    return False


# ── 主逻辑 ────────────────────────────────────────────────────────────────────

def load_manifest(manifest_path: Path) -> list[dict]:
    """读取 manifest.json；若不存在则返回空列表（兼容旧式硬编码清单）。"""
    if not manifest_path.exists():
        return []
    with manifest_path.open(encoding="utf-8") as f:
        return json.load(f)


def fetch_entry(entry: dict, out_dir: Path, timeout: int, max_retries: int, strategy: str) -> bool:
    """对单条 manifest entry 执行三级策略。"""
    fname    = entry["filename"]
    label    = entry.get("label", fname)
    img_url  = entry.get("image_url") or ""
    src_url  = entry.get("source_url") or ""
    dest     = out_dir / fname

    log(f"\n→ [{label}]  dest={fname}")

    # 强制策略 b 时跳过 A
    if strategy != "b":
        # A0：已知直链
        if img_url:
            log(f"  [A0] direct URL: {img_url[:80]}")
            if strategy_a_direct(img_url, dest, timeout, max_retries):
                log(f"  ✓ A0 OK ({dest.stat().st_size} bytes)")
                return True
            log("  A0 failed, try A1…", err=True)

        # A1：HTML 解析
        if src_url:
            if strategy_a_parse(src_url, dest, timeout, max_retries):
                log(f"  ✓ A1 OK ({dest.stat().st_size} bytes)")
                return True
            log("  A1 failed, try B…", err=True)

    # B：Playwright 渲染（有 source_url 才能进）
    if src_url and strategy in ("auto", "b"):
        if strategy_b_playwright(src_url, dest, timeout, max_retries):
            log(f"  ✓ B OK ({dest.stat().st_size} bytes)")
            return True

    # C：跳过
    return strategy_c_skip(label)


def main() -> int:
    ap = argparse.ArgumentParser(description="Multi-strategy report image fetcher")
    ap.add_argument("--report",      required=True, help="Report slug, e.g. 2026-03-ai-for-design")
    ap.add_argument("--timeout",     type=int, default=DEFAULT_TIMEOUT)
    ap.add_argument("--max-retries", type=int, default=DEFAULT_MAX_RETRIES)
    ap.add_argument("--strategy",    choices=["auto", "a", "b"], default="auto",
                    help="auto=A→B降级; a=仅 HTML 解析; b=直接用 playwright")
    ap.add_argument("--dry-run",     action="store_true", help="仅打印计划，不下载")
    args = ap.parse_args()

    skill_root = Path(__file__).resolve().parent.parent
    out_dir    = skill_root / "assets" / "images" / args.report
    out_dir.mkdir(parents=True, exist_ok=True)

    manifest_path = out_dir / "manifest.json"
    entries = load_manifest(manifest_path)

    # 兼容旧式硬编码（manifest 不存在时的示例）
    if not entries:
        log(f"  manifest.json not found at {manifest_path}, using empty list.")
        log("  → 请在 manifest.json 中定义图片清单后重试。")
        return 1

    if args.dry_run:
        log(f"[dry-run] {len(entries)} entries for {args.report}:")
        for e in entries:
            log(f"  {e['filename']:30s} image_url={bool(e.get('image_url'))} source_url={bool(e.get('source_url'))}")
        return 0

    log(f"Fetching {len(entries)} images for [{args.report}] | strategy={args.strategy} "
        f"timeout={args.timeout}s retries={args.max_retries}\n")

    ok = fail = 0
    for entry in entries:
        success = fetch_entry(entry, out_dir, args.timeout, args.max_retries, args.strategy)
        if success:
            ok += 1
        else:
            fail += 1
            dest = out_dir / entry["filename"]
            if dest.exists():
                dest.unlink()

    log(f"\n{'='*50}")
    log(f"Done: {ok} ok, {fail} skipped (暂无可用配图)")
    return 0 if fail == 0 else 2  # exit 2 = partial success


if __name__ == "__main__":
    sys.exit(main())
