#!/usr/bin/env python3
"""
步骤二：按 articles.json 清单逐篇下载文章（正文 HTML + 图片 + Markdown + 元数据）。
用法:
  python3 step2_download_articles.py                 # 下载 articles.json 里的全部文章（可中断、可续跑）
  python3 step2_download_articles.py --url <链接>    # 单篇测试
  python3 step2_download_articles.py --limit 5       # 只下前 5 篇（试跑）
输出目录: output/YYYY-MM-DD_标题/
    article.md        Markdown（图片已改成本地相对路径）
    article.html      清理过的正文 HTML（图片本地路径）
    page_raw.html     微信原始整页 HTML（备份，图片仍指向微信 CDN）
    meta.json         标题/作者/时间/原链接/图片清单
    images/           所有图片
"""
import argparse, json, random, re, sys, time
from pathlib import Path
from urllib.parse import urlparse, parse_qs
from bs4 import BeautifulSoup
from markdownify import markdownify as md
from playwright.sync_api import sync_playwright

BASE = Path(__file__).parent
OUT = BASE / "output"
STATE_FILE = BASE / "mp_login_state.json"
UA = ("Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/136.0.0.0 Safari/537.36")

def safe_name(s, n=60):
    s = re.sub(r'[\\/:*?"<>|\r\n\t]+', "_", s or "").strip(" ._")
    return (s[:n] or "untitled")

def img_ext(url, content_type=""):
    q = parse_qs(urlparse(url).query)
    fmt = (q.get("wx_fmt") or [""])[0].lower()
    if fmt in ("jpeg", "jpg"): return "jpg"
    if fmt in ("png", "gif", "webp", "bmp", "svg"): return fmt
    if "png" in content_type: return "png"
    if "gif" in content_type: return "gif"
    if "webp" in content_type: return "webp"
    return "jpg"

def get_var(html, name):
    m = re.search(r'var\s+' + name + r'\s*=\s*(?:htmlDecode\()?["\']([^"\']*)["\']', html)
    return m.group(1) if m else ""

def fetch_one(ctx, url, out_dir_hint=None, retries=3):
    page = ctx.new_page()
    try:
        for attempt in range(retries):
            page.goto(url, wait_until="domcontentloaded", timeout=60000)
            page.wait_for_timeout(2500)
            html = page.content()
            if "环境异常" in html and "js_content" not in html:
                print("    !! 触发验证页，等待 90 秒后重试 ...")
                time.sleep(90); continue
            break
        soup = BeautifulSoup(html, "html.parser")
        content = soup.select_one("#js_content")
        if content is None:
            # 已删除 / 违规 / 不存在
            tip = soup.select_one(".weui-msg__title, .global_error_msg, #js_top_ad_area, .text_area")
            reason = tip.get_text(strip=True) if tip else "未找到正文(#js_content)"
            return {"ok": False, "reason": reason[:100], "raw": html}

        title = (soup.select_one("#activity-name") or soup.select_one("h1"))
        title = title.get_text(strip=True) if title else get_var(html, "msg_title")
        author = (soup.select_one("#js_author_name") or soup.select_one("#meta_content .rich_media_meta_text"))
        author = author.get_text(strip=True) if author else get_var(html, "author")
        nickname = soup.select_one("#js_name")
        nickname = nickname.get_text(strip=True) if nickname else get_var(html, "nickname")
        create_time = get_var(html, "createTime")
        if not create_time:
            pt = soup.select_one("#publish_time")
            create_time = pt.get_text(strip=True) if pt else ""
        ct = get_var(html, "ct")
        date = create_time[:10] if create_time else (time.strftime("%Y-%m-%d", time.localtime(int(ct))) if ct.isdigit() else "0000-00-00")
        digest = get_var(html, "msg_desc")
        cover = get_var(html, "msg_cdn_url")

        # 目录
        d = OUT / f"{date}_{safe_name(title)}"
        d.mkdir(parents=True, exist_ok=True)
        (d / "images").mkdir(exist_ok=True)
        (d / "page_raw.html").write_text(html, "utf-8")

        # 图片：收集 + 下载 + 改写
        images = []
        def download(src, idx, tag="img"):
            if not src or src.startswith("data:"): return None
            if src.startswith("//"): src = "https:" + src
            try:
                r = ctx.request.get(src, headers={"Referer": "https://mp.weixin.qq.com/"}, timeout=60000)
                if r.status != 200 or len(r.body()) < 100: 
                    print(f"    !! 图片下载失败 {r.status}: {src[:80]}"); return None
                ext = img_ext(src, r.headers.get("content-type", ""))
                fn = f"{tag}_{idx:03d}.{ext}"
                (d / "images" / fn).write_bytes(r.body())
                images.append({"file": f"images/{fn}", "src": src})
                return f"images/{fn}"
            except Exception as e:
                print(f"    !! 图片异常: {e} {src[:80]}"); return None

        for i, img in enumerate(content.find_all("img"), 1):
            src = img.get("data-src") or img.get("src")
            local = download(src, i)
            for a in ["data-src", "data-w", "data-ratio", "data-type", "data-s", "data-backh", "data-backw",
                      "data-croporisrc", "data-cropx1", "data-cropx2", "data-cropy1", "data-cropy2", "data-fail", "data-imgfileid", "crossorigin"]:
                img.attrs.pop(a, None)
            img.attrs.pop("style", None) if img.get("style") and "visibility" in img.get("style") else None
            if local: img["src"] = local
            elif src: img["src"] = src
            time.sleep(random.uniform(0.2, 0.6))

        # 背景图（section style="background-image:url(...)"）也尽量抓下来
        bg_i = 0
        for el in content.find_all(style=re.compile(r"background-image")):
            m = re.search(r'url\((["\']?)(https?://mmbiz[^"\')]+)\1\)', el["style"])
            if m:
                bg_i += 1
                local = download(m.group(2), bg_i, "bg")
                if local: el["style"] = el["style"].replace(m.group(2), local)

        if cover:
            download(cover, 0, "cover")

        # 去掉隐藏样式，导出正文 HTML
        if content.get("style"):
            content["style"] = re.sub(r"visibility\s*:\s*hidden;?|opacity\s*:\s*0;?", "", content["style"])
        content_html = str(content)
        page_html = f"""<!DOCTYPE html><html><head><meta charset="utf-8"><title>{title}</title>
<style>body{{max-width:680px;margin:20px auto;padding:0 16px;font:16px/1.75 -apple-system,Helvetica,Arial,sans-serif;color:#333}} img{{max-width:100%;height:auto}}</style></head>
<body><h1>{title}</h1><p style="color:#888">{nickname} · {author} · {create_time}<br><a href="{url}">{url}</a></p>
{content_html}</body></html>"""
        (d / "article.html").write_text(page_html, "utf-8")

        body_md = md(content_html, heading_style="ATX", strip=["script", "style"])
        body_md = re.sub(r"\n{3,}", "\n\n", body_md).strip()
        front = f"---\ntitle: \"{title}\"\naccount: \"{nickname}\"\nauthor: \"{author}\"\ndate: \"{create_time}\"\nsource: \"{url}\"\ndigest: \"{digest}\"\n---\n\n# {title}\n\n"
        (d / "article.md").write_text(front + body_md + "\n", "utf-8")

        meta = {"title": title, "account": nickname, "author": author, "create_time": create_time,
                "date": date, "url": url, "digest": digest, "cover": cover, "images": images, "dir": str(d.relative_to(BASE))}
        (d / "meta.json").write_text(json.dumps(meta, ensure_ascii=False, indent=2), "utf-8")
        return {"ok": True, "dir": d, "title": title, "n_img": len(images)}
    finally:
        page.close()

def launch_browser(p, headless):
    for ch in ("chrome", "msedge", None):
        try:
            return p.chromium.launch(headless=headless, channel=ch) if ch else p.chromium.launch(headless=headless)
        except Exception:
            continue
    raise SystemExit("找不到可用浏览器，请安装 Google Chrome 或运行: playwright install chromium")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--url"); ap.add_argument("--limit", type=int); ap.add_argument("--headed", action="store_true"); ap.add_argument("--include-deleted", action="store_true")
    a = ap.parse_args()
    OUT.mkdir(exist_ok=True)

    if a.url:
        items = [{"title": "", "link": a.url}]
    else:
        items = json.loads((BASE / "articles.json").read_text("utf-8"))
        if a.limit: items = items[:a.limit]

    done_file = BASE / "download_log.json"
    log = json.loads(done_file.read_text("utf-8")) if done_file.exists() else {}

    with sync_playwright() as p:
        b = launch_browser(p, headless=not a.headed)
        ctx = b.new_context(user_agent=UA, storage_state=str(STATE_FILE) if STATE_FILE.exists() else None)
        total = len(items)
        for i, it in enumerate(items, 1):
            url = it["link"]
            if not url:
                continue
            if url in log and log[url].get("ok"):
                continue
            if it.get("is_deleted") and not a.include_deleted:
                log[url] = {"ok": False, "reason": "已删除(后台标记 is_deleted, 跳过)", "title": it.get("title"), "date": it.get("date")}
                continue
            print(f"[{i}/{total}] {it.get('date','')} {it.get('title','')[:40]}")
            try:
                r = fetch_one(ctx, url)
            except Exception as e:
                r = {"ok": False, "reason": f"exception: {e}"[:200]}
            if r["ok"]:
                print(f"    ✓ {r['n_img']} 张图 -> {r['dir'].name}")
                log[url] = {"ok": True, "dir": r["dir"].name, "title": r["title"]}
            else:
                print(f"    ✗ 失败: {r['reason']}")
                log[url] = {"ok": False, "reason": r["reason"], "title": it.get("title")}
                if r.get("raw"):
                    fd = OUT / "_failed"; fd.mkdir(exist_ok=True)
                    (fd / f"{safe_name(it.get('title') or url[-20:])}.html").write_text(r["raw"], "utf-8")
            done_file.write_text(json.dumps(log, ensure_ascii=False, indent=2), "utf-8")
            time.sleep(random.uniform(3, 6))
        b.close()

    ok = sum(1 for v in log.values() if v.get("ok")); bad = [k for k, v in log.items() if not v.get("ok")]
    print(f"\n>>> 完成: 成功 {ok} 篇, 失败 {len(bad)} 篇。日志: download_log.json")
    for k in bad[:20]: print("   失败:", log[k].get("title"), log[k].get("reason"), k)

if __name__ == "__main__":
    main()
