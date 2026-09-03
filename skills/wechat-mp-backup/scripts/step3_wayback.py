#!/usr/bin/env python3
"""
步骤三（可选）：对微信侧已删除/无法查看的文章，去 Wayback Machine (web.archive.org) 找存档。
用法: python3 step3_wayback.py        # 读取 download_log.json 中失败的文章，逐个查询，有存档就下载到 output_wayback/
注意: archive.org 限流很严，每次查询间隔 6 秒；被 429 时会自动等待 2 分钟再试。
"""
import json, re, time, urllib.parse
from pathlib import Path
import requests
from bs4 import BeautifulSoup
from markdownify import markdownify as md

BASE = Path(__file__).parent
OUT = BASE / "output_wayback"; OUT.mkdir(exist_ok=True)
log = json.loads((BASE / "download_log.json").read_text("utf-8"))
targets = [(u, v) for u, v in log.items() if not v.get("ok")]
print(f"待查询 {len(targets)} 篇")
res_file = BASE / "wayback_log.json"
res = json.loads(res_file.read_text("utf-8")) if res_file.exists() else {}
S = requests.Session(); S.headers["User-Agent"] = "Mozilla/5.0"

def get(url, **kw):
    for _ in range(5):
        r = S.get(url, timeout=60, **kw)
        if r.status_code == 429:
            print("   429 限流，等 120 秒 ..."); time.sleep(120); continue
        return r
    return r

for i, (url, v) in enumerate(targets, 1):
    if url in res: continue
    print(f"[{i}/{len(targets)}] {v.get('title')}")
    r = get("https://archive.org/wayback/available?url=" + urllib.parse.quote(url, safe=""))
    try:
        snap = r.json().get("archived_snapshots", {}).get("closest")
    except Exception:
        snap = None
    if not snap:
        res[url] = {"found": False, "title": v.get("title")}; print("   无存档")
    else:
        snap_url = snap["url"]
        page = get(snap_url)
        soup = BeautifulSoup(page.text, "html.parser")
        content = soup.select_one("#js_content")
        if content is None or "该内容已被发布者删除" in page.text:
            res[url] = {"found": True, "usable": False, "snapshot": snap_url, "title": v.get("title")}
            print("   有存档但无正文:", snap_url)
        else:
            title = (soup.select_one("#activity-name") or soup.title).get_text(strip=True)
            d = OUT / re.sub(r'[\\/:*?"<>|]+', "_", f"{snap['timestamp'][:8]}_{title}")[:70]; d.mkdir(exist_ok=True)
            (d / "page_raw.html").write_text(page.text, "utf-8")
            (d / "article.md").write_text(f"# {title}\n\n来源: {url}\n存档: {snap_url}\n\n" + md(str(content), heading_style="ATX"), "utf-8")
            res[url] = {"found": True, "usable": True, "snapshot": snap_url, "dir": d.name, "title": title}
            print("   ✓ 找回:", d.name)
    res_file.write_text(json.dumps(res, ensure_ascii=False, indent=2), "utf-8")
    time.sleep(6)
print("完成，结果见 wayback_log.json")
