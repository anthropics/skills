#!/usr/bin/env python3
"""生成 INDEX.md：全部文章清单 + 下载状态。用法: python3 make_index.py"""
import json
from pathlib import Path
BASE = Path(__file__).parent
a = json.loads((BASE / "articles.json").read_text("utf-8"))
log = json.loads((BASE / "download_log.json").read_text("utf-8")) if (BASE / "download_log.json").exists() else {}
ok = sum(1 for v in log.values() if v.get("ok"))
lines = ["# 公众号文章总索引\n", f"共 {len(a)} 篇文章记录；已下载 {ok} 篇。\n",
         "| 日期 | 标题 | 状态 | 本地目录 / 原链接 |", "|---|---|---|---|"]
for x in a:
    v = log.get(x["link"], {})
    if v.get("ok"):
        st, loc = "✅ 已下载", f"[{v['dir']}](output/{v['dir']}/article.md)"
    else:
        st, loc = "❌ " + v.get("reason", "未处理"), x["link"]
    lines.append(f"| {x['date']} | {x['title'].replace('|', '｜')} | {st} | {loc} |")
(BASE / "INDEX.md").write_text("\n".join(lines) + "\n", "utf-8")
print(f"INDEX.md 已生成：{len(a)} 篇，已下载 {ok} 篇")
