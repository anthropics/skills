#!/usr/bin/env python3
"""
CrossRef API 批量文献元数据查询工具
用于 citation-audit skill 的 L1/L2 层验证

用法：
  1. 编辑底部 QUERIES 列表，填入参考文献的查询字符串
  2. 运行: python crossref_batch_check.py
  3. 结果输出到同目录下 crossref_result.txt

注意：
  - CrossRef 返回的"最佳匹配"可能不正确，需要人工 + Web 搜索二次验证
  - 数据集、书籍章节、非英语文献的匹配准确率较低
  - rate limit: 每次查询间隔 0.3 秒（polite crawling）
"""

import urllib.request
import urllib.parse
import json
import time
import os
import sys

# ============================================================
# 配置
# ============================================================
OUTPUT_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "crossref_result.txt")
RATE_LIMIT = 0.3  # 秒

# ============================================================
# 查询列表（修改此处）
# 格式: ("标识符", "查询字符串")
# 标识符用于在结果中标记条目，建议用参考文献编号
# ============================================================
QUERIES = [
    # 示例：
    # ("[1]",  "Aiello-Lammens 2015 spThin spatial thinning Ecography"),
    # ("[2]",  "Allouche 2006 assessing accuracy species distribution models TSS"),
    # ...在此添加全部参考文献查询...
]


def query_crossref(search_str):
    """查询 CrossRef API，返回最佳匹配的元数据字典"""
    url = "https://api.crossref.org/works?" + urllib.parse.urlencode({
        "query": search_str,
        "rows": 1,
        "select": "DOI,title,author,container-title,published-print,published-online,volume,page,issue"
    })
    req = urllib.request.Request(url, headers={
        "User-Agent": "CitationAuditBot/1.0 (mailto:your@email.com)"
    })
    with urllib.request.urlopen(req, timeout=30) as resp:
        data = json.loads(resp.read().decode("utf-8"))
    items = data.get("message", {}).get("items", [])
    if not items:
        return None
    return items[0]


def format_result(item):
    """将 CrossRef 返回的元数据格式化为可读字符串"""
    title = (item.get("title") or ["N/A"])[0]
    journal = (item.get("container-title") or ["N/A"])[0]
    doi = item.get("DOI", "N/A")
    vol = item.get("volume", "N/A")
    pages = item.get("page", "N/A")

    # 年份：优先取 published-print，否则取 published-online
    year = "N/A"
    for key in ("published-print", "published-online"):
        dp = item.get(key, {}).get("date-parts", [[]])
        if dp and dp[0]:
            year = str(dp[0][0])
            break

    # 作者列表
    authors = "N/A"
    if item.get("author"):
        names = []
        for a in item["author"]:
            given = a.get("given", "")
            family = a.get("family", "")
            names.append(f"{family}, {given}" if given else family)
        authors = "; ".join(names)

    return {
        "title": title,
        "journal": journal,
        "doi": doi,
        "volume": vol,
        "pages": pages,
        "year": year,
        "authors": authors
    }


def main():
    if not QUERIES:
        print("QUERIES 列表为空。请编辑脚本底部的 QUERIES 添加查询条目。")
        sys.exit(1)

    with open(OUTPUT_FILE, "w", encoding="utf-8") as f:
        f.write("=" * 70 + "\n")
        f.write("CrossRef 批量查询结果\n")
        f.write(f"查询时间: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
        f.write(f"总条目数: {len(QUERIES)}\n")
        f.write("=" * 70 + "\n\n")

        for i, (ref_id, search_str) in enumerate(QUERIES):
            try:
                item = query_crossref(search_str)
                if item is None:
                    f.write(f"[{ref_id}] 无结果\n\n")
                    continue

                r = format_result(item)
                f.write(f"[{ref_id}] Year={r['year']} Vol={r['volume']} Pages={r['pages']}\n")
                f.write(f"  Authors: {r['authors']}\n")
                f.write(f"  Title: {r['title']}\n")
                f.write(f"  Journal: {r['journal']}\n")
                f.write(f"  DOI: {r['doi']}\n")
                f.write("\n")

            except Exception as e:
                f.write(f"[{ref_id}] ERROR: {e}\n\n")

            time.sleep(RATE_LIMIT)

            # 进度提示
            if (i + 1) % 10 == 0:
                print(f"  进度: {i + 1}/{len(QUERIES)}")

    print(f"完成。结果已保存至 {OUTPUT_FILE}")


if __name__ == "__main__":
    main()
