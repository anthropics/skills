#!/usr/bin/env python3
"""
步骤一：列出公众号后台的全部历史文章（发表记录）。
用法:  python3 step1_list_articles.py
  1. 会弹出浏览器窗口打开 mp.weixin.qq.com，请用管理员微信扫码登录。
  2. 登录成功后脚本自动翻页拉取全部文章清单，保存到 articles.json / articles.csv。
"""
import csv, json, re, sys, time
from pathlib import Path
from playwright.sync_api import sync_playwright

OUT_DIR = Path(__file__).parent
STATE_FILE = OUT_DIR / "mp_login_state.json"   # 保存 cookie，下次不用重复扫码
PAGE_SIZE = 10
SLEEP = 2.5   # 每页之间的间隔，别太快

def wait_login(page):
    print(">>> 请在弹出的浏览器里扫码登录公众号后台 ...")
    page.goto("https://mp.weixin.qq.com/")
    last = ""
    for i in range(1800):  # 最多等 30 分钟
        for pg in page.context.pages:
            m = re.search(r"token=(\d+)", pg.url)
            if m:
                print(">>> 登录成功, token =", m.group(1), "  url:", pg.url[:80])
                return m.group(1)
        # 兜底：已登录但 URL 里没 token 时，请求首页从正文里找 token
        if i % 5 == 0:
            try:
                body = page.evaluate("async () => { const r = await fetch('https://mp.weixin.qq.com/cgi-bin/home?t=home/index&lang=zh_CN', {credentials:'include'}); return (await r.text()).slice(0, 200000); }")
                m = re.search(r'token["\'=:\s]+(\d{6,})', body)
                if m and "登录" not in body[:3000]:
                    print(">>> 登录成功(从首页解析), token =", m.group(1))
                    return m.group(1)
            except Exception:
                pass
        if page.url != last:
            print("    当前页面:", page.url[:100]); last = page.url
        time.sleep(1)
    sys.exit("登录超时")

def api(page, url):
    """在页面上下文里发请求，自动带 cookie"""
    return page.evaluate("""async (u) => {
        const r = await fetch(u, {credentials: 'include'});
        return await r.json();
    }""", url)

def fetch_publish_list(page, token):
    """接口一：发表记录 appmsgpublish（包含群发+发布的所有文章）"""
    items, begin, total = [], 0, None
    while True:
        url = ("https://mp.weixin.qq.com/cgi-bin/appmsgpublish?sub=list&search_field=null"
               f"&begin={begin}&count={PAGE_SIZE}&query=&fakeid=&type=101_1&free_publish_type=1"
               f"&sub_action=list_ex&token={token}&lang=zh_CN&f=json&ajax=1")
        data = api(page, url)
        if data.get("base_resp", {}).get("ret") != 0:
            print("!!! 接口返回异常:", data.get("base_resp"))
            if data.get("base_resp", {}).get("ret") == 200013:
                print("    被限频了，休息 60 秒后重试 ..."); time.sleep(60); continue
            break
        pp = json.loads(data["publish_page"])
        if total is None:
            total = pp.get("total_count", 0)
            print(f">>> 发表记录总数(条群发/发布): {total}")
        plist = pp.get("publish_list", [])
        if not plist:
            break
        (OUT_DIR / "raw_pages").mkdir(exist_ok=True)
        (OUT_DIR / "raw_pages" / f"publish_{begin:04d}.json").write_text(json.dumps(pp, ensure_ascii=False), "utf-8")
        for p in plist:
            try:
                info = json.loads(p["publish_info"]) if p.get("publish_info") else {}
            except Exception as e:
                print("    !! publish_info 解析失败, 跳过:", str(p)[:200]); continue
            if not info:
                print("    !! 空 publish_info, 跳过 (publish_type=%s)" % p.get("publish_type")); continue
            sent = info.get("sent_info", {})
            for a in info.get("appmsgex", []):
                items.append({
                    "title": a.get("title"),
                    "link": a.get("link"),
                    "digest": a.get("digest"),
                    "author": a.get("author_name"),
                    "cover": a.get("cover"),
                    "create_time": a.get("create_time"),
                    "date": time.strftime("%Y-%m-%d", time.localtime(a.get("create_time", 0))),
                    "aid": a.get("aid"),
                    "is_deleted": a.get("is_deleted", False),
                    "publish_type": p.get("publish_type"),
                    "sent_time": sent.get("time"),
                })
        begin += PAGE_SIZE
        print(f"    已获取 {len(items)} 篇文章 (begin={begin}/{total})")
        (OUT_DIR / "articles_partial.json").write_text(json.dumps(items, ensure_ascii=False, indent=2), "utf-8")
        if begin >= total:
            break
        time.sleep(SLEEP)
    return items

def fetch_appmsg_list(page, token):
    """接口二(兜底)：素材/图文消息列表 appmsg list_ex"""
    items, begin, total = [], 0, None
    while True:
        url = ("https://mp.weixin.qq.com/cgi-bin/appmsg?action=list_ex"
               f"&begin={begin}&count={PAGE_SIZE}&fakeid=&type=9&query=&token={token}&lang=zh_CN&f=json&ajax=1")
        data = api(page, url)
        if data.get("base_resp", {}).get("ret") != 0:
            print("!!! 接口二返回异常:", data.get("base_resp")); break
        if total is None:
            total = data.get("app_msg_cnt", 0)
            print(f">>> 接口二 图文总数: {total}")
        lst = data.get("app_msg_list", [])
        if not lst: break
        for a in lst:
            items.append({
                "title": a.get("title"), "link": a.get("link"), "digest": a.get("digest"),
                "author": a.get("author_name"), "cover": a.get("cover"),
                "create_time": a.get("create_time"),
                "date": time.strftime("%Y-%m-%d", time.localtime(a.get("create_time", 0))),
                "aid": a.get("aid"), "is_deleted": a.get("is_deleted", False),
                "publish_type": "appmsg", "sent_time": a.get("update_time"),
            })
        begin += PAGE_SIZE
        print(f"    已获取 {len(items)} 篇 (begin={begin}/{total})")
        if begin >= total: break
        time.sleep(SLEEP)
    return items

def launch_browser(p, headless):
    """优先用系统 Chrome（微信页面在 Playwright 自带 Chromium 上会崩溃/被拦），没有再退回自带 Chromium"""
    for ch in ("chrome", "msedge", None):
        try:
            return p.chromium.launch(headless=headless, channel=ch) if ch else p.chromium.launch(headless=headless)
        except Exception:
            continue
    raise SystemExit("找不到可用浏览器，请安装 Google Chrome 或运行: playwright install chromium")

def main():
    with sync_playwright() as p:
        browser = launch_browser(p, headless=False)
        ctx = browser.new_context(storage_state=str(STATE_FILE) if STATE_FILE.exists() else None)
        page = ctx.new_page()
        token = wait_login(page)
        ctx.storage_state(path=str(STATE_FILE))

        items = fetch_publish_list(page, token)
        if not items:
            print(">>> 接口一没拿到数据，改用接口二 ...")
            items = fetch_appmsg_list(page, token)

        # 去重（同一 link 可能在群发和发布里各出现一次）
        seen, uniq = set(), []
        for it in items:
            key = it["link"] or (it["title"], it["create_time"])
            if key in seen: continue
            seen.add(key); uniq.append(it)
        uniq.sort(key=lambda x: x["create_time"] or 0)

        (OUT_DIR / "articles.json").write_text(json.dumps(uniq, ensure_ascii=False, indent=2), "utf-8")
        with open(OUT_DIR / "articles.csv", "w", newline="", encoding="utf-8-sig") as f:
            w = csv.DictWriter(f, fieldnames=list(uniq[0].keys()) if uniq else ["title"])
            w.writeheader(); w.writerows(uniq)
        print(f"\n>>> 完成：共 {len(uniq)} 篇文章，已保存到 articles.json / articles.csv")
        if uniq:
            print("    最早:", uniq[0]["date"], uniq[0]["title"])
            print("    最晚:", uniq[-1]["date"], uniq[-1]["title"])
        browser.close()

if __name__ == "__main__":
    main()
