---
name: wechat-mp-backup
description: Export and back up every article from the user's own WeChat Official Account (微信公众号) as Markdown + images + raw HTML + metadata, with a single QR-code login and resumable downloads. Use when the user wants to export, back up, migrate or download the full article history of a WeChat Official Account they administer (公众号文章导出/备份/迁移/历史文章下载).
license: Complete terms in LICENSE.txt
---

# 微信公众号历史文章备份

脚本位于本 skill 的 `scripts/` 目录：`step1_list_articles.py`、`step2_download_articles.py`、`step3_wayback.py`、`make_index.py`
（找不到时可 `git clone https://github.com/pixel-ju/wechat-mp-backup` 从仓库根目录取）。
项目主页与完整说明：https://github.com/pixel-ju/wechat-mp-backup

## 何时使用
用户是公众号管理员，想把自己账号里的历史文章（含图片）全部导出到本地或迁移到其他平台。
**只用于用户自己有管理权限的账号**；如果用户想抓别人的公众号，说明本工具不适用。

## 前置条件
- Python 3.9+：`pip install playwright requests beautifulsoup4 markdownify`
- 本机安装 Google Chrome（Playwright 自带 Chromium 在微信文章页会崩溃/被拦，纯 `curl` 只能拿到"环境异常"验证页）
- 用户能用管理员微信扫码

## 步骤
1. 在用户指定的工作目录（没有就新建 `wechat_export/`）里，把本 skill `scripts/` 下的 4 个 `.py` 脚本复制过去。
2. 后台运行 `nohup python3 -u step1_list_articles.py > step1.log 2>&1 &`（`-u` 必须，否则日志不刷新），告诉用户浏览器已弹出、请扫码。脚本检测到 URL 里的 `token=` 即登录成功，并**立刻**把 cookie 存到 `mp_login_state.json`；之后所有步骤自动复用，**不要再让用户扫码**。
3. 等 `step1.log` 出现 `>>> 完成`，读取 `articles.json`：按年份统计篇数、`is_deleted` 数量；日志里的"空 publish_info, 跳过"是纯文字/图片群发（非图文），属正常。
4. `python3 step2_download_articles.py --limit 3` 试跑，检查 `output/` 里的 `article.md` 与 `images/`；没问题后后台全量运行 `nohup python3 -u step2_download_articles.py > step2.log 2>&1 &`，用 `until grep -qE ">>> 完成|Traceback" step2.log; do sleep 15; done` 等待（约 10 秒/篇）。
5. `python3 make_index.py` 生成 `INDEX.md`。向用户汇报：成功篇数、图片总数、体积、失败原因分布，并说明失败类型均为微信侧不可恢复：
   - `已删除(后台标记 is_deleted)`：作者自己删过，公开页显示"该内容已被发布者删除"，后台 `get_appmsg` 也返回 not found；
   - `此内容发送失败无法查看` / `该内容暂时无法查看`：当年群发被拒或被平台屏蔽。
6. 可选：`python3 step3_wayback.py` 去 Wayback Machine 找失败文章的存档（archive.org 限流很严，命中率也不高，如实告知用户）。

## 输出结构
`output/YYYY-MM-DD_标题/`：`article.md`（front-matter + 本地图片路径）、`article.html`、`page_raw.html`（原页备份）、`images/`、`meta.json`；另有 `articles.json/csv`、`download_log.json`、`INDEX.md`。

## 坑
- 老账号"发表记录"里会有 `publish_info` 为空的条目，必须跳过而不是崩溃（脚本已处理）。
- 素材库（`appmsg?action=list_ex`）通常是已发表文章的子集，不用指望从中找回已删文章。
- 每篇之间随机等待 3–6 秒；触发验证页时脚本会等 90 秒重试，不要把间隔调短。
- 用户如果说"从 2012 年就开始发"，但清单最早只到某年，请如实告知后台记录起点，可能是另一个账号或早期已清理。
- `mp_login_state.json` 含登录 cookie，绝不能提交到 git 或发给他人。
