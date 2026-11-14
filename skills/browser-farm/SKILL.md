---
name: browser-farm
display_name: AI替你干网页活·登录一次就够
display_name_en: Browser Farm
description: 一账号一个常驻 Chrome 档，真人登录一次 agent 永久免登：批量开页、挂机盯表、快照回滚、抓包重放、效率模式省资源。触发词：浏览器农场、多账号登录、登录保持、账号挂机、盯表触发、抓包重放、效率模式、structured
description_zh: 给 agent 用的多账号浏览器舰队。每账号独立 Chrome 档位+固定调试端口，真人扫码登录一次，之后 agent 全程免登：无窗口干活、效率模式（DNS 层拦广告域名）、危险操作前快照回滚、录制点击循环挂机、盯表格数值触发、接口抓包+带登录态重放。
description_en: "A multi-account browser fleet for agents. Each account gets its own resident Chrome slot with a fixed debug port — a human logs in once, then the agent works login-free forever: headless work, efficiency mode (DNS-level ad blocking), snapshot/rollback, recorded click loops, table-watch triggers, and XHR capture with login-state replay."
version: 0.1.23
author: browser-farm contributors
examples_zh:
- 帮我把这 3 个账号的后台数据每天巡检一遍
- 盯着投放后台的表格，消耗到 500 就点暂停
- 这些账号挂机用效率模式跑，别吃太多内存
- 抓一下当前页面的结构化信息（og/json-ld）
examples_en:
- Run a daily dashboard check across my 3 accounts
- Watch the ad platform table and click pause at 500 spend
- Keep these accounts idling in efficiency mode
- Extract structured data (og/json-ld) from the current page
---

# 浏览器农场：多账号常驻浏览器

**一个账号 = 一个常驻 Chrome 档 = 一个固定调试端口 = 一个独立数据目录。**真人登录一次，登录态永久保持，你（agent）后续全程免登。

- 适用：多账号网页操作、登录态保持、批量巡检、挂机盯表、账号级截图采集
- 不适用：无登录态的大规模公开网页采集——那活用轻量 headless 引擎更合适，别硬上农场

## 铁律（先读）

1. **不许为跑本机已有账号另起全新 Chrome/Playwright 实例**——重新登录又慢又容易触发风控，统一走农场档位
2. **一个档 = 一个身份**；两个账号必须用两个档
3. **一个档同一时刻只跑一个任务**，开工前 `GET /slots` 查状态，被占就等或换档
4. **危险操作（批量改/删/提交）前先快照**，出事一键回滚
5. 不要删 `slots/` 目录；不要占用 9222 端口

## 首次安装（每台机器一次）

农场是常驻服务，运行时会写数据（登录态/脚本/快照/日志），**不要在技能目录里跑**：

1. 把本技能 `scripts/` 里的全部文件拷到一个专用目录（问用户放哪，没意见就用 `~/browser-farm/`）
2. 在那个目录跑 `node farm.js slots`——总管（supervisor）自动拉起，HTTP 口 9300
3. `curl http://127.0.0.1:9300/health` 回 `{"ok":true}` 就是装好了
4. 想验证安装质量：`node test-farm.js` 应 42/42 全过（离线跑真 Chrome，几分钟）
5. 给账号建档登录（一个账号只做一次）：`node farm.js add "平台-账号名"` → `node farm.js login 01` 弹真窗口，人扫码/输验证码 → 登完 `node farm.js start 01` 切回无窗口

前提：Node ≥18 + 本机已装 Chrome/Edge，零 npm 依赖。Windows 用户双击运行可自建一个 `start-farm.bat`（内容两行：`node farm.js slots` + `start "" http://127.0.0.1:9300/gui`）。

人工入口（告诉用户）：浏览器开 `http://127.0.0.1:9300/gui`——网页控制台看档位、启停、截图、录脚本。

## 日常干活

先 `GET http://127.0.0.1:9300/slots` 找目标账号的档（`note` 就是账号名，`alive` 看死活，死了 `POST /slot/ID/start {}` 秒回、登录态都在）。然后：

| 动作 | HTTP | CLI 等价 |
|---|---|---|
| 开页（返回 targetId） | `POST /slot/ID/open {"url":"..."}` | `node farm.js open 01 "https://..."` |
| 页面里执行 JS | `POST /slot/ID/eval {"code":"...","targetId":"..."}` | `node farm.js eval 01 "return document.title"` |
| 结构化一把抓 | `POST /slot/ID/structured` | `node farm.js structured 01` |
| 档位详情+页面列表 | `GET /slot/ID` | `node farm.js status 01` |
| 当前页截图 | `GET /slot/ID/shot`（真 JPEG） | `node farm.js shot 01` |
| 快照 / 回滚 | `POST /slot/ID/snapshot {"name":"动作前"}` / `{"name":...}` 路由 restore | `node farm.js snap 01 名` / `restore 01 名` |

eval 规则：顶层 `return xxx` 可用（自动包 IIFE），`await` 可用，返回值必须 JSON 能装；一次上限 2 分钟，长任务分步。structured 直接拿 og / json-ld / twitter / meta / canonical，不用手写。

## 效率模式（挂机/盯表首选）

```
POST /slot/ID/start {"mode":"eff"}      # CLI: node farm.js start 01 --eff
```

无窗口之上再省一档：广告/埋点域名在 **DNS 层**拦死（映 127.0.0.2，请求出不了机器）+ 禁远端字体 + 禁视频自动播 + 磁盘缓存 8MB + 关 DoH。清单在安装目录 `blocklist.txt`（一行一个域，子域自动跟拦；默认只有国际广告/埋点域，目标网站自己的域别放；改完重启档生效）。看护/eval 自动拉回都会保持效率跑法。

## 空闲自动停（别被吓到）

无窗口档 30 分钟没操作会自动停（省内存；登录态不丢，`start` 秒回）。任务间隔长就每 20 分钟发一次 `GET /slot/ID` 当心跳，或挂脚本（**跑脚本的档自动豁免**）。登录窗口（headful）永不自动停。阈值环境变量 `FARM_IDLE_MIN` 调，0=关闭。

## 判断这活能不能转纯接口（sniff + replay，优先做）

```
POST /slot/ID/open   {"url":"https://目标站"}
POST /slot/ID/sniff  {"action":"start"}
（把活干一遍：自己 eval 点/填，或让用户操作）
POST /slot/ID/sniff  {"action":"stop"}     ← 出接口清单（url/方法/状态/重复次数）
POST /slot/ID/replay {"url":"抓到的接口","method":"GET"}   ← 带登录态脱离浏览器重放
```

replay 回 200 且有数据 → 这个接口能转纯后台直调（cookie 从档位拿，会过期）。401/403/被拦 → 老实留在农场点页面。重复次数高的接口多半是数据轮询，最值得转。

## 装了 forge(record-to-skill) 的机器：桥（1+1>2）

forge 的录制/探查/纯接口执行全走 `--port`，农场档位就是现成的调试口——挂上去就**免登录**（真人只在农场档扫一次码，cookie 过期回档重登）：

```
node farm.js forge 01 record --url https://目标站 --name 链路名 --forge-dir <forge目录>
node farm.js forge 01,02,04 api_run --config xx --go   # 多档顺序跑=多账号
node farm.js forge-rec 07                               # 农场脚本07 → forge rec.json
```

档口和 `--keep-open` 桥焊死（forge 收尾不杀档）；rec.json 进 forge 的 evidence（打分）→probe（挂档口复现接口）→build（出子包）管线，农场出料、forge 出判定。

## 挂机脚本（重复活不占你）

两类：路径循环（录一串点击反复跑）和盯表触发（表格某格达标点该行按钮）。人可以在 GUI 里录；录制收工窗口条上除了「存」还有蓝色「存Agent」——不建脚本，落安装目录 `agent-notes/` 一份 md 笔记（步骤表+接口+原始 JSON），用户说"录给你看"时你就读它。你直接写 JSON 交 `POST /script/new`（校验+自动编号，跟人录的同待遇）：

```json
{
  "name": "点名下载",
  "loop": 0,
  "delayMs": 1200,
  "jitterMs": 800,
  "steps": [
    { "selector": "#download-btn", "text": "下载安装包", "href": "https://目标站/页面" }
  ]
}
```

每步 `selector` 或 `text` 必有其一；`href` = 页面没开自动开回（强烈建议带）。写之前先 open + eval 用 `querySelectorAll` 看清选择器再落笔，别猜。绑账号档：`POST /script/ID/bind {"slot":"01","desc":"用途"}`，绑了启动不用选档。脚本挂总管进程里：每步 90 秒重连窗穿过档位重启，档整个死了看护 15 秒拉回接着跑。

## 出问题查哪

- **桌面 Chrome 点不开**：无头残留占了默认数据目录的单人锁，`node farm.js fixchrome` 一条命令清掉（总管每 5 分钟也自动扫）
- `farm.log`——所有启停、自动停、报错
- 总管挂了不影响已开档位，重启总管自动接管
- 你的引擎要直连 CDP 也行：档位就是标准 Chrome 调试口（port 从 `/slots` 拿），Playwright/Puppeteer `connectOverCDP` 直连；但直连不产活动记录，空闲停可能杀到你——保持心跳或调大 `FARM_IDLE_MIN`

## 深入阅读

- 完整 agent 接入指引（含登录流程细账、绑定/导入导出规矩）：@references/AGENTS.md
- 项目说明与设计要点（为什么是真 Chrome 不是无头引擎）：@references/README.md
- 版本记录：@references/CHANGELOG.md

## 许可与免责

本技能全部为原创代码，MIT 许可（版权 2026 browser-farm contributors）：任何人可自由使用、修改、再发布，需保留版权与许可声明，软件按「现状」提供不担担保。设计层面参考过 Lightpanda（AGPL-3.0 项目）的公开讨论，未复制其任何代码、资产或名义。

仅供自有账号的合法自动化与测试使用。使用者需遵守目标网站的服务条款及所在地法律；滥用（批量注册、爬取受限数据、绕过反作弊等）产生的一切后果自负。
