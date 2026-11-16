# browser-farm 接入指引（给自动化 agent）

本机如果有这套"浏览器农场"在跑：每个账号一个常驻浏览器档，登录一次永久保持。你（agent）做任何网页自动化，**先读这份文档，按规矩用农场，不要自己另开浏览器**。

## 铁律

1. **不许自己起 Chrome/Playwright 全新实例去跑本机已有账号**——每次重新登录又慢又容易触发风控。统一走农场的档位。
2. **一个档 = 一个身份**。同一身份在不同网站的登录态在同一个档里共存（cookie 按网站分开存）；两个不同账号必须用两个档。
3. **一个档同一时刻只跑一个任务**。开工前 `GET /slots` 看档位状态，被占着就等或换档。
4. **危险操作（批量改、删、提交）前先快照**：`POST /slot/ID/snapshot {"name":"动作前"}`，出事可回滚。
5. 不要手动删 `slots/` 目录；不要占用 9222 端口（那是别的工具的）。

## 第一步：找到农场

```
GET http://127.0.0.1:9300/health
```

- 有回话 `{"ok":true}` → 农场活着，直接用。
- 连不上 → 找到农场目录（本仓库/本安装目录），在里面跑 `node farm.js slots`，任何命令都会自动拉起总管。

## 第二步：挑档位（账号↔档位对照）

```
GET /slots
```

返回 `slots: [{id, port, note, alive, mode, lastUsed, ...}]`。**note 就是账号名**，命名规范 `平台-账号`，如 `商城-主号`、`论坛-小号A`。

- 找到目标账号的档 → 看 `alive`，死了就 `POST /slot/ID/start {}`（秒起，登录态都在）。
- 没有这个账号的档 → 问用户"这个账号要常驻还是一次性用"，常驻再登记：
  ```
  POST /slots/add {"note":"平台-账号名"}
  ```
  然后走下面的登录流程。

## 登录流程（一个账号只做一次）

```
POST /slot/ID/start {"mode":"headful"}   ← 弹真窗口
```

窗口里人扫码/输验证码（提醒用户操作）。登完：

```
POST /slot/ID/stop
POST /slot/ID/start {}                   ← 切回无窗口干活模式
```

验证登录态：`POST /slot/ID/eval {"code":"return location.href"}` 开目标站看是否免登。

## 干活：开页 + 执行

```
POST /slot/ID/open  {"url":"https://..."}     → 返回 targetId
POST /slot/ID/eval  {"code":"...", "targetId":"..."}   → 返回页面里的值
```

eval 规则：
- 直接写语句，顶层 `return xxx` 可以用（自动包 IIFE），`await` 可以用，返回值必须是 JSON 能装的
- 例：抓表格 → `return [...document.querySelectorAll('tr')].map(tr=>tr.innerText)`
- 查页面信息（og/json-ld/meta）不用手写：`POST /slot/ID/structured` 一把抓
- 一次 eval 上限 2 分钟，长任务分步做

命令行等价（能跑 shell 时更顺手）：

```
node farm.js open 01 "https://..."
node farm.js eval 01 --target <tid> "return document.title"
node farm.js structured 01
node farm.js status 01
node farm.js snap 01 动作前
```

## 效率模式（挂机/盯表首选）

```
POST /slot/ID/start {"mode":"eff"}
命令行：node farm.js start 01 --eff
```

无窗口+拦广告/埋点域名（清单=目录根 `blocklist.txt`，改完重启档生效）。看护/eval 自动拉回会保持效率跑法不变。

## 空闲自动停（重要，别被吓到）

headless 档 **30 分钟**没有任何操作会自动停（省内存；登录态不丢，`start` 秒回）。所以：

- 任务间隔长：每 20 分钟左右发一次 `GET /slot/ID/status` 当心跳，或挂个脚本（**跑脚本的档自动豁免空闲停**）。
- 发现档停了别慌，`start` 再来，cookie 还在。
- 登录窗口（headful）永不自动停。阈值用环境变量 `FARM_IDLE_MIN` 调，0=关闭。

## 判断"这活能不能转纯后台"（sniff + replay，优先做）

接口比点页面快百倍，每个网站的第一次，先做一轮探测：

```
POST /slot/ID/open  {"url":"https://目标站"}
POST /slot/ID/sniff {"action":"start"}           ← 开始录接口
（在页面上把活干一遍：你自己 eval 点/填，或让用户操作）
POST /slot/ID/sniff {"action":"stop"}            ← 出接口清单（url/方法/状态/重复次数）
POST /slot/ID/replay {"url":"抓到的接口","method":"GET"}   ← 带档位登录态脱离浏览器重放
```

- **replay 返回 200 且有数据** → 这个接口能转纯后台：以后直接 HTTP 调（cookie 从档位拿）。注意 cookie 会过期，过期了回档位重新拿。
- **replay 401/403/被拦** → 老实留在农场点页面。
- 清单里**重复次数高**的接口多半是数据轮询接口，最值得转纯后台。

## 装了 forge(record-to-skill) 的机器：桥（1+1>2）

forge 的录制/探查/纯接口执行全走 `--port`，农场档位就是现成的调试口——挂上去它就**免登录**（真人只在农场档扫一次码），cookie 过期回档重登就行：

```
node farm.js forge 01 record --url https://目标站 --name 链路名 --forge-dir <forge目录>
node farm.js forge 01,02,04 api_run --config xx --go     # 多档顺序跑=多账号
node farm.js forge-rec 07                                  # 农场脚本07 → forge rec.json
```

桥焊死两条：档口按档位分配（别传 `--port`）、`--keep-open` 强制（forge 默认收尾按端口关浏览器，会把农场档杀了）。rec.json 交给 forge 的 `evidence.mjs`（打分挑数据源）→ `probe.mjs`（挂档口免登录复现接口）→ `build_skill.mjs`（出可安装子包）——农场出料、forge 出判定，两边谁也不用改谁。

## 挂机脚本（重复活交给脚本盯，不占你）

两类：**路径循环**（录一串点击按随机间隔反复跑）和**数据触发**（盯表格某格达标点该行按钮）。

录制收工时窗口条上除了「存」（存脚本）还有蓝色**「存Agent」**：不建脚本，落农场目录 `agent-notes/` 一份 md 笔记（步骤表+录制期间抓到的接口+原始 JSON）。用户说"录给你看"时用这个——你读文件就能复现流程、判断哪步转纯接口，想挂机再照原始 JSON 转脚本。

```
GET  /scripts                          ← 全部脚本+各自运行状态
POST /script/ID/start {"slot":"01"}    ← 挂到档位起跑（可加 "loop":3、"once":true）
POST /script/ID/stop {}
GET  /script/ID/status
```

agent 直接写脚本：步骤 json 交 `POST /script/new`（校验、自动编号、跟人录的同待遇），格式示例：

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

每步 `selector` 或 `text` 必有其一；`href` = 页面没开就自动开回（强烈建议带上）。写之前先 `open` 到目标页、`eval` 里 `document.querySelectorAll` 看清选择器再落笔，别猜。

脚本绑账号档：`POST /script/07/bind {"slot":"01","desc":"干什么用的"}`，绑了启动不用选档；配置搬家（export/import）时绑定自动跟走，档位号对不上的宁可摘绑不会绑错。

## 你的引擎非要直连 CDP？

档位就是标准 Chrome 调试口：`http://127.0.0.1:<port>`（port 从 `/slots` 拿）。Playwright/Puppeteer 用 connectOverCDP 直连即可。但直连不经过总管，**不产生活动记录，空闲停可能杀到你头上**——直连期间保持心跳，或让用户调大 `FARM_IDLE_MIN`。

## 出问题查哪

- **桌面 Chrome 点不开/弹不出窗**：有无头残留 Chrome 占了默认数据目录的单人锁。`node farm.js fixchrome` 一条命令清掉；总管每 5 分钟也自动扫（门卫只清「无头+占默认目录」的，农场档位和正经自动化不碰）。
- `farm.log` —— 所有启停、自动停、报错都在里面
- `GET /slot/ID` —— 档位详情+当前打开的页面
- 总管死了不影响已开档位，重启总管自动接管
