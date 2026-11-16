# browser-farm 浏览器农场

> 技能包摘录说明：这是 browser-farm 项目的自述文档。技能包不带 LICENSE 与 start-farm.bat——许可全文见 SKILL.md「许可与免责」节；启动用 `node farm.js slots`，Windows 双击入口可按 SKILL.md 两行自建。

给 AI agent 用的多账号浏览器舰队：**一个账号档 = 一个 Chrome 实例 = 一个固定调试端口 = 一个独立数据目录**。

- **登录一次永久保持**：每档独立 user-data-dir，互不串号；真人扫码/验证码登录后，agent 后续全程免登
- **总管常驻**：一个 Node 进程管全部档位的生死、快照、脚本任务；agent 只需要一条命令
- **三种跑法**：有窗口（登录/人工介入）、无窗口（省内存干活）、**效率模式**（拦广告/埋点域名+禁远端字体+禁自动播，批量挂机最省）
- **零依赖**：纯 Node（≥18，用内置 WebSocket）+ 本机已装的 Chrome/Edge，不装任何 npm 包
- **脚本器**：真人点一遍录制成脚本，后台无限循环或盯表格数值触发；脚本绑账号档，agent 一条命令直跑
- **快照/回滚**：档位 = 轻量虚拟机，危险操作前拍快照，出事一键回滚
- **抓包+重放**：录制时自动抓 XHR/Fetch，带登录态脱离浏览器重放——判断哪个活能转纯接口

## 快速开始

```bash
node farm.js add "平台-账号名"    # 登记档位（自动分配端口）
node farm.js login 01            # 弹真 Chrome 窗口，人扫码/输验证码，登完关掉
node farm.js start 01            # 切回无窗口干活模式
node farm.js open 01 "https://后台地址"
node farm.js eval 01 "document.title"
```

任何 `farm.js` 命令都会自动拉起常驻总管（supervisor.js，HTTP 口 9300）。普通用户双击 `start-farm.bat` 打开网页控制台（看档位、启动/停止/效率跑、当前页截图、录制、脚本管理）。

## 效率模式（v0.1.21 起）

```bash
node farm.js start 01 --eff      # 或 GUI 点「效率跑」
```

无窗口之上的再省一档：广告/埋点域名用 Chrome 原生 `--host-resolver-rules` 在 **DNS 层**拦死（映到 127.0.0.2，请求出不了机器、秒失败、浏览器级生效），加上禁远端字体、禁视频自动播、磁盘缓存砍到 8MB、关 DoH 防绕过。

清单在工作区根 `blocklist.txt`（一行一个域名，子域自动跟拦）。默认只放国际广告/埋点域名；目标网站自己的域别往里放。改完重启档生效。

看护、eval 自动拉回、快照恢复都会记住档位最后一次的跑法——效率档被自动拉回还是效率档，拦截不丢。

## 核心命令

| 命令 | 作用 |
|---|---|
| `slots` / `add "备注"` | 全部档位+死活 / 登记新档位 |
| `start <id> [--eff]` / `login <id>` | 无窗口启动（--eff=效率模式）/ 有窗口启动（登录用） |
| `open <id> <url>` / `eval <id> "代码"` | 开页返回 targetId / 页面里执行 JS 拿返回值 |
| `structured <id>` | 当前页结构化数据一把抓（og / json-ld / meta / canonical） |
| `status <id>` / `shot` | 档位详情+页面列表 / 当前页截图（HTTP `GET /slot/01/shot`） |
| `snap <id> <名>` / `restore <id> <名>` | 快照 / 回滚（自动停机拷目录） |
| `sniff <id> start\|stop` | 抓包：录页面背后的 XHR/Fetch 接口清单 |
| `replay <id> <url>` | 带档位登录态脱离浏览器重放（判断能否转纯接口） |
| `record <id> [--agent]` | 录制点击路径（窗口右下角常驻条，滤假点击，自动带抓包）；`--agent`=不存脚本，存 `agent-notes/` 一份 agent 直接读的 md 笔记 |
| `forge <id[,id..]> <forge脚本名> [参数..]` | **forge(record-to-skill) 挂档位口跑**：免登录录制/探查/纯接口（口和 `--keep-open` 桥焊死不杀档；record 自动切有窗；多档=多账号） |
| `forge-rec <脚本id 或 笔记.md>` | 农场录制产物转 forge 的 rec.json，喂它的 evidence→probe→build 管线 |
| `newscript` / `runscript` / `bind` | agent 写脚本 / 后台执行 / 脚本绑账号档 |
| `fixchrome` | 清占默认数据目录的无头 Chrome 残留（桌面 Chrome 点不开就跑它） |
| `export` / `import` | 配置搬家：档位登记+全部脚本（登录态不跟走，另登一次） |

HTTP API 与 CLI 同构（`GET /slots`、`POST /slot/01/start|stop|open|eval|structured|snapshot|restore|remove`、脚本/绑定/配置全套），agent 接入细节见 [AGENTS.md](AGENTS.md)。

## 为什么是真 Chrome，不是无头引擎

这个项目管的是「有真实登录态的账号级操作」：真指纹过风控、真渲染截图、扫码登录，这三样只有真浏览器给得了。资源问题用另一条路解决——无窗口+禁图+禁 GPU 打底，效率模式再在 DNS 层砍流量。公开网页的大规模采集（不需要登录态）不在本项目射程内，用轻量 headless 引擎更合适。

## 设计要点

1. **端口绑账号，不绑 tab**：同一 Chrome 里 tab 隔离不了 cookie，账号档才是隔离的最小单位；同档多开页不另起进程，很便宜。
2. **总管挂了档位不死**：Chrome 独立于总管进程（Windows detached 脱离 job），下次起总管自动接管。
3. **脚本杀不死**：脚本任务挂总管进程里；每步 90 秒重连窗穿过档位重启，录制页没开自动开回来；档整个死了看护 15 秒拉回接着跑。
4. **停机先礼后兵**：先 CDP `Browser.close` 让 profile 落盘，超时才连根杀。
5. **录制只记真人点击**（`isTrusted` 过滤网页代码自己触发的假点击），同时抓接口——存下的脚本自带「点了什么+背后发了什么请求」。
6. **每脚本跟自己的录制页**：同档多个脚本各在各的页面干活，互不抢焦点（会话隔离的最小实现）。

## 测试

```bash
node test-farm.js         # 离线全链：真 Chrome + 本地页面，42 条断言（含效率模式域名拦截 A/B、structured）
node test-scripter.js     # 脚本器：录制/循环/盯表/重启存活/看护/导入导出/绑定/存Agent笔记/forge转换，50 条断言
node test-idle-script.js  # 空闲停豁免：脚本运行中的档不被杀（约 4 分钟）
```

## 许可与免责

MIT 许可（版权与许可全文见 SKILL.md「许可与免责」节）。本项目全部为原创代码，未包含任何第三方代码；设计层面参考过 Lightpanda（AGPL-3.0 项目）的公开讨论，未复制其任何代码、资产或名义。

仅供自有账号的合法自动化与测试使用。使用者需遵守目标网站的服务条款及所在地法律，滥用（包括但不限于批量注册、爬取受限数据、绕过反作弊）产生的一切后果自负。
