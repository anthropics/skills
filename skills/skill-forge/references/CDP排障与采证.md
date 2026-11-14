# CDP 录制/采证排障实录（2026-11-04）

> 背景：skill-forge 交付时报「已实测」，但真机一跑「录出来永远 0 条」。以下 5 个 bug 是按症状逐个逼出来的。
> 用途：以后任何「CDP 注入式录制器录不到东西 / 跳页后断了 / 跟着空白页跑」都先照这张表排。

## 症状 → 根因 → 修法

| # | 症状 | 根因 | 修法 |
|---|---|---|---|
| 1 | 页面正常操作，录制文件 `actions: 0` | `record.mjs` 轮询里写了 `if (!window.__SOP.recording)`，但 recorder 的状态位叫 `S.on`。字段永远 undefined → 每 0.5 秒 `__SOP_start()` 一次，动作刚 push 就被清空 | 判断改成 `window.__SOP.on` |
| 2 | 换页后 `window.__SOP` 一直是 false，怎么点都不录 | `injectFile()` 走 `evalJs()`，evalJs 会给表达式再包一层 IIFE；recorder.js 开头是 `/* 注释 */`、结尾是 `})();`，包完变语法错误，异常被 `.catch(()=>{})` 吞掉 | injectFile 直接 `Runtime.evaluate` 原文，并把 `exceptionDetails` 抛出来 |
| 3 | 关掉一个标签后，录制进程还活着但再也不录 | `Cdp.send()` 的 Promise 没超时，`ws.onclose` 也没 reject 所有 pending；页面一跳 ws 断，`await` 永远挂住，轮询循环卡死在第一步 | send 加 15 秒超时；`ws.onclose` 遍历 pending 全部 reject |
| 4 | 日志「↪ 跟随新标签：about:blank」，录制跑在空白页上，`network` 全 0 | `followNewTab()` 把「新出现的任意 page」当目标，残留的 about:blank 被当成用户新开的页 | 只跟 `/^https?:\/\//` 的页；启动时先把已存在的 page 全塞进 knownTargets，避免拿历史残留当新页 |
| 5 | 跳页前 1.5 秒内的动作丢了 | 轮询间隔 1500ms，页面卸载即失忆 | 间隔降到 500ms（CPU 开销可忽略）。仍会丢最后 0.5 秒，属已知边界 |

## 验证方法（改完必须这样验，别只看代码）

1. **注入自证**：`Runtime.evaluate` 读 `JSON.stringify({url:location.href, has:!!window.__SOP, on:window.__SOP.on})` → 必须 `has:true, on:true`。
2. **跨页自证**：同 tab `Page.navigate` 到另一个站 → 等 4 秒 → 再读一次，仍要 `has:true`（证明重注入生效）。
3. **新 tab 自证**：`PUT /json/new?<url>` 开新页 → 录制日志必须出现 `↪ 跟随新标签：<url>`。
4. **点击落盘**：用 `Input.dispatchMouseEvent`（mousePressed + mouseReleased）发**真实**鼠标事件，别用 `el.click()` 合成事件（合成事件 `isTrusted=false`，跟真实用户路径不完全等价）。
5. **端到端**：`--minutes 1` 让进程自然收尾（`process kill` 不发 SIGINT，不会落 rec.json），再核对 rec.json 的 `meta.counts` 与页面实际动作数。

## 采证（evidence）踩过的坑

- `Network.getResponseBody` 有生命周期：页面跳走后旧 requestId 取不到 body，只能拿到 `status/mime`。要采响应体，请求发生后尽快收工，别开着页面逛。
- 响应常被包一层：`{data:{list:[...]}}` / `{result:{records:[...]}}`。判「这是不是数据源」要递归找第一个对象数组，不能只看顶层。
- 只记 XHR/Fetch：`Document` 类型是 HTML，抓了也没结构；静态资源（js/css/png）要减分，否则排序被噪声占满。

## 探查（probe）口径

- **必须在已登录的浏览器页面内 `fetch(credentials:'include')`**，不要用 Node 直接请求：Node 没 cookie，401 会被误判成「没接口」。
- 默认只放行 GET/HEAD/OPTIONS；POST/PUT/DELETE 必须显式 `--go`（可能写数据）。
- **最小参数集判定要拿基线比**：首次复现有 N 行，删掉某参数后必须仍有 >0 行、且是同样的数组形态，才算「可删」；只看 `status 200 + 有字段` 会把「返回空壳的必需参数」误判成可删。
- 结论只给三种：能接口化 / 只能 UI / 需要额外鉴权（缺什么写清楚）。不许出现「可能可以」这种话。

## 汇报纪律（用户 2026-11-04 纠过）

1. **样例结果必须标「样例」**：拿 fixture/演示数据跑出来的映射、行数，汇报时第一句就写「这是样例数据推的」，否则用户会以为你把映射写死了。
2. **用户问「为什么不能自动」时，先真机验证能力边界，再解释原因**。本次一开始用「需要 URL + 首次登录」解释「绕不过」，实际是代码有 bug —— 用户连问三次才逼出来。正确顺序：**先跑一次证据 → 再说限制在哪**。
