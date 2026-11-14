# 对标 web-recorder（市场包）→ 本工厂吸收了什么（2026-11-06）

用户把市场包 `web-recorder`（Playwright 录制 → 生成脱浏览器的 Python 成品，5069 行 / 6 文件 / 7MB）
摆出来问"它比你强的 5 条"，结论：**只抄纪律，不换架构**。本文留档对比结论 + 每条落在哪个脚本。

## 一、九维对比（结论：定位不同，不是替代关系）

| 维度 | web-recorder（市场） | 本工厂（skill-forge） |
|---|---|---|
| 定位 | 一次性产物：录一遍出一个 Python 成品 | 探最短路 + 模板化生包 + 生命周期管理 |
| 产物 | `run_api.py`（requests + openpyxl，脱浏览器） | `.mjs` 页面内 fetch / UI 回放包 |
| 录制器 | Playwright + chromium + 7 个 npm 包 | 原生 CDP，零依赖 |
| 流程 | 11 阶段 | 3 步（录 → 证探 → 固） |
| 参数判定 | 二次录制逐层 diff | `--minimize` 删参数试（弱） |
| 认证 | 独立账密登录通道 | 只复用已登录浏览器（离不开人） |
| 生成 | AI 手写脚本 | `build_skill.mjs` 模板化 |
| 失败闭环 | 最多修 5 轮 | broken 标记 / 3 次重录升版 / zip 7 天 / 台账 |
| 经验沉淀 | 按域名 `site-experience/<domain>.md` | 按主题散在 references/ |

## 二、吸收的 5 条（全部落成代码，不是文档）

| # | 抄什么 | 落在哪 | 关键实现 |
|---|---|---|---|
| 1 | 二次录制对比 | 新增 `scripts/diffrec.mjs` | 两份 rec 逐层 diff（URL/Query/Headers/Body/字段+行数），一样=常量、不同=变量；输出 `对比报告.md` + `参数判定.json` |
| 2 | 请求体模板替换铁律 | `probe.mjs`（草稿带 `bodyTemplate`）+ `build_skill.mjs`（无原文模板拒绝生成）+ `api_run.mjs`（只换 `{{k}}`） | 模板从录制 JSON 结构整段来，只把变量叶子换成 `{{k}}`；JSON 值做转义、form 值做 URL 编码 |
| 3 | 字段数校验 | `build_skill` 写 `校验.fieldCount`；`api_run` 比对 | 不一致非 0 退出；`--allow-fields` 本次放行并打 ⚠️ |
| 4 | 独立账密登录通道 | 新增 `scripts/login.mjs` | 专属 `user-data-dir`；`SF_USER`/`SF_PASS` 环境变量；成功必须有证据（success-url/success-sel），错密码 exit 2 |
| 5 | 按域名建站点经验库 | 新增 `references/site/`（README + `_模板.md`） | 命名 `<host>.md`；开工先读、跑通回写；只写验证过的 |

配套：`api_run --dry`（只渲染 URL/body，不碰浏览器）、`--profile` + `--bg`（无人值守）、
`test/run_forge_v2_test.mjs`（21 条断言，含两条负例）。

## 三、没抄的（判断依据：现在的架构更强）

- **Playwright 录制**：多 7 个 npm 包、7MB，只为录制；原生 CDP 零依赖够用。
- **AI 手写 `run_api.py`**：手写＝不可复生产、改版就废；模板化生包 + 台账才能管版本。
- **一次性产物**：没有 broken 标记/重录升级/台账，跑久了没人知道哪条还活着。
- **最多修 5 轮**：我们的判据是失败 3 次整条重录并升版，比"死磕"更省人。

## 四、它反而该学我们的

接口候选打分（≥6 分才值得探）、零依赖 CDP 录制、模板化生成、失败 3 次重录 + 版本台账 + zip 7 天。

## 五、字段口径学不了，但结构可学

某投放平台后台「推直播 78 列 / 推商品 75 列」是平台列号，抄不过来；**可抄的是"覆盖率对账"这个方法**：
找自己链路的总消耗/分项/素材级三列 → 跑同区间算系数区间 → 写进校验，越界即拦。
