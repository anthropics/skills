---
name: industry-trends-analysis
description: 行业动态与趋势分析，产出带来源索引与分级的高价值洞察报告；支持按行业视角（persona）分析，以及创建新的行业 persona。用于跟踪某行业动态、做月度/周度趋势分析、生成可快速查看的 MD 报告；或当用户要求「创建行业视角」「新建 persona」「添加行业」时，引导并生成新 persona 文件。当用户要求「行业动态」「趋势分析」「AI for Design 月刊」「设计行业前沿」或「创建/新建/添加行业（persona）」时使用。
---

# 行业动态趋势分析

本 Skill 用于在**排除噪音、严格核查**的前提下，跟踪行业动态并生成**一份便于快速查看的 Markdown 报告**。背景：订阅源过多导致熵增与注意力分散，缺的是筛选与优先级；目标为快速跟踪、高价值聚合与真实洞察汇总。

## 角色与目标

- **角色**：行业动态与趋势分析专家，负责筛选高价值信息、排除低质/幻觉、产出可追溯的洞察报告。
- **交付物**：一次分析工作流产出的 **MD 报告**（按模板填写，含总览、动态至少 10～N、总结与展望、来源链接索引）。

## 何时使用本 Skill

- 用户明确要求某行业动态/趋势/月刊式报告；
- 或要求「像 AI for Design 那样的内部战略参考」；
- 或要求带来源索引与分级的行业洞察、便于快速查看的 MD 报告；
- 或要求**创建/新建/添加**行业视角（persona），以支持后续用该视角做分析。

## 意图识别与推荐语法

本 Skill 支持两种意图，从用户消息中解析后分支执行。**推荐写法**（顺序不拘，能表达清楚即可）：

| 意图 | 推荐语法示例 | 说明 |
|------|----------------------|------|
| **分析** | `@industry-dynamics-trends 分析 ai-for-design 本月` | 用指定 persona 做趋势分析（必须先确认行业再执行） |
| **分析** | `分析 --persona=fintech --month=2月` | 伪参数形式，解析出 persona + 时间即可 |
| **分析** | `用 金融科技 视角 调研本月动态` | 自然语言，解析出行业 + 时间 + 动作 |
| **创建** | `@industry-dynamics-trends 创建行业 金融科技` | 新建名为「金融科技」的 persona |
| **创建** | `create persona fintech` / `新建 persona 金融科技` | 同上，创建后可用「分析 fintech 本月」调用 |

- **分析**：必须得到用户对**行业视角**的确认后再执行；未指定行业时提示「请指定行业视角，例如：AI for Design、金融科技」或列出当前支持的行业。
- **创建**：按 [references/create-persona.md](references/create-persona.md) 流程，基于 `references/industries/_template.md` 生成 `references/industries/{key}.md`，并可选更新 `references/industries/README.md` 索引。

## 报告模板与行业覆盖 (A+B)

- **默认**：报告结构以 `assets/report-template.md` 为准（总览、动态 1～N、总结与展望、来源链接索引）。
- **行业实例可覆盖**：
  - **报告标题**：如「AI for Design 行业前沿洞察」→ 可由实例改为「金融科技监管与创新月报」等。
  - **三条目名称**：每条动态的 3 个子项标签。默认/示例为【最新动态】/【行业风向】/【设计启发点】；实例可改为【最新动态】/【监管与风险】/【落地建议】等，与 `output-format.md` 中「其他行业可替换」一致。
- 若行业实例未定义覆盖项，则使用 template 中的默认标题与三条目名称。

## 执行流程 (Workflow)

**先判断意图**（创建 vs 分析）：

- **创建 persona**：按 [references/create-persona.md](references/create-persona.md) 执行：确定 key/显示名 → 基于 `references/industries/_template.md` 填空 → 写入 `references/industries/{key}.md` → 可选更新 `references/industries/README.md`。
- **分析（出报告）**：按下述 1～3 步；**必须先得到用户对行业视角的确认**后再执行。

**分析分支三步**：

1. **解析并加载行业实例**：从用户请求中解析**行业**（必选）、**时间范围**（可选，默认本月）、**动作**（可选）；将行业映射为实例 key（如「AI for Design」→ `ai-for-design`），加载 `references/industries/{key}.md`。**未指定行业**时：提示「请指定行业视角」并列出当前支持行业（见 `references/industries/README.md` 或该目录下 `.md`，排除 `_template.md`）。**指定了但无对应实例**：同上列出支持列表。采用实例文件中的角色、核查协议、规则；若实例中定义了**报告标题**与**三条目名称**则覆盖 template 默认值（见上文 A+B）。
2. **检索与核查**：严格执行 `references/verification-curation.md`（时间戳、信源交叉验证、挤水分、硬核过滤、原声引用、关键数据二次核查、高价值/噪音分级）；按需执行 `references/source-discovery.md` 中的信源维度，并遵守 `references/multimedia-curation.md` 对图片/视频的采集与引用要求；行业实例内若有额外检索与筛选要求一并执行。
3. **撰写报告**：按 `references/output-format.md` 与 `assets/report-template.md`（及行业实例中的覆盖项）输出 Markdown 报告；文末必须带完整「来源链接索引」，每条【最新动态】句末带行内引用 [n]。

## 输出与引用规范

- 行内引用：句末使用 `[1]`、`[2]`… 递增。
- 重要数据/观点尽量**原声 quote**并指向来源。
- 关键数据若已二次核查可注明，无法核查须标注「待核查」。
- 报告文末必须包含「来源链接索引」表，格式见 `references/output-format.md`。

## 资源导航

| 用途 | 文件 |
|------|------|
| 核查与 Curation 细则 | [references/verification-curation.md](references/verification-curation.md) |
| 信源发现维度 | [references/source-discovery.md](references/source-discovery.md) |
| 多媒体与证据采集 | [references/multimedia-curation.md](references/multimedia-curation.md) |
| 配图/视频采集清单（行业动态报告） | [checklists/asset-collection.md](checklists/asset-collection.md) |
| 报告结构与格式 | [references/output-format.md](references/output-format.md) |
| 报告填空模板（默认结构，可被行业覆盖标题与三条目） | [assets/report-template.md](assets/report-template.md) |
| **创建新行业 persona** | [references/create-persona.md](references/create-persona.md) |
| Persona 模板（新建时复制填空） | [references/industries/_template.md](references/industries/_template.md) |
| 已支持行业索引（列出 key 与显示名） | [references/industries/README.md](references/industries/README.md) |
| 行业实例目录（每文件 = 一行业视角） | `references/industries/*.md`，示例 [ai-for-design.md](references/industries/ai-for-design.md) |
| 定时执行（仅参考） | [references/scheduling.md](references/scheduling.md) |

**如何添加行业**：走**创建**意图，按 [references/create-persona.md](references/create-persona.md) 执行；或手动在 `references/industries/` 下新建 `{key}.md`（结构参考 `_template.md` 与 `ai-for-design.md`），并在 `README.md` 中追加一行索引。

## Guardrails

- 禁止无来源的断言；禁止忽略时间戳或信源校验。
- 关键数据未二次核查时须在报告中标注「待核查」。
- 单次报告最多 20 条动态，宁缺毋滥。
