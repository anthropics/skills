# Academic Research Skills for Claude Code

[![Version](https://img.shields.io/badge/version-v3.16.0-blue)](https://github.com/Imbad0202/academic-research-skills/releases/tag/v3.16.0)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20696614-blue)](https://doi.org/10.5281/zenodo.20696614)
[![License: CC BY-NC 4.0](https://img.shields.io/badge/license-CC%20BY--NC%204.0-lightgrey)](https://creativecommons.org/licenses/by-nc/4.0/)
[![Sponsor](https://img.shields.io/badge/sponsor-Buy%20Me%20a%20Coffee-orange?logo=buy-me-a-coffee)](https://buymeacoffee.com/crucify020v)

[English](README.md) | [繁體中文版](README.zh-TW.md) | [日本語版](README.ja-JP.md) | [한국어](README.ko-KR.md)

一套完整的学术研究 Claude Code 技能包，涵盖从研究到论文出版的全流程。

**30 秒安装**（Claude Code CLI / VS Code / JetBrains，v3.7.0+）：

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

安装后运行 `/ars-plan`，ARS 会用苏格拉底式对话帮你规划章节结构。需要前置条件或传统 symlink 安装，请看 [快速安装](#快速安装)。

> **AI 是你的副驾驶，不是机长。** 这个工具不会替你写论文。它处理繁琐工作：搜文献、排格式、验数据、查逻辑一致性。这样你就能专注在真正需要思考的事上：定义问题、选择方法、解读数据意义、写出「我认为」后面那句话。
>
> 和 humanizer 不同，这个工具不是帮你隐藏使用 AI 协作的事实，而是帮你把关文章质量。风格校准会从你过去的文章中学习你的声音，写作质量检查会识别让文字读起来像机器生成的模式。目标是质量，不是掩饰。

### 为什么选「人机协作」而不是「全自动」？

Lu 等人（2026，*Nature* 651:914-919）发表的 **The AI Scientist** 是第一个端到端全自动的 AI 研究系统，其生成的论文通过 ICLR 2025 workshop 的盲审（评分 6.33/10，workshop 平均 4.87）。他们自己的 Limitations 段落也列出了这类系统会遇到的结构性失败模式：实现错误、幻觉实验结果、取巧特征依赖、实现错误被包装成「意外发现」、方法论伪造、框架锁定、引用幻觉。

ARS 建立在这个前提上：**人类研究者 + AI 的组合，比纯自动或纯人工更能避开这些失败模式**。Stage 2.5 与 Stage 4.5 学术诚信闸门运行 7 类阻断式检查清单（见 [`academic-pipeline/references/ai_research_failure_modes.md`](academic-pipeline/references/ai_research_failure_modes.md)），reviewer 也提供 opt-in 的 calibration mode 用用户提供的 gold set 测量 FNR/FPR。

[**Zhao 等人**](https://arxiv.org/abs/2605.07723)（2026-05）盘点了 arXiv、bioRxiv、SSRN、PMC 上 250 万篇论文中的 1.11 亿条引用，保守估计 2025 年单年就有 146,932 条幻觉引用，并观察到 2024 年中是上升的拐点；bioRxiv-to-PMC 这条配对的「预印本进入正式发表版本」幻觉存活率达 85.3%。他们把「真实引用被用来支撑被引文献其实没有提出的主张」描述为当前未解的问题。ARS v3.7.1 为来源 provenance 加上 trust-chain frontmatter，v3.7.3 为未来的 claim-level 审计铺设 locator 基础设施（三层引用 anchor），并在引用阶段呈现 advisory 风险信号（ARS 内部把这条 claim-faithfulness 缺口标记为「L3」，此为 ARS 的用词，不是论文的用词）。v3.7.x 的设计动机来自 Zhao 等人的 corpus-scale 发现；ARS 本身的 corpus-scale 评估仍是未来工作。

v3.8 补上 L3 缺口的另一半。v3.7.3 让每一条引用都带 locator anchor，v3.8 在这个基础上加一道 opt-in 审计（`ARS_CLAIM_AUDIT=1`）：获取每个 anchor 指向的原始文本，判断论文里的 claim 是否真有被该引用支撑。五类新的 HIGH-WARN annotation（claim-not-supported、negative-constraint-violation、fabricated-reference、anchorless、constraint-violation-uncited）会在 formatter terminal hard gate 直接阻止输出。Calibration 随 release 提供 20 条 gold set，采用 FNR<0.15、FPR<0.10 双阈值；正式放大投入前要先有 calibration 证据（v3.8 spec §5）。

v3.3 的灵感来自 [**PaperOrchestra**](https://arxiv.org/abs/2604.05018)（Song, Song, Pfister & Yoon, 2026, Google）：Semantic Scholar API 验证、反泄露协议、VLM 图表验证、分数轨迹追踪。

---

## 架构与 pipeline

**👉 [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md)** — 完整 pipeline 视图：流程图、阶段 × 维度矩阵、数据访问流、skill 依赖图、质量闸门、模式清单。

这份架构文档取代了原本散在 README 各处的 pipeline 描述。关于「哪个阶段跑什么」的所有信息都集中在一个地方。

## 快速安装

**前置条件**

- [Claude Code](https://docs.claude.com/en/docs/claude-code/setup)（建议最新版；plugin packaging 需要近期版本）
- 已导出 `ANTHROPIC_API_KEY`，或在第一次运行 `claude` 时设置
- *选用：* Pandoc 用于 DOCX 输出，tectonic + 思源宋体 TC 用于 APA 7.0 PDF（纯 Markdown 输出不需要这两者）

**Plugin 安装（v3.7.0+，推荐）：**

```text
/plugin marketplace add Imbad0202/academic-research-skills
/plugin install academic-research-skills
```

**验证可用：** 运行 `/ars-plan` 并描述你正在写的论文，ARS 会用苏格拉底式对话帮你规划章节结构。如果想做单次测试，可以运行 `/ars-lit-review "你的主题"`。

**👉 [docs/SETUP.md](docs/SETUP.md)** — 完整指南：安装 Claude Code、设置 API key、选用的 Pandoc/tectonic（DOCX/PDF）、跨模型验证（`ARS_CROSS_MODEL`），以及六种安装方式（Plugin、项目 skills、全局 skills、claude.ai Project、repo clone、Claude Science 导入）。

**使用 Claude Science？** 四个 skill 可直接导入：**Skills → Import from GitHub**，粘贴 `https://github.com/Imbad0202/academic-research-skills`，点 **Preview**，再点 **Import 4 skills**（需本 repo v3.14.0+——导入器读取 marketplace manifest 中显式声明的 skill 路径）。导入是一次性快照：ARS 更新后需重新导入。导入的 skill 承载 ARS 方法论（研究／写作／评审协议）；Claude Code 专属机制——slash commands、hooks、subagent 编排——不会转移。详见 [docs/SETUP.md](docs/SETUP.md) Method 5。

**用 Codex CLI？** 请安装姐妹版：[`Imbad0202/academic-research-skills-codex`](https://github.com/Imbad0202/academic-research-skills-codex)。同一套 workflow 内容，Codex 原生打包为单一 `$academic-research-suite` skill，提供 `ars-*` 别名。

## 性能与费用

**👉 [docs/PERFORMANCE.md](docs/PERFORMANCE.md)** — 各模式 token 预算、完整 pipeline 估算（一篇 15k 字论文约 ~$4–6），以及建议的 Claude Code 设置（Auto 模式；Agent Team 选用）。

## 使用指南与文章

- [学术写作不该是一个人的事：一套开源 AI 协作工具如何改变研究者的工作流](https://open.substack.com/pub/edwardwu223235/p/ai?r=4dczl&utm_medium=ios) — 完整使用指南（繁体中文）
- [Academic Writing Shouldn't Be a Solo Act](https://open.substack.com/pub/edwardwu223235/p/academic-writing-shouldnt-be-a-solo?r=4dczl&utm_medium=ios) — Full pipeline walkthrough (English)

---

## 功能特色一览

- **Deep Research** — 13 个 Agent 的研究团队，支持苏格拉底引导、PRISMA 系统性回顾、意图检测、对话健康度监控、可选跨模型 DA、Semantic Scholar API 验证。
- **Academic Paper** — 12 个 Agent 的论文撰写团队，含风格校准、写作质量检查、LaTeX 输出强化、可视化、修订教练、引用格式转换、反泄露协议、VLM 图表验证。
- **Academic Paper Reviewer** — 7 个 Agent 的多视角同行评审，0-100 质量量表（主编 + 3 位动态审查者 + 魔鬼代言人），含让步门槛协议、攻击强度保持、可选跨模型 DA critique / calibration、R&R 追溯矩阵、只读约束。
- **Academic Pipeline** — 10 阶段全流程调度器，含自适应 checkpoint、主张验证、材料护照、可选 `repro_lock`、可选跨模型学术诚信验证、中途强化机制、分数轨迹追踪。
- **数据访问层级标注**（v3.3.2+）— 每个 skill 声明 `data_access_level`（`raw` / `redacted` / `verified_only`），由 `scripts/check_data_access_level.py` 强制执行。设计灵感来自 Anthropic 的 automated-w2s-researcher（2026）。详见 [`shared/ground_truth_isolation_pattern.md`](shared/ground_truth_isolation_pattern.md)。
- **任务类型标注**（v3.3.2+）— 每个 skill 声明 `task_type`（`open-ended` 或 `outcome-gradable`）。目前 ARS 所有 skills 皆为 `open-ended`。
- **Benchmark 报告 Schema**（v3.3.5+）— JSON Schema + lint script，要求诚实的 benchmark 比较报告。详见 [`shared/benchmark_report_pattern.md`](shared/benchmark_report_pattern.md)。
- **Artifact 可复现性 Lockfile**（v3.3.5+）— Material Passport 添加可选 `repro_lock` 子区块。**是配置文档化，不是重播保证** — LLM 输出不是逐字节可复现。详见 [`shared/artifact_reproducibility_pattern.md`](shared/artifact_reproducibility_pattern.md)。
- **实验来源凭证登录**（#260）— Material Passport 可选的 `experiment_provenance[]` 记录研究者在**外部**跑过的实验（ARS 从不执行实验），论文主张通过 `claim_intent_manifest.planned_experiment_ids[]` 与之 join。诚信 gate（Stage 2.5/4.5）逐条比对实验支撑型主张与登录凭证 — `ALIGNED` / `OVERSTATED` / `NOT_SUPPORTED_BY_PROVENANCE` / `PROVENANCE_INSUFFICIENT` — **但不判定实验本身是否正确**。fail-closed 的 `experiment_intake_declaration` 让「有没有跑实验」成为 Stage 1 明确决定。详见 [`shared/handoff_schemas.md`](shared/handoff_schemas.md)。

---

## 实际产出展示

查看完整 10 阶段 pipeline 的实际产出 — 包含**同行评审报告、学术诚信验证报告、完稿论文**：

**[浏览所有 pipeline 产出 →](examples/showcase/)**

| 产出物 | 说明 |
|---|---|
| [完稿论文（英文）](examples/showcase/full_paper_apa7.pdf) | APA 7.0 格式，LaTeX 编译 |
| [完稿论文（中文）](examples/showcase/full_paper_zh_apa7.pdf) | 中文版，APA 7.0 |
| [学术诚信报告 — 审稿前](examples/showcase/integrity_report_stage2.5.pdf) | Stage 2.5：发现 15 个虚构引用 + 3 个统计错误 |
| [学术诚信报告 — 最终](examples/showcase/integrity_report_stage4.5.pdf) | Stage 4.5：确认零回归 |
| [同行评审第一轮](examples/showcase/stage3_review_report.pdf) | 主编 + 3 审查者 + 魔鬼代言人 |
| [再审](examples/showcase/stage3prime_rereview_report.pdf) | 修订后验证审查 |
| [同行评审第二轮](examples/showcase/stage3_review_report_r2.pdf) | 跟踪审查 |
| [回复审查意见](examples/showcase/response_to_reviewers_r2.pdf) | 逐点回复 |
| [出版后审计报告](examples/showcase/post_publication_audit_2026-03-09.pdf) | 独立全引用审计：发现 21/68 篇问题，在 3 轮学术诚信审查后仍被漏掉 |

---

## 搭配工具：Experiment Agent

如果你的研究需要在写作前做实验（代码或人工研究），[Experiment Agent](https://github.com/Imbad0202/experiment-agent) 技能填补 ARS Stage 1（研究）和 Stage 2（写作）之间的空缺。

```
ARS Stage 1 研究      →  RQ Brief + Methodology Blueprint
        ↓
  experiment-agent     →  运行/管理实验 → 验证结果
        ↓
ARS Stage 2 写作      →  用验证过的实验结果撰写论文
```

**功能**：执行代码实验（Python、R 等）并实时监控、管理人工研究 protocol 与 IRB 伦理审查、11 种统计谬误检测、可复现性验证。

**搭配使用方式**：ARS pipeline 完成 Stage 1 后暂停，在另一个 experiment-agent session 中执行实验，完成后将结果（含 Material Passport）带回 ARS Stage 2。ARS 不需要任何修改。详见 [experiment-agent README](https://github.com/Imbad0202/experiment-agent)。

---

## 使用方式

### 快速开始

```
# 启动完整研究 pipeline
你: "我想做一篇关于 AI 对高等教育质量保障影响的研究论文"

# 苏格拉底引导模式
你: "引导我研究 AI 在教育评估中的应用"

# 引导式论文撰写
你: "引导我写一篇关于少子化影响的论文"

# 审查现有论文
你: "帮我审查这篇论文"（接着提供论文）

# 查看 pipeline 进度
你: "进度" 或 "status"
```

### 个别 Skill 使用

#### Deep Research（深度研究，8 种模式）

```
"研究 AI 对高等教育的影响"                    → full mode（完整研究）
"给我一份 X 的快速摘要"                       → quick mode（快速简报）
"帮我做 X 的系统性文献回顾，含 PRISMA"        → systematic-review mode
"引导我研究 X"                                → socratic mode（苏格拉底引导）
"帮我核查这些说法"                            → fact-check mode（事实核查）
"帮我做文献回顾"                              → lit-review mode（文献回顾）
"审查这篇论文的研究质量"                      → review mode（论文审查）
```

#### Academic Paper（学术论文撰写，11 种模式）

```
"帮我写一篇论文"                              → full mode（完整撰写）
"引导我写论文"                                → plan mode（引导规划）
"先帮我搭论文大纲"                            → outline-only mode（只做大纲）
"我有初稿，这是审稿意见"                      → revision mode（修订）
"帮我整理这些审稿意见成修订路线图"            → revision-coach mode
"帮我写这篇的摘要"                            → abstract-only mode（摘要）
"把这批数据写成文献回顾论文"                  → lit-review mode（文献回顾论文）
"转换成 LaTeX" / "引用格式转 IEEE"            → format-convert mode（格式转换）
"检查引用格式"                                → citation-check mode（引用检查）
"帮我生成 NeurIPS 的 AI 使用声明"             → disclosure mode（AI 使用声明）
```

#### Academic Paper Reviewer（论文审查，6 种模式）

```
"审查这篇论文"                                → full mode（主编 + R1/R2/R3 + 魔鬼代言人）
"快速评估这篇论文"                            → quick mode（快速评估）
"引导我改进这篇论文"                          → guided mode（引导改进）
"检查研究方法"                                → methodology-focus mode（方法论聚焦）
"验收修订"                                    → re-review mode（再审验收）
"用我的 gold set 校准 reviewer"               → calibration mode（校准）
```

#### Academic Pipeline（全流程调度器）

```
"我想做一篇完整的研究论文"                    → 从 Stage 1 开始完整 pipeline
"我已经有论文，帮我审查"                      → 从 Stage 2.5 进入（先做学术诚信审查）
"我收到审稿意见了"                            → 从 Stage 4 进入
```

> Pipeline 结束时自动产出 **Stage 6：过程记录** — 含论文创建过程记录与 6 维度协作质量评估（1–100 分）。

### 支持语言

- **繁体中文** — 用户以中文对话时默认使用
- **English** — 用户以英文对话时默认使用
- 学术论文自动产出双语摘要（中文 + English）

> **使用其他语言？** 苏格拉底模式（deep-research）和 Plan 模式（academic-paper）采用**意图匹配**启动 — 检测你的请求含义，而非比对特定关键字。这代表它们**支持任何语言**，无需额外设置。
>
> 不过，一般的 `Trigger Keywords` 区块（决定 skill 是否被启动）仍以英文和繁体中文为主。如果你发现 skill 在你的语言下触发不稳定，可以在各 `SKILL.md` 的 `### Trigger Keywords` 区块中加入你的语言的关键字，提高匹配信心。

### 支持引用格式

- APA 7.0（默认，含中文引用规则）
- Chicago（Notes & Author-Date）
- MLA
- IEEE
- Vancouver

### 支持论文结构

- IMRaD（实证研究）
- 主题式文献回顾
- 理论分析
- 个案研究
- 政策简报
- 研讨会论文

---

## Skill 详细信息

各 agent 的职责与各阶段产出物现已移至 [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md)。版本号保留在此以维持 release metadata 集中管理。

### Deep Research (v2.11.0)

13 个 Agent 的研究团队。模式：full、quick、review、lit-review、three-way-scan、fact-check、socratic、systematic-review。完整 agent 名单与产出物：见 ARCHITECTURE.md §3。

### Academic Paper (v3.2.0)

12 个 Agent 的论文撰写 pipeline。模式：full、plan、outline-only、revision、revision-coach、abstract-only、lit-review、format-convert、citation-check、disclosure、rebuttal-audit。输出：MD + DOCX（Pandoc 可用时）+ LaTeX（APA 7.0 `apa7` class / IEEE / Chicago）→ tectonic 编译 PDF。完整 agent 名单与各 phase 职责：见 ARCHITECTURE.md §3。

### Academic Paper Reviewer (v1.10.0)

7 个 Agent 的多视角审查，搭配 **0-100 质量量表**。模式：full、re-review、quick、methodology-focus、guided、calibration。**决策对照：** ≥80 接受、65-79 小修、50-64 大修、<50 退稿。第一轮审查团队 vs. 精简再审团队的分界：见 ARCHITECTURE.md §3 Stage 3 / Stage 3'。

### Academic Pipeline (v3.16.0)

10 阶段调度器，含学术诚信验证、两阶段审查、苏格拉底指导、协作质量评估。Pipeline 保证：每个阶段都需用户确认 checkpoint；学术诚信验证（Stage 2.5 + 4.5）不可跳过；R&R 追溯矩阵（Schema 11）独立验证作者修订主张。v3.4 添加 Compliance Agent（PRISMA-trAIce + RAISE）于 Stage 2.5 / 4.5。v3.5 添加 **协作深度观察员**（`collaboration_depth_agent`，仅咨询性质、永不阻挡流程）于每一次 FULL/SLIM checkpoint 与 pipeline 完成时。MANDATORY 学术诚信闸门（2.5 / 4.5）明确跳过观察员，避免稀释合规检查。理论基础：Wang & Zhang (2026), IJETHE 23:11。逐阶段矩阵（agent、产出物、闸门）：见 ARCHITECTURE.md §3。

---

## v3.0 优化：我们发现了 AI 的哪些结构性限制

在使用 ARS 撰写一篇关于 AI 与高等教育的反思文章时，我们遇到了三个结构性问题：

1. **框架锁定**：AI 在给定框架内越来越精致，但无法质疑框架本身
2. **谄媚倾向**：每次挑战魔鬼代言人的攻击，它都让步得太快
3. **意图检测错误**：苏格拉底模式在用户仍在探索时就急着收敛

### 改了什么

- **魔鬼代言人让步门槛**：反驳必须评分 1-5，≥4 才允许让步。不允许连续让步。框架锁定检测。
- **苏格拉底意图检测**：检测用户是「探索型」还是「目标型」。探索型模式停用自动收敛。
- **对话健康度指针**：每 5 轮后台自检，检测持续同意、回避冲突、过早收敛。
- **跨模型验证**：设置 `ARS_CROSS_MODEL` 激活第二 AI 模型独立审查。详见 [docs/SETUP.md](docs/SETUP.md)。
- **AI 自我反思报告**：Pipeline 结束后自动产出 AI 行为自评。

这些优化不能完全解决 AI 的结构性限制——它们让限制变得可见、可追踪、可被人类介入。

---

## 授权条款

本作品采用 [CC-BY-NC 4.0](https://creativecommons.org/licenses/by-nc/4.0/) 授权。

**你可以自由：**
- 分享 — 复制并分发本作品
- 改编 — 重混、转换、以本作品为基础进行创作

**但须遵守以下条件：**
- **署名** — 你必须给予适当署名
- **非商业性** — 你不得将本作品用于商业目的

**署名格式：**
```
Based on Academic Research Skills by Cheng-I Wu
https://github.com/Imbad0202/academic-research-skills
```

---

## 贡献者

**吴政宜** (Cheng-I Wu) — 作者与维护者

**[aspi6246](https://github.com/aspi6246)** — 贡献者。v3.1 优化灵感来自 [Claude-Code-Skills-for-Academics](https://github.com/aspi6246/Claude-Code-Skills-for-Academics)：只读约束模式、Anti-Pattern 作为一等公民设计、认知框架方法（教「如何思考」而非只有步骤）、精简 skill 体量理念。

**[mchesbro1](https://github.com/mchesbro1)** — 贡献者。最初提出并撰写了 IS Basket of 8 期刊清单（[Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5)）。

**[cloudenochcsis](https://github.com/cloudenochcsis)** — 贡献者。将 IS 章节从 *Basket of 8* 扩充为完整的 *Senior Scholars' Basket of 11*，补上 *Decision Support Systems*、*Information & Management*、*Information and Organization*（[Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7)、[PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8)）。数据源：[AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/)。

**[eltociear](https://github.com/eltociear)**（Ikko Eltociear Ashimine）— 贡献者。翻译了日文版 README（[`README.ja-JP.md`](README.ja-JP.md)）（[PR #161](https://github.com/Imbad0202/academic-research-skills/pull/161)）。

**[xpfo-go](https://github.com/xpfo-go)**（xpfo）— 贡献者。翻译了简体中文版 README（[`README.zh-CN.md`](README.zh-CN.md)）（[PR #181](https://github.com/Imbad0202/academic-research-skills/pull/181)）。

---

## 更新纪录

### v3.16.0（2026-07-12）— 模型分层、跨模型闸门强化、WP 提示语锐化

> **新增：**可选模型分层（#517）— 新 `ARS_MODEL_TIERING` 开关含两个方向（`economy` 让 13 个执行型 agent 以低于 session 模型一档派工、下限 Opus 级；`quality-boost` 让完整性闸门与最终审查面的判断型 agent 升到前沿档）；未设置时逐字节等同旧行为，冻结的 39-agent 分类由新 manifest + lint 钉死。跨模型闸门强化（#518）— 风险分层抽验（HIGH-IMPACT 参考文献在两道闸门 100% 验证）、两个不可逆决策点（设计冻结 + 最终编辑决定）的盲测分歧检查、验证模型 id 状态白名单、升格 bakeoff 协议；原规划的通用第 6 位审查者确定退役、非延期。GPT-5.6 Sol 列为暂定跨模型验证者并增设明确 reasoning-effort 控制（#515）。devCharlotte 提案的韩文触发词 + 路由边界 fixture（#452/#509）。论文写作端新增 CARS 导论修辞 + 标题设计参考文件（#500）。**变更：**WP 研究问题提示语经名词替换测试泛化到 20 壳表之外（#501）并锐化豁免条款、抓到装饰型标题壳（#505）— held-out 漏判率 0.34–0.38 → 0.094、误触 0/16 维持；审查者校准协议记载 LLM 评审偏宽方向（FARS 锚点，#484）；OpenAlex API key 认证 + 预算感知 429 处理 + arXiv ToU 对齐退避（#495/#496）。**文档：**THIRD_PARTY.md 社区目录（#497/#498）。`academic-pipeline` 跟随套件版本至 v3.16.0；其余三个 skill 版本不变。

### v3.15.0（2026-07-04）— 发版闸门强化、prompt 债务清理第二轮、防漂移锁

> 以发版纪律与质量卫生为主的版本；skill 行为无变更。**新增：**三道 CI 闸门 — CHANGELOG-covers-merges tag 前闸门（#483）、版本一致性 invariant 9-11 加 tag 时重跑闸门（#487）、把 SessionStart announce 清单钉到实际 16 个指令清单的 command-invariants 闸门（#486）— 以及两道防漂移锁：Phase Boundary enforcement 句在全部 23 个 Bucket A agent 区块逐字钉死、SETUP 跨模型示例与 canonical 型号表互相钉死（#491 → #492）。**变更：**prompt 债务清理第二轮深扫第一轮延后的 17 个 agent（#489 → #490）：修正两个 socratic_mentor 的活矛盾（过期的 15 轮劝退规则 vs 文档明载的典型 20-30 轮）、修正全仓库 29 处过期的 enforcement 状态句、修剪 7 个 agent 的 few-shot 与重复流程脚手架 — 经 4 批并行稽核 + 独立 codex 跨模型挑战验证；稽核报告在 `audits/`。**修复：**DOI 徽章改由 shields.io 提供（#482）。`academic-pipeline` 跟随套件版本至 v3.15.0；其他三个 skill 版本不变。

### v3.14.0（2026-07-02）— Claude Science 可导入性、eval comment 呈现、prompt 债务清理

> 一个以可移植性与打磨为主的 release，skill 行为无变更。**新增：** Claude Science 可导入性——marketplace manifest 显式声明 skill 路径，让无法穿越 symlink `skills/` 目录的 GitHub-API 导入器（Claude Science「Import from GitHub」、Windows checkout）能找到全部四个 skill；已在 Claude Science 端到端验证，README + SETUP 新增导入指南（#480）。eval-harness 的 PR comment 改为一行结论 + 逐任务表格、原始 JSON 折叠进 `<details>`，取代裸贴整份报告——仅显示层，gate 逻辑字节不变（#479）。**变更：** 依 2026-07 harness-retirement 审计，自四个写作面 agent 移除过期的 writing-harness scaffold（#476/#477 → #478，净 −111 行 prompt）；remind-don't-block 的 Platform Port Reminder 在 PR 新增顶层目录时提示 platform-ports 政策（#473）。**文档：** devCharlotte 母语审校的韩文 README（#469/#471）；GitHub Copilot repository instructions（#465）；建议 auto permission mode 取代 Skip Permissions（#464）。累积于 `[Unreleased]` 的 16 条积压条目（代码均在 v3.13.0 tag 前已上——diff/patch revision mode #390、submission-package verifier #394、eval gold sets #215/#216 等）并入版本记录；详见 `CHANGELOG.md`。`academic-pipeline` 随 suite 至 v3.14.0；其余三个 skill 版本不变。

### v3.13.0（2026-06-18）— Hook 可移植性、provider-agnostic 验证、guard 正确性

> 一个 minor release，强化安装／执行面并扩展跨模型范围。**修正：** 写入范围 guard 在 git-clone + symlink 安装布局下不再误挡使用者自己的 `CLAUDE.md`（#459，收掉 #448/#449 的残余一半——`CLAUDE.md` 是文档而非承载 enforcement 的档案，故移出 infra 保护清单，所有承载档案仍受保护）；Windows Python hook 可移植性 + 无 Python 时优雅降级，改由跨平台 `hooks/run_guard.sh` launcher 启动，会拒绝 0-byte 的 Microsoft Store `python3` stub 且不再洗 hook log（#454）；`draft_writer` dual-phase static union 文档化 + Windows POSIX-safe 路径匹配（#451）。**新增：** provider-agnostic 跨模型验证，接受 OpenAI 相容端点（MiMo、DeepSeek、自架）与 grounded first-party OpenAI 并存，且后者绝不被静默降级（#455）；opt-in 的 Socratic 邻近 framing probe（借自 STORM 的视角扩展，`ARS_SOCRATIC_ADJACENT_PROBE=1`，预设 OFF，纯 prose-layer——`deep-research` 2.10.0 → 2.11.0）（#461）。`academic-pipeline` 随 suite 至 v3.13.0；`academic-paper` 与 `academic-paper-reviewer` 不变。逐 issue 细节见 `CHANGELOG.md`。

### v3.12.1（2026-06-15）— 审稿回复分流模式（PR #433 整合）

> 一个 patch release，依 ARS 的模式化架构，把一份外部贡献中真正具新意的部分收进既有 skill 成为模式。**新模式：** `deep-research` `three-way-scan` —— 介于 `quick` 与 `lit-review` 之间的轻量 WHY/HOW/WHAT 论文比较分流，产出逐论文短清单加跨论文统合（`deep-research` 2.9.4 → 2.10.0）；`academic-paper` `rebuttal-audit` —— 对作者既有的 rebuttal／回复草稿，比对审稿意见做独立的咨询式 QA（逐条覆盖表 + 缺口清单 + 语气／证据／误读风险旗标），它不产生任何内容，且独立调用时明确抑制 Schema 11／Material Passport 写入／`ready_to_submit`（由带 mutation 覆盖的 `check_rebuttal_audit_guard()` lint 强制）；另含 `revision-coach` 范围扩展到反驳／不同意姿态与非期刊情境，以及 `/ars-3w` + `/ars-rebuttal-audit` 斜线指令。依输入形状路由：审稿意见加草稿 → `rebuttal-audit`；仅意见 → `revision-coach`。整合自 [@Yaobin29](https://github.com/Yaobin29) 的 [PR #433](https://github.com/Imbad0202/academic-research-skills/pull/433)。Suite 模式数 25 → 27（仍 4 个 skill）。逐 issue 细节见 `CHANGELOG.md`。

### v3.12.0（2026-06-08）— Kong 自动研究功能线：实验来源、图表保真、跨论文矛盾、部分证据拆解

> **[machine-translated]** 本条目为机器翻译，待母语 contributor 校订；以英文版 CHANGELOG 为准。

> 一个 minor release，落地 Kong et al.（2026，arXiv:2605.18661）自动研究功能线，以及部分证据陷阱的拆解工作，每项都已各自审查并 merge。**新功能：** 实验来源登录 + 宣称对实验对齐 —— 为实验支撑的宣称建立 schema-first 的证据帐本层，只做登录与对齐（学者在外部跑实验，ARS 从不执行）（#260）；图表保真 gate，查验 caption 的诠释是否从资料推得、论文是否拿该图表佐证它真正支撑的宣称（#261）；结构化的跨论文矛盾盘点，把已评估的论文对列举出来供学者确认（#262）；以及在引用判定（#213）与编辑统合（#214）两层都先做子宣称拆解再判定，于两层收敛 §F.3.2 部分证据陷阱。**引导与诠释层：** 对产报告的审稿人加上精简输出 + 抗压边界强化（#274）；同源／rubric-aware 校准的认识论注记（#273）；把检索内容的指令／资料边界订为常设原则（#367）。**负面范围：** Kong META（#255）收尾，在 `POSITIONING.md` 加「拒绝机制」段落列举 ARS 不做的五种自主机制，外加两份 Tier D 设计教训文件。**发版纪律 lint：** version-consistency 不变量 5–7（#357）与 ARCHITECTURE 元件版号稽核（#345）。另含跨模型 grounding guard（#346 / #349 / #351）、引用 gate 快取键与 rationale 上界（#359 / #360 / #361）、eval 黄金集（#250）、ACL/EMNLP 揭露重新接地（#242）等正确性修正。新增的 schema、manifest 字段与所有不变量皆为增量、向后兼容。`academic-pipeline` 随 suite 升至 v3.12.0；其余三个 skill 版号不变。逐 issue 细节见 `CHANGELOG.md`。

### v3.11.1（2026-06-06）— 出货后正确性、强化与来源修正汇整

> 一个 patch release，汇整 v3.11.0 出货后浮现的修正，每项都已各自审查并 merge：把跨模型同意 gate 扩展到 integrity-verification + collaboration-depth 路径（#322）、每笔 entry 的 OpenAlex + Crossref backfill 并行化（#138），以及横跨引用存在性 gate、v3.10 政策层、eval harness、领域证据 profile、#310 安全边界边角案例的七项正确性/强化修正（#323 / #327 / #328 / #329 / #331 / #332 / #333）—— 其中两项是 P1（#327 no-handoff 路径上的领域 profile 启动、#328 eval harness 的 per-class 门槛 gate）。无新功能、无破坏性 schema 变更。逐 issue 细节见 `CHANGELOG.md`。

### v3.11.0（2026-06-04）— 确定性引用查验 gate（#182）

> **[machine-translated]** 本条目为机器翻译，待母语 contributor 校订；以英文版 CHANGELOG 为准。

> 新增一道**确定性的引用存在性查验 gate**，独立于 LLM 同侪审查运作。每笔引用都会比对最多四个书目索引（Semantic Scholar、OpenAlex、Crossref，以及新增的 **arXiv resolver**，`scripts/arxiv_client.py`，不需 API key），把每笔引用的 `lookup_verified` 状态（`{true, false, unresolvable}`）写进统一汇整。捏造、带着查不到的 DOI/arXiv ID 的引用，因此被 lookup 侦测标示出来（在用户选用 strict 时才升级为终止），而非寄望审查 agent 注意到。这道 gate **沿用 v3.10 `terminal_policies` 的 opt-in 模型**：侦测一律执行，但 `lookup_verified == false` 的列只有在用户选用 `terminal_policies.citation_existence == strict` 时才是终止性的；默认行为是 advisory、可用 `/ars-mark-read` 认可。`false` 的定义刻意**收窄到 ID-keyed unmatched**（一次以精确 DOI/arXiv 查验、却证实查不到），因此正当但未被索引的人文 / 非英语 / 区域期刊引用会落在 `unresolvable`、永不阻挡（这是文件中载明的「精确优先于召回」取舍）。本版另含持久化 SQLite 查验 cache（`~/.cache/ars/verification.db`，90 天 TTL）搭配 `/ars-cache-invalidate` 指令、独立的 `verification_gate` API 与 `verify_passport.py` CLI，以及把 v3.9.0 污染三角验证矩阵扩成四索引（k=0..4，全属 advisory）。`academic-pipeline` 追 suite 至 v3.11.0，其余三个 skill 版号不变。规格：`docs/design/2026-05-21-v3.10-182-promote-citation-gate-spec.md`（§0 amendment + C-V6）。

### v3.10.0（2026-06-01）— 三角验证政策层、Kong 综述采纳、评测 harness、scoped-write guard

> Minor release，打包数项工作：可选用的污染三角验证 **terminal 政策层**（#127，默认引用行为与 v3.9.0 byte-equivalent）；**Kong et al. 2026 综述采纳**，包含 Rebuttal Commitment Ledger（#256/#266/#268/#269）与依学门的 domain evidence profile（#259）；**v3.10 量测基建**，通用化评测 gold set 加 ranking-lift CI gate（#184）；**scoped-write guard MVP**（#134），一个 deterministic `PreToolUse` hook，把 23 个单一 phase 的 subagent 围进各自的 phase 目录、并禁用它们的 Bash（改用 Grep/Glob 与结构化编辑工具）；`/ars-mark-read` plugin 指令（#190）加一个 broken-on-arrival 修正（#195）；简体中文 README（#185）；以及 CI 强化（#156/#155）。`academic-paper` 升至 v3.2.0、`academic-paper-reviewer` 升至 v1.10.0，反映 Commitment Ledger 与 domain profile 的新增功能；`academic-pipeline` 追 suite 至 v3.10.0。默认 skill 行为不变，除非用户选用 strict 政策模式；唯一 default-on 的改动是 #134 guard，它约束的是被围起来的 subagent，不是面向用户的产出。

### v3.9.4.2（2026-05-19）— PR #149 CI 纪律 gate post-ship hotfix（codex post-ship）

> Codex post-ship review 对 PR #149（7 道 CI 纪律 gate）抓到 4 个 P2 finding；v3.9.4.2 修齐其中 3 个。F1：`harness-retirement-monthly.yml` 补 `GH_REPO`，让调度跑能取到 repo context 给 `gh issue create`。F2：`release-cooldown.yml` 把 `PREV_TAG` 查找 filter 到 `v*` tag，避免非 release tag（如旧 plugin tag）绕过 cooldown gate。F3：`release-cooldown.yml` 加读 annotated tag subject + 接受 `hot-fix` 拼写变体（v3.9.2 在旧检测器下是 false-negative hotfix）。PR #157 follow-up：`[skip-cooldown]` override 改从 commit message 跟 annotated tag message 双处读取（self-bootstrapping fix — 本 tag 的 cooldown 绕过正好证明 F2+F3 端到端可用）。F4（test-count-monotonic 强化）被 revert，因为它 surface 了 `scripts/` package 预存问题，追踪为 #154（已由 PR #158 修复）+ 再次尝试 #155。Closes #152。Follow-ups：#155、#156。

### v3.9.4.1（2026-05-19）— v3.9.4 时序验证 post-ship hotfix（#135 codex post-ship）

> Codex post-ship review 抓到 4 个 per-task subagent reviewer 漏掉的真 bug。Hotfix 一次修齐：(1) `audit()` 把 `citation_provenance` 接到 P2 + P4，遇到 ref slug 在 provenance.yaml 是 `confidence: low` 或 `conflict` 时，验证器改发 `TEMPORAL-METADATA-MISSING` 而不是直接用 timeline 日期当算术 ground truth（spec §3.4 第一手 safety check 原本没接线）。(2) `_date_to_interval` 补齐全部 schema-valid 日期形状，包括 `YYYY-MM`（Crossref 月精度）和 `YYYY-MM-DD..YYYY-MM-DD`（interval），v3.9.4 对这两种 silently `ValueError` 跳过。(3) P4 在 ref marker 缺席时可 bind 直接 prose 日期 — 「The 2026 policy enabled the 2020 rollout」这种句现在会 trigger。(4) `citation_provenance.schema.json` `confidence:high` allOf 加 `then.required`，补 absent-property bypass 漏洞。1561 passed（+12 新测试、0 regression）。ARCHITECTURE.md 同步补齐（先前停在 v3.8.0）。

### v3.9.4（2026-05-18）— #135 时序验证层（advisory）

> Phase 4 → 5 边界添加决定性 advisory verifier，涵盖 5 种时序失效模式（P1 回顾算术、P2 时代错置引用、P3 比较基准未实体化、P4 因果倒置、P5 现在式指示语）。新 Phase 2 sibling `timeline_extraction_agent` 拥有 `phase2_investigation/timeline.yaml` + `phase2_investigation/citation_provenance.yaml`。验证脚本 `scripts/temporal_integrity_audit.py` 运行 5 道确定性 pass。M3 时序完整性铁律加入 `report_compiler_agent` + `draft_writer_agent`。M6-minimal：Crossref `issued` + pdftotext cover 第一手验证。M7-minimal：日期出处 + 比较基准实体化。M5-stub：仅用户声明的 `version_family_id`。`literature_corpus_entry`、`claim_audit_result`、`claim_intent_manifest` 零修改。`bibliography_agent` 未改动（F2 不变量）。3 个新 sidecar schema。覆盖率估计：55-70% 基准 / 含 M7 minimal 65-75%。1549 passed（+44 新测试、0 regression）。

### v3.9.3（2026-05-18）— #128 housekeeping（client utility 抽出 + resolver dedup）

> 纯 refactor + 一个 latent bug fix，从 v3.9.0 `/simplify` review backlog 结清。抽出 `scripts/_text_similarity.py`（3-way client dedup：normalize / similarity / threshold / retry 常数）+ `scripts/_passport_yaml.py`（2-way migration tool dedup：ruamel.yaml round-trip config）+ 私有 `_resolve_by_doi_then_title` helper（2-way resolver body dedup、§3.4 / §3.5 API surface 不变）。OpenAlex + Crossref 的 throttle 量测从 `time.time`（NTP 不安全）统一改用 `time.monotonic`，与 Semantic Scholar 对齐。5 个 module-level cross-import 都加 dual-path try/except（sibling-first、namespace-package fallback）保持 class identity；额外顺手修了 2 个 latent-broken 的 `import scripts.X` 路径。1505 passed（+23 新测试、0 regression）。#128 §4（OA + CR 平行化）carry-over 到 #138。

### v3.9.2（2026-05-18）— #133 phase boundary 热修

> #133 收尾（hot-fix 层）。长期架构修正以 v3.10 active conductor 在 #134 追踪。添加：CLAUDE.md routing 厘清闸（跨 phase 素材 → 以 a-d 选项厘清，不静默 dispatch）、22 个 single-phase agent 加 prompt 硬 fence（`## Phase Boundary (v3.9.2)`）、16 个 multi-phase / phase-orthogonal / cross-phase-meta agent 刻意不加 fence（诚实 framing：纯 prose placebo 会造成假性 enforce 错觉）、advisory verifier `scripts/check_pipeline_integrity.py` 事后检测 #133 pattern。Behavioral smoke test 含 cross-model spot-check（Opus 4.7 100% / Sonnet + GPT-5.5 ≥75%）。

### v3.9.1（2026-05-18）— #129 + #130 client hardening

> v3.9.0 hot-fix。包 OpenAlex / Crossref response-read 失败为 `*Unavailable`（#129）；`check_claim_audit_consistency` 对非字符串 `manifest_id` 加 guard（#130）。无 spec 变动。

### v3.9.0（2026-05-17）— #102 跨索引三角测量

> #102 收尾。v3.7.3 已完成单索引（Semantic Scholar）污染检测；v3.9.0 延伸至三索引三角测量（S2 + OpenAlex + Crossref），定位为**纯 advisory**。`contamination_signals` 添加两个 optional boolean（`openalex_unmatched`、`crossref_unmatched`）；manual-entry not-rule 对称延伸。Finalizer 加入 4-tier advisory matrix（k=0/1/2/3，计算范围为现有 `*_unmatched` 字段），v3.7.3 的 legacy `CONTAMINATED-UNMATCHED`（k=1/k_max=1、S2-only case）保留。Formatter pass-through allowlist 从 3 条延伸至 9 条；refusal rules 1-10 依 R-L3-2-E 不变。Policy layer（strict modes、hard-block tier、`venue_type` / `triangulation_policy`）依 spec §2.3 延至 v3.10。k=3 marker 为 `CONTAMINATED-TRIANGULATION-UNMATCHED`（描述可观测现象，不推断成因）。添加 3 条 firm rules：R-L3-2-C（k 计算范围为现有字段）、R-L3-2-D（不得 API 推断分类）、R-L3-2-E（refusal list 不扩充；pass-through allowlist 须与 finalizer 同步延伸）。

**迁移：** v3.7.3 corpus — 跑 `python scripts/migrate_literature_corpus_to_v3_9_0.py PATH` 补齐两个新字段。pre-v3.7.3 corpus — **先**跑 `migrate_literature_corpus_to_v3_7_3.py`，再跑 v3.9.0 迁移工具（spec §3.7 daisy-chain；v3.9.0 工具只动已有 `contamination_signals.semantic_scholar_unmatched` 的 entries）。

### v3.8.2（2026-05-17）— #118 uncited audit_tool_failure 补面

> #118 收尾。`ARS_CLAIM_AUDIT=1` 的 uncited 约束判断路径原本碰到 `JudgeInvocationError` 会静默替换成 `{"judgment": "NOT_VIOLATED"}`，把 HIGH-WARN 的 constraint check 在 transient judge 中断时直接吞掉。v3.8.2 改走新的 `uncited_audit_failures[]` aggregate，MED-WARN advisory tier 对应 cited 路径 INV-14 row，但用独立 schema 因为 `claim_audit_result.ref_slug` 必填、uncited 路径没 ref 可绑。#118 issue body 四个 option 最后选了 option 2（新 aggregate）；option 4（re-raise 并 abort 整段 audit）因会严重折损 audit coverage（特别是 judge endpoint 不稳时）被否决。

- **新 `uncited_audit_failure.schema.json` aggregate**（spec §3.6）：每笔 uncited sentence × manifest pair 一个 entry，记录 constraint judge raise `JudgeInvocationError` 的情况。Fault-class enum 与 cited 路径 INV-14 相同（`judge_timeout` / `judge_api_error` / `judge_parse_error` / `cache_corruption` / `retrieval_api_error` / `retrieval_timeout` / `retrieval_network_error`）。`rule_version: D4-c-v1-uaf-v1`。
- **UAF-INV-1..UAF-INV-6 lint**（spec §6 rule 4d）：`finding_id` 唯一性、scoped_manifest_id 跨 aggregate integrity、(M, C) pair integrity（manifest_claim_id non-null 时）、per-(sentence, manifest) dedup、rationale fault_class 前缀、与 `constraint_violations[]` cross-aggregate exclusivity。
- **Finalizer §5 MED-WARN advisory row**：annotation `[CLAIM-AUDIT-TOOL-FAILURE-UNCITED — <fault-class>]`，gate 通过（retry-next-pass 为补救手段）。Formatter REFUSE list 不变 — UAF 是 advisory。
- **Pipeline 集成**（`scripts/claim_audit_pipeline.py`）：line 1211-1224 的 swallow site 移除；`JudgeInvocationError` 改 emit UAF row + `continue` 到下个 (sentence, manifest) pair。`constraint_violations[]` 不会再被假 NOT_VIOLATED 污染。
- **Tests**：添加 18 笔（15 笔 schema/lint TSUAFUncitedAuditFailureInvariants + 3 笔 pipeline integration TP23UncitedJudgeOutageEmitsUAF）。Baseline 694 → 712 tests、0 regression。
- **Agent doc**（`academic-pipeline/agents/claim_ref_alignment_audit_agent.md`）：Output emission 表格添加第七列；Error handling 表格从 3 种 surface 扩成 4 种，添加 uncited 路径 UAF 列。

### v3.8.0（2026-05-16）— L3 Claim-Faithfulness Locator + Audit（配对 milestone）

> v3.7.3 + v3.8 端到端关闭 L3（claim-faithfulness）缺口。v3.7.3 铺 locator 基础建设（每笔引用都带三层 anchor，给未来的审计抓得到原文位置）；v3.8 在这之上加一道审计 pass，判断引用来源是否真的支撑论文的 claim，违反者在 formatter terminal hard gate 直接阻止。本次 release 也合并了从 v3.7.0 后累积的 5 个 audit-trail-shipped feature PR（#104 / #105 / #108 / #111 / #115）。

- **#103 — `claim_ref_alignment_audit_agent`**（v3.8 PR #121）：opt-in（`ARS_CLAIM_AUDIT=1`，默认 OFF）的 Stage 4→5 audit agent。对每笔抽样引用判断与原文段落是否一致，emit `claim_audit_results[]` + `claim_intent_manifests[]` + `claim_drifts[]` + `uncited_assertions[]` + `constraint_violations[]` 五个 aggregate。Finalizer 8 列 matrix 把 HIGH-WARN 类别（CLAIM-NOT-SUPPORTED / NEGATIVE-CONSTRAINT-VIOLATION / FABRICATED-REFERENCE / ANCHORLESS / CONSTRAINT-VIOLATION-UNCITED）导去 formatter REFUSE rules 6-10。Calibration runner 随 release 提供 20 条 gold set（T-C1 FNR<0.15 + FPR<0.10、T-C2 per-class、T-C3 shape integrity）。共 8 轮 dual-track review（R1 codex + Gemini 3.1-pro-preview、R2-R8 在 Gemini quota 用完后改 codex-only）；trajectory R1 4P1+2P2 → R8 0P1+4P2 ship gate。
- **v3.7.3 — Three-Layer Citation Emission + contamination signals**（PR #98）：`synthesis_agent` / `draft_writer_agent` / `report_compiler_agent` 加上 `## Three-Layer Citation Emission (v3.7.3)` H2。每个 `<!--ref:slug-->` 都带 `<!--anchor:<kind>:<value>-->`，`<kind> ∈ {quote, page, section, paragraph, none}`（quote anchor 限 25 字以内、值需 URL-encode）。`pipeline_orchestrator_agent` finalizer 升 5 cell 并加 precedence-zero NO-LOCATOR 检查。`formatter_agent` 在 hard gate 加上对 `[UNVERIFIED CITATION — NO QUOTE OR PAGE LOCATOR]` 的明确 refusal。`literature_corpus_entry.schema.json` 添加 optional 的 `contamination_signals: { preprint_post_llm_inflection, semantic_scholar_unmatched }` 对象，`bibliography_agent` 在 ingest 时计算两个信号。11 轮 review trajectory（Codex×10 + Gemini cross-model×1）收敛 22 个 finding。Spec：`docs/design/2026-05-12-ars-v3.7.3-claim-faithfulness-and-contaminated-source-spec.md`。外部动机：Zhao 等人 arXiv:2605.07723（2026-05）。
- **#108 — AI usage disclosure policy-anchor renderer**（2026-05-14）：在原本的 venue-track renderer 之外，添加 PRISMA-trAIce / ICMJE / Nature / IEEE 四条 policy-anchor disclosure 路径。
- **#111 — `slr_lineage` emission on systematic-review → academic-paper handoff**（2026-05-15）：Schema 9 添加 optional 的 boolean `slr_lineage` 字段。Producer 是 `pipeline_orchestrator_agent`（每次 handoff transition 写入），consumer 是 `disclosure` mode（读到后按 §4.3 G2 invariant 路由到 `--policy-anchor=prisma-trAIce`）。
- **#104 — README motivation：Zhao 等人 corpus-scale 证据锚点**（2026-05-15）：README + `README.zh-TW.md` 动机段以 Zhao 等人 146,932 条幻觉引用的发现作为 v3.7.x 线设计动机的证据锚点。
- **#105 — v3.7.3 contamination_signals 回填迁移工具**（2026-05-15）：`scripts/migrate_literature_corpus_to_v3_7_3.py` 对 v3.7.3 前的 passport 反向计算两个 contamination signals 并补上。
- **#115 — Semantic Scholar client 成熟度**（2026-05-15）：`scripts/semantic_scholar_client.py` 加 1 req/s throttle（检测到 `S2_API_KEY` 时降到 0.1s）、URLError 触发的 outage latch、以及 `reset_outage_latch()` 给跨 passport 的长运行批量清算用。

### v3.7.0（2026-05-05）— Claude Code Plugin 打包

> Plugin 打包升级：ARS 现可在 Claude Code CLI / VS Code / JetBrains 一行装（`/plugin marketplace add Imbad0202/academic-research-skills` + `/plugin install academic-research-skills`）。原本的 `git clone + symlink 到 ~/.claude/skills/` 安装流程不变、继续支持；双轨都是一级公民。

- **Plugin manifest 与 marketplace metadata**（Phase 1，PR #68）：`.claude-plugin/plugin.json` 声明整个 suite（4 个 skill 通过 `skills/` 目录相对 symlink 自动探索）；`.claude-plugin/marketplace.json` 注册 plugin，使单一 GitHub-hosted endpoint 同时提供 marketplace listing 与 plugin 来源。README、`README.zh-TW.md`、`docs/SETUP.md` 都加入双轨安装指引。
- **10 个 slash command** 在 `commands/ars-*.md`（Phase 2.1，PR #69）将 `MODE_REGISTRY.md` 的条目映射到 `/ars-<mode>` 触发。每个 command frontmatter 钉住模型路由：`opus` 给 `full` 与 `revision-coach`（架构与审稿解读深度），`sonnet` 给其他 8 个。任何情境不用 Haiku。
- **3 个 plugin-shipped agent** 在 `agents/*_agent.md`（Phase 2.1，PR #69）以相对 symlink 指向 `deep-research/agents/` 内 v3.6.7 已 hardened 的下游 agent：`synthesis_agent`、`research_architect_agent`、`report_compiler_agent`。底线文件名保留以对齐 `scripts/check_v3_6_7_pattern_protection.py` hard-pin 路径与 INV-3 manifest-confined Clause 1 不变式。Symlink（不复制）维持 single source of truth，避免 v3.6.7 §6 inversion sweep + INV-1/2/3 lint 已关闭的 Pattern C3 攻击面再开。
- **`model: inherit`** 加在这三个 source agent frontmatter 上。选 inherit 而非 pin `sonnet` 是为了让 Opus session 跑 ARS full pipeline 时 agent 仍是 Opus（不被降）。用户的 `~/.claude/hooks/warn-agent-no-model.sh` PreToolUse hook 在派工边界已 gate Haiku，所以 inherit 解析到的是已经没 Haiku 的模型。
- **SessionStart announce hook** 在 `hooks/hooks.json` + `scripts/announce-ars-loaded.sh`（Phase 2.2，PR #70）。Plugin 加载时，hook 把 10 个 slash command、3 个 plugin agent、token 预算指引以 `additionalContext` 注入 LLM 第一轮。`startup` 与 `clear` 拿完整 announce；`resume` 与 `compact` 只拿一行确认，避免每次 resume 都烧 context。Bash 3.2 兼容 — macOS stock `/bin/bash` 直接跑，不需 `brew install bash`。
- **Phase 2.2 范围缩减**：原本规划的 `SubagentStop → run_codex_audit.sh` codex audit hook 在 v3.7.0 被排除，因为 (a) contract gap：SubagentStop payload 没带 stage / deliverable，wrapper 必要参数无法从 hook 推出；(b) invoker 边界：`run_codex_audit.sh` lines 4–7 明禁同 session in-LLM 调用，PostToolUse 在产出 deliverable 的 LLM session 内触发。真正的 audit-hook 集成留到后续版本，等 ARS 有 stage / deliverable propagation contract 再做。详见 `docs/design/2026-04-30-ars-v3.7.0-plugin-packaging-roadmap.md` Update note 2026-05-05（Phase 2.2 scope reduction）。
- **`docs/PERFORMANCE.md` + `.zh-TW.md`** 添加「v3.7.0 Plugin agent 与模型路由」节，说明 inherit 语意与目前 3-agent scope 边界。
- **跨三个 PR 的 codex review chain**：8 轮 inline iterative review + 3 轮 fresh PR-level review，全部在 merge 前收敛到 0 个 P0/P1/P2 finding。Phase 2.2 fresh PR review 抓到一个 P2（`${CLAUDE_PLUGIN_ROOT}` 没 quote，含空白的安装路径会 break）— inline 轮次抓不到，证实「实作 review（inline）」与「contract review（fresh）」分离的价值。
- **没动的东西**：4 个 skill 目录、25 个 mode、agent prompt、schema 文件、lint contract 全不变。Plugin 打包只**添加**顶层接口（`commands/`、`agents/`、`hooks/`、`.claude-plugin/`、`skills/` symlink dir、3 个 source agent frontmatter 加 `model: inherit`）。既有 4.3k clone 安装用户完全不破。

### v3.6.8（2026-05-03）— Generator-Evaluator Contract Gate（v3.6.6 spec ship）

> 命名说明：本次发行交付 **v3.6.6 generator-evaluator contract** spec 与实作。
> v3.6.6 因项目排序晚于 v3.6.7 才落地；design doc 内仍保留 v3.6.6 内部命名作为
> contract gate 版本，suite release 标 v3.6.8 维持 CHANGELOG 单调递增。

- **Schema 13.1**（`shared/sprint_contract.schema.json`）在 Schema 13 之上加两个 `mode` enum 值（`writer_full` + `evaluator_full`）、两个新 optional top-level 字段（`pre_commitment_artifacts` writer-only、`disagreement_handling` evaluator-only）、12 条 `allOf` branch 强制 reviewer- / writer- / evaluator-conditional gate。既有 reviewer contract 在 Schema 13.1 下 byte-equivalent validate（§3.6 zero-touch promise）。
- **两个新 shipped contract template**：`shared/contracts/writer/full.json`（D1–D7、F1/F4/F2/F3/F0）+ `shared/contracts/evaluator/full.json`（D1–D5、F1/F2/F3/F6/F4/F5/F0）。Spec branch 上原是 design-time artefact，本次发行 atomically promote 为 live shipped。
- **`academic-paper full` 模式内加入 two-phase orchestration**：Phase 4 拆成 Phase 4a（writer paper-blind 预先承诺）+ Phase 4b（writer paper-visible 撰稿 + 自评）；Phase 6 拆成 Phase 6a（evaluator paper-blind 预先承诺）+ Phase 6b（evaluator paper-visible 评分 + 决策）。phase-numbered `<phase4a_output>` / `<phase6a_output>` data delimiter 沿用 v3.6.2 reviewer pattern。Lint count summary：writer 3+4 / evaluator 5+5 / reviewer 5+6（reviewer 维持 zero-touch）。
- **`academic-paper` SKILL + agent file 添加 `## v3.6.6 Generator-Evaluator Contract Protocol` 区块**（SKILL.md 101 行 + `draft_writer_agent.md` 47 行 + `peer_reviewer_agent.md` 57 行）。SKILL.md 另加 `## Known limitations` 区块承载 graceful-degradation + cross-session resume v3.6.7+ forward note。
- **Validator 扩充**：`scripts/check_sprint_contract.py` 做 SC-* mode-gating audit（SC-5 + SC-11 reviewer-only；SC-9 跨三个 mode family 各读对应字段）。validator 单元测试从 54 条增加到 71 条（4 positive + 5 schema-branch negative + 2 §3.6 reviewer regression + 6 mode-gating）。
- **Manifest CI lint**：`scripts/check_v3_6_6_ab_manifest.py` 强制 `tests/fixtures/v3.6.6-ab/manifest.yaml` 的 §6.2 manifest schema + §6.5 git-tracked invariant。`.github/workflows/spec-consistency.yml` 把 sprint contract validation loop 扩成同时跑 reviewer + writer + evaluator 三个 template directory，并加入新的 manifest CI lint 步骤。
- **A/B evidence fixture stub**（`tests/fixtures/v3.6.6-ab/`，30 个文件）：manifest + README + 6 paper-A inputs/baseline + 1 paper-C inputs/baseline + Stage 3 reviewer excerpt + 6 codex-judge baseline placeholder。真实 fixture data 在后续 commit populate。

### v3.6.7（2026-04-30）— 下游 agent pattern protection（Step 1+2）

- **三个下游 agent 收紧 13 / 18 个已知幻觉与漂移 pattern**：`synthesis_agent`（A1–A5 叙事侧）、`research_architect_agent` survey-designer 模式（B1–B5 工具侧）、`report_compiler_agent` abstract-only 模式（C1–C3 出版侧）。三个 agent prompt 各自加上 `PATTERN PROTECTION (v3.6.7)` 区块。
- **`shared/references/` 增加四份 reference 文档**：`irb_terminology_glossary.md`、`psychometric_terminology_glossary.md`、`protected_hedging_phrases.md`、`word_count_conventions.md`。protection 条款引用这些文件路径做为 operational contract。
- **跨模型 audit prompt 模板** 在 `shared/templates/codex_audit_multifile_template.md`，含七个 audit dimension 与 `report_compiler_agent` bundle 必跑的三段式 Section 4(f) 检查。任一 sub-check 失败即 P1 finding。
- **静态 lint + 29 条 mutation 测试**：`scripts/check_v3_6_7_pattern_protection.py` 强制 protection 条款存在性与 obligation phrase 形状；`scripts/test_check_v3_6_7_pattern_protection.py` 把 codex review 的 mutation 证据封存为 unit test，未来 lint 退化会在 CI 浮上来。两者都接进 `.github/workflows/spec-consistency.yml`。
- **Codex review 纪录**：七轮 `gpt-5.5` + `xhigh` 跨模型 review 收敛到 0 P1+P2 finding 才 SHIP。Step 6（orchestrator runtime hook）与 Step 8（合成 eval case）走 follow-up PR。

### v3.6.5（2026-04-27）— Material Passport `literature_corpus[]` Consumer 集成

- **Phase 1 两个文献 consumer** 接上：`deep-research/agents/bibliography_agent.md` 与 `academic-paper/agents/literature_strategist_agent.md`。当 passport 带有非空 `literature_corpus[]` 时，两者都走相同的五步 **corpus-first、search-fills-gap** 流程，并遵守相同的四条 Iron Rule（Same criteria / No silent skip / No corpus mutation / Graceful fallback on parse failure）。
- **PRE-SCREENED 可复现区块** 进 Search Strategy 报告：列出已纳入／排除／略过的 corpus entry，附 F3 zero-hit 注解与 F4a–F4f provenance 报告（针对 `obtained_via` / `obtained_at` 部分声明情境）。`final_included = pre_screened_included[] ∪ external_included[]` 维持 neutral — bibliography entry 与 literature matrix row 不挂 provenance 标签。
- **Consumer 协定参考文档** 在 `academic-pipeline/references/literature_corpus_consumers.md`，包含 PRE-SCREENED 模板、BAD/GOOD 范例、四条 Iron Rule 与 per-consumer 读取指示。
- **CI lint** `scripts/check_corpus_consumer_protocol.py` 通过 manifest 驱动的 consumer 清单（`scripts/corpus_consumer_manifest.json`）强制九条协定不变式。
- **Schema 9 caveat 退役**：`shared/handoff_schemas.md` 移除 v3.6.4「Consumer-side integration deferred to v3.6.5+」一行，改成指向 consumer 协定的 backpointer。
- 采 presence-based 启动，不变更 schema、不引入新 env flag。Parse 失败 fallback 到 external-DB-only flow，并 surface `[CORPUS PARSE FAILURE]`。`citation_compliance_agent` 的 corpus 集成延后（目标版本将于 v3.8 后再订）。
- 无破坏性变更，既有用户 adapter 不需修改。

### v3.6.4（2026-04-25）— Material Passport `literature_corpus[]` 输入端口

- **Schema 9 添加 `literature_corpus[]`** 选填字段作为用户文献的输入端口。每笔 entry 符合 `shared/contracts/passport/literature_corpus_entry.schema.json`（CSL-JSON authors / year / title / source_pointer，加上 PRIVATE 选填的 `abstract` / `user_notes`）。
- **语言中性的 adapter 契约** 放在 `academic-pipeline/references/adapters/overview.md`：任何语言写的程序都能读用户自己的 corpus source 并产出符合契约的 `passport.yaml` + `rejection_log.yaml`。Entry-level 错误 fail-soft、adapter-level 错误 fail-loud、输出顺序确定。
- **三个 reference Python adapter** 在 `scripts/adapters/`：`folder_scan.py`（文件系统的 PDF 文件夹）、`zotero.py`（Better BibTeX JSON export）、`obsidian.py`（vault frontmatter）。仅供起点参考；非 reference source 预期用户自行实作 adapter。
- **Rejection log 契约** 在 `shared/contracts/passport/rejection_log.schema.json`，采用封闭 enum 的 categorical reason 值；永远输出（无 rejection 时为空）。
- **CI 把关**：`scripts/check_literature_corpus_schema.py` 验 schemas + adapter examples；`scripts/sync_adapter_docs.py --check` 防 schema→docs drift；新 `pytest.yml` workflow 在 path-filtered 触发跑 `scripts/adapters/tests/`。
- **仅输入端口**：v3.6.4 只定义 schema 与 adapter 契约，consumer 集成到 v3.6.5 才接上 `bibliography_agent` 与 `literature_strategist_agent`。
- 无破坏性变更。

### v3.6.3（2026-04-23）— 选用式 Passport 重置边界

- **Opt-in passport 重置边界**（`ARS_PASSPORT_RESET=1`）。把每个 FULL checkpoint 提升为 context 重置边界。添加 `resume_from_passport=<hash>` 模式，让用户在新的 Claude Code session 单凭 Material Passport ledger 就恢复 pipeline，不重播先前对话。`systematic-review` 模式 flag ON 时，每个 FULL checkpoint 一律强制重置；其他模式视重置为 flag 打开后的强默认。Flag OFF 时 byte-for-byte 维持 pre-v3.6.3 行为。
- Schema 9 添加 append-only `reset_boundary[]` ledger，两种 entry kind（`kind: boundary` + `kind: resume`）。Hash 用 JSON Canonical Form + SHA-256，搭配 canonical placeholder 处理自我参照问题。选填 `pending_decision` 负责 MANDATORY 分支决策。
- 新 CI lint `scripts/check_passport_reset_contract.py`：任何提到 flag 的文件都必须指向权威协议文档。
- 协议文档：`academic-pipeline/references/passport_as_reset_boundary.md`。
- `docs/PERFORMANCE.zh-TW.md` 更新 long-running session 指引。
- 无破坏性变更，flag 默认关闭。

### v3.6.2（2026-04-23）— 审稿 Sprint Contract Hard Gate

v3.6.2 引入 Schema 13 sprint contract 与 hard-gate 编排，强制审稿人在阅读论文前先承诺评分准则。本次只动审稿端（reviewer-only first test case）；writer/evaluator 留到 v3.6.4。详见 CHANGELOG。

- **Schema 13 sprint contract**：`panel_size`、`acceptance_dimensions`、`failure_conditions`（含 `severity` 优先序 + 随 panel 变动的 `cross_reviewer_quantifier`）、`measurement_procedure`、选用 `override_ladder`、限定 `agent_amendments`。验证器：`scripts/check_sprint_contract.py`。
- **两段 hard gate**：审稿人先在「论文内容盲」Phase 1 预先承诺评分计划，Phase 2 才看到论文；Phase 1 输出包在 `<phase1_output>...</phase1_output>` 数据分隔符内，缩窄 self-injection 面。
- **合成者三步机械协议**：建构跨审稿矩阵 → 依 panel-relative quantifier + 认可表达式词汇评估每条 `failure_condition` → 用 `severity` 决优先。禁止操作清单写在 `editorial_synthesizer_agent`。
- **出货两份审稿模板**：`shared/contracts/reviewer/full.json`（panel 5）与 `shared/contracts/reviewer/methodology_focus.json`（panel 2）。`reviewer_re_review`、`reviewer_calibration`、`reviewer_guided` 三个 mode 在 schema enum 中保留，但 v3.6.2 不出 template，继续沿用 pre-v3.6.2 行为；`reviewer_quick` 完全排除于 enum 外。
- `academic-paper-reviewer` SKILL 版本：`1.8.1 → 1.9.0`。`academic-pipeline` SKILL 版本：`3.5.1 → 3.6.2`（suite-version invariant）。Suite 版本升至 `3.6.2`。
- 详见设计稿 [`docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md`](docs/design/2026-04-23-ars-v3.6.2-sprint-contract-design.md) 与协定 [`academic-paper-reviewer/references/sprint_contract_protocol.md`](academic-paper-reviewer/references/sprint_contract_protocol.md)。

### v3.5.1（2026-04-22）— 选用式 Socratic 诚实探测

v3.5.1 添加 Socratic Mentor 的选用式诚实探测（设置 `ARS_SOCRATIC_READING_PROBE=1` 激活）。默认关闭。详见 CHANGELOG。

- **选用式阅读诚实探测**：设置 `ARS_SOCRATIC_READING_PROBE=1` 后，Socratic Mentor 在目标导向 session 中引用特定论文时，触发一次性诚实探测，请用户摘述一段文本。拒绝回答仅记录，不扣分。探测结果写入研究计划摘要，并带入 Stage 6 AI 自我反思报告。不添加 agent，不变更 schema。
- `deep-research` SKILL 版本：`2.9.0 → 2.9.1`。`academic-pipeline` SKILL 版本：`3.5.0 → 3.5.1`。Suite 版本升至 `3.5.1`。

### v3.5.0（2026-04-21）— 协作深度观察员（Collaboration Depth Observer）

- **添加 agent**：`academic-pipeline` 添加 `collaboration_depth_agent`（Agent Team 从 3 成长为 4）。每个 FULL/SLIM checkpoint 与 pipeline 完成后（Stage 6 之后）触发，依 4 维度 rubric 对用户与 AI 的协作模式评分。**纯观察建议，永不阻挡流程**。MANDATORY checkpoints（Stages 2.5 / 4.5 的学术诚信检查）**不**触发 observer，学术诚信闸门完全保留。
- **添加 rubric**：[`shared/collaboration_depth_rubric.md`](shared/collaboration_depth_rubric.md) v1.0。四个维度：Delegation Intensity、Cognitive Vigilance、Cognitive Reallocation、Zone Classification（Zone 1 / Zone 2 / Zone 3）。理论依据为 Wang, S., & Zhang, H. (2026). "Pedagogical partnerships with generative AI in higher education: how dual cognitive pathways paradoxically enable transformative learning." *International Journal of Educational Technology in Higher Education*, 23:11. DOI [10.1186/s41239-026-00585-x](https://doi.org/10.1186/s41239-026-00585-x)。
- **Cross-model 分歧显式标注，不默默平均**：当 `ARS_CROSS_MODEL` 设置时，observer 于两个模型同时运行；若任一维度分差 > 2 分即标记为 `cross_model_divergence`。另提供 `ARS_CROSS_MODEL_SAMPLE_INTERVAL` 调控成本。
- **Short-stage guard**：stage 内用户 turn < 5 时注入静态 `insufficient_evidence` 区块，不派发全模型 observer call。
- **反谄媚规范**：分数 ≥ 7 必须附具体对话 turn 引用；Zone 3 触发 re-audit；禁止鼓励性语言。
- `academic-pipeline` SKILL 版本：`3.3.0 → 3.4.0`。Suite 版本升至 `3.5.0`。添加 lint `scripts/check_collaboration_depth_rubric.py` 加 10 个测试。

### v3.4.0（2026-04-20）— Compliance Agent + Schema 12

- **Compliance Agent（shared）**：单一 mode-aware agent，同时跑 PRISMA-trAIce 17 项（限 SR mode）+ RAISE 四原则 + 8-role matrix。挂载既有 Stage 2.5 / 4.5 Integrity Gate；tier-based block（Mandatory → block、HR → warn、R/O → info）。非 SR 入口只跑原则、warn-only。
- **Schema 12 compliance_report** 附加到 Material Passport 的 `compliance_history[]`（append-only）。
- **三回合 user-override 阶梯**，自动注入 `disclosure_addendum` 到 manuscript。无法规避披露要求。
- **Calibration 以透明公布取代硬门槛**，与 `task_type: open-ended` 自洽。
- **Upstream freshness CI** 检测 PRISMA-trAIce 上游漂移（non-blocking）。
- **长时间 session 文档**：Material Passport 作为跨 session 续跑机制。

### v3.3.6 (2026-04-15) — README 精简 + ARCHITECTURE 文档

- 添加 `docs/ARCHITECTURE.md` 作为 pipeline 结构的单一来源（流程、矩阵、数据访问、依赖图、质量闸门、模式）。通过 PR #18 合并入 main。
- 添加 `docs/SETUP.md` / `docs/SETUP.zh-TW.md`（前置需求、API key、Pandoc/tectonic、跨模型验证、四种安装方式），以及 `docs/PERFORMANCE.md` / `docs/PERFORMANCE.zh-TW.md`（token 预算、建议 Claude Code 设置）。README 以链接取代内嵌。
- 精简 README：移除 ASCII pipeline 图与 16 项 key-feature 清单（已被 ARCHITECTURE.md 取代）；Skill 详细信息维持版本号锚点，读者跳到 ARCHITECTURE.md §3 看各 agent 名单。
- 注记：没有任何 skill 的功能变动，纯文档重构。suite version 升级至 `3.3.6`。

### v3.3.5 (2026-04-15)
- 添加 `benchmark_report.schema.json` 与 Material Passport 的 `repro_lock` 可选区块。两者都附 pattern 文档、lint、范例。首次引入正式的 Python 开发依赖清单（`requirements-dev.txt`）。

### v3.3.4 (2026-04-15) — README 更新纪录同步修补

- 同步 `README.md` 与 `README.zh-TW.md` 内嵌的 changelog 区块，补上原本缺漏的 `v3.3.3` 与 `v3.3.2` 发版摘要。
- 扩充 `scripts/check_spec_consistency.py`，之后 README changelog 如果再次漂移，CI 会直接 fail。
### v3.3.3 (2026-04-15) — Release Prep + Lint 强化

- 强化 SKILL frontmatter lint：缺少 closing `---` fence 时，现在会明确报错，不再把整份文件后半段误当成合法 YAML。
- frontmatter 若可被 YAML 解析但不是 mapping，现在会回报可读错误，而不是直接 crash。
- 修正中英文 README 中 post-publication audit showcase 链接失效的问题。
- 在 spec consistency check 补上 README 相对链接验证，之后 dead link 会直接让 CI fail。
- 将 DOCX 输出契约在文档中统一：直接产出 `.docx` 依赖 Pandoc，否则回退为 Markdown + 转换说明。
- 完成 `v3.3.3` 发版准备：suite version bump，`academic-paper` -> v3.0.2，`academic-pipeline` -> v3.2.2。

### v3.3.2 (2026-04-15) — Data Access Level + Task Type Metadata

- 所有顶层 `SKILL.md` 添加 `metadata.data_access_level`，并以 `raw`、`redacted`、`verified_only` 为强制词汇。
- 所有顶层 `SKILL.md` 添加 `metadata.task_type`，并以 `open-ended`、`outcome-gradable` 为强制词汇。
- 为两个 metadata 字段添加 lint script 与单元测试，并接到 GitHub Actions spec consistency workflow。
- 添加 `shared/ground_truth_isolation_pattern.md`，并在 `shared/handoff_schemas.md` 中补上对新词汇的说明入口。

### v3.3.1 (2026-04-14) — 规格一致性修补

- 同步 README、`.claude/CLAUDE.md`、`MODE_REGISTRY.md` 与各 `SKILL.md` 的 mode 数量与公开版本标注。
- 修正跨模型叙述：目前已实作的是完整性抽样核查与独立 DA critique；同行评审第六位 reviewer 仍在规划中。
- 厘清 adaptive checkpoint 语意：SLIM checkpoint 仍然必须等待用户明确确认。
- 再次明确化 Stage 2.5 与 Stage 4.5 学术诚信关卡不可跳过。
- 添加轻量 spec consistency 检查与 GitHub Actions workflow，避免后续再发生文档漂移。

### v3.3 (2026-04-09) — PaperOrchestra 启发的强化

集成 [PaperOrchestra](https://arxiv.org/abs/2604.05018)（Song, Song, Pfister & Yoon, 2026, Google）的技术。

- **Semantic Scholar API 验证** — Tier 0 程序化引用存在性核查。Levenshtein >= 0.70 标题比对、DOI 不符检测、S2 ID 去重。API 不可用时优雅降级。
- **反泄露协议** — 知识隔离指令优先使用 session 内材料，缺少的内容标记 `[MATERIAL GAP]` 而非用 LLM 记忆填补。降低 Mode 5/6 失败风险。
- **VLM 图表验证**（可选）— 用视觉模型闭环检查生成图表。10 项检核清单，最多 2 轮修正。
- **分数轨迹协议** — 跨修订轮次的逐维度评分差异追踪（7 个维度）。检测退步（delta < -3）触发强制 checkpoint。
- **Stage 2 并行化** — 可视化与论证建构可在大纲完成后并行运行。
- 新版本：deep-research v2.8、academic-paper v3.0、academic-pipeline v3.2

### v3.2 (2026-04-09) — Lu 2026 Nature 集成

集成 Lu 等人（2026，*Nature* 651:914-919）的研究洞见——第一个通过盲审的端到端全自动 AI 研究系统。

- **7 类 AI 研究失败模式检查清单** — 在 Stage 2.5/4.5 阻断管线：检测实现错误、幻觉实验结果、取巧特征依赖、错误包装为发现、方法伪造、框架锁定。扩充现有 5 类引用幻觉分类。
- **Reviewer 校准模式**（academic-paper-reviewer v1.8）— opt-in 的 FNR/FPR/balanced accuracy 测量，用户提供 gold set。5 次集成、跨模型默认打开、session 内强制附加信心披露。
- **AI 使用声明模式**（academic-paper v2.9）— 针对特定期刊/会议的 AI 使用声明生成器。v1 涵盖 ICLR、NeurIPS、Nature、Science、ACL、EMNLP。
- **提前停止机制**（academic-pipeline v3.1）— 收敛检查 + pipeline 开始时的 token 预算透明化。
- **忠实度-原创性模式光谱** — 按 Lu 2026 Fig 1c 分类所有 3 个 skill 的模式。
- 新版本：academic-paper v2.9、academic-paper-reviewer v1.8、academic-pipeline v3.1

### v3.1.1 (2026-04-09) — 信息系统 Senior Scholars' Basket of 11

外部贡献：[@mchesbro1](https://github.com/mchesbro1) 最初提出并撰写了 IS Basket of 8 期刊清单（[Issue #5](https://github.com/Imbad0202/academic-research-skills/issues/5)）；[@cloudenochcsis](https://github.com/cloudenochcsis) 将其扩充为完整的 Senior Scholars' Basket of 11（[Issue #7](https://github.com/Imbad0202/academic-research-skills/issues/7)、[PR #8](https://github.com/Imbad0202/academic-research-skills/pull/8)）。更新 `academic-paper-reviewer/references/top_journals_by_field.md` 第 7 节，补上 *Decision Support Systems*、*Information & Management*、*Information and Organization*。数据源：[AIS Senior Scholars' List of Premier Journals](https://aisnet.org/research/seniorscholarsbasket/)。

### v3.1 (2026-04-06) — 抗 Context Rot + 认知框架 + 精简尺寸

灵感来自 [aspi6246/Claude-Code-Skills-for-Academics](https://github.com/aspi6246/Claude-Code-Skills-for-Academics)。

**Wave 1：抗 Context Rot 锚定**
- 4 个 skill 共 29 条 Anti-Patterns（每个 7-8 条，表格含「为何失败」+「正确行为」）
- 22 个 IRON RULE 标记，确保长对话中关键规则不被遗忘
- 审查者只读约束（reviewer 不可修改论文原稿）

**Wave 2：追溯性 + 认知框架 + 中途强化**
- R&R 追溯矩阵（Schema 11）：Re-Review 添加「作者主张」+「已验证？」字段，独立核实修订主张
- 3 个认知框架 reference 文件，教 agent「如何思考」而非只是「做什么」：
  - 论证与推理框架（Toulmin 模型、Bradford Hill 因果推理、最佳解释推论、认知状态分类）
  - 评审质量思维框架（三镜头法、常见审查陷阱、校准问题）
  - 写作判断力框架（清晰度测试、读者旅程、学科语态、修订决策矩阵）
- 中途强化机制：每次 stage 转换注入对应 IRON RULE + Anti-Pattern 提醒
- FULL checkpoint 前的 5 题自我检查（引用完整性、谄媚让步、质量轨迹、范围纪律、完整性）

**Wave 3：精简 Skill 尺寸**
- SKILL.md 总大小从 142KB 降至 85KB（-40%），详细协议移至 `references/` 按需加载
- 添加 ~15 个 reference 文件（re-review protocol、guided mode、systematic review、process summary 等）
- 所有 IRON RULE 保留在 SKILL.md；详细内容按需加载
- 新版本：deep-research v2.7、academic-paper v2.8、academic-paper-reviewer v1.7、academic-pipeline v3.0

### v3.0 (2026-04-03) — 反谄媚 + 意图检测 + 跨模型验证 + AI 自我反思
- **魔鬼代言人让步门槛**（deep-research + academic-paper-reviewer）：反驳必须评分 1-5。≥4 才允许让步。不允许连续让步。让步率追踪。框架锁定检测。
- **攻击强度保持**（academic-paper-reviewer）：DA 不因被反驳而软化。反驳评估协议含偏移检测。
- **意图检测层**（deep-research socratic）：检测探索型 vs. 目标型。探索模式停用自动收敛，最大轮数提升至 60。每 5 轮重新评估。
- **对话健康度指针**（deep-research socratic）：每 5 轮后台自检，检测持续同意、回避冲突、过早收敛。检测到模式时自动注入挑战性问题。
- **跨模型验证协议**（shared，可选）：用 GPT-5.4 Pro 或 Gemini 3.1 Pro 做学术诚信验证 30% 抽样跨模型检查与独立 DA critique。同行评审第六位 reviewer 仍在规划中，尚未实作。设置 `ARS_CROSS_MODEL` 环境变量激活——未设置时零开销。完整设置指南见 `shared/cross_model_verification.md`。
- **AI 自我反思报告**（academic-pipeline Stage 6）：Pipeline 结束后 AI 行为自评——DA 让步率、健康警报、谄媚风险评级（LOW/MEDIUM/HIGH）、框架锁定事件。
- 来源：四轮辩证实验中发现 DA 让步太快、苏格拉底模式过早收敛、整个辩论锁定在人类设置的框架中。
- 版本：deep-research v2.5、academic-paper-reviewer v1.5、academic-pipeline v2.8

### v2.9.1 (2026-04-03) — Skill Metadata
- 为 4 个 SKILL.md 加入 `status: active` 和 `related_skills` 交叉引用
- 支持 skill 探索工具及跨技能导航

### v2.9 (2026-03-27) — 风格校准 + 写作质量检查
- **风格校准**（academic-paper intake Step 10，可选）：提供 3+ 篇过去论文，pipeline 会学习你的写作风格 — 句子节奏、词汇偏好、引用集成方式。写作时作为软性指引；学科规范永远优先。优先级系统：学科规范（硬性）> 期刊惯例（强）> 个人风格（软性）。见 `shared/style_calibration_protocol.md`
- **写作质量检查**（`academic-paper/references/writing_quality_check.md`）：写作质量 checklist，于初稿自我审查时套用。5 大类：AI 高频词汇警告（25 个词）、标点模式控制（em dash ≤3）、开头废话检测、结构模式警告（三项枚举强迫症、均匀段落、同义词循环）、句子长度变化检查。这是好写作规则 — 不是逃避检测
- **Style Profile** 通过 academic-pipeline Material Passport 携带（`shared/handoff_schemas.md` Schema 10）
- **deep-research** report compiler 也可选地消费这两个功能
- 版本：academic-paper v2.5、deep-research v2.4、academic-pipeline v2.7

### v2.8 (2026-03-22) — SCR Loop Phase 1：State-Challenge-Reflect 反思机制
- **Socratic Mentor Agent**（deep-research + academic-paper）：集成 SCR（表态-挑战-反思）协议
  - **Commitment Gate**：在每个层级/章节转换前收集用户预测，再呈现数据
  - **Certainty-Triggered Contradiction**：检测高信心语句（「显然」「毫无疑问」），自动引入反面观点
  - **Adaptive Intensity**：追踪 commitment 准确率，动态调整挑战频率
  - **Self-Calibration Signal (S5)**：新收敛信号，追踪用户在对话中是否展现自我校准能力
  - **SCR Switch**：用户可随时说「跳过预测」关闭 SCR，或「恢复预测」重新打开，苏格拉底式提问不受影响
- `deep-research/references/socratic_questioning_framework.md`：添加 SCR Overlay Protocol，映射 SCR 三阶段到苏格拉底功能
- 添加 `CHANGELOG.md`

### v2.7 (2026-03-09) — 学术诚信验证 v2.0：反幻觉全面改版
- **integrity_verification_agent v2.0**：Anti-Hallucination Mandate（禁止靠 AI 记忆验证）、消除灰色地带分类（仅 VERIFIED/NOT_FOUND/MISMATCH）、强制 WebSearch audit trail、Stage 4.5 独立全面验证、Gray-Zone Prevention Rule
- **已知引用幻觉 Pattern**：5 类分类法（TF/PAC/IH/PH/SH，来自 GPTZero × NeurIPS 2025 研究）、5 种复合欺骗模式、实战案例、文献统计
- **出版后审计**：对全部 68 篇引用做 WebSearch 逐一验证，发现 21 篇有问题（31% 错误率），证明外部核查的必要性
- **论文修正**：移除 4 篇捏造引用、修正 6 篇作者错误、修正 7 篇书目细节、修正 2 篇格式问题

### v2.6.2 (2026-03-09) — 意图匹配模式启动
- **deep-research**：苏格拉底模式改为**意图匹配**启动，取代关键字比对。支持任何语言 — 检测含义（如「用户想要引导式思考」）而非比对特定字符串。
- **academic-paper**：Plan 模式改为**意图匹配**启动。检测意图信号如「用户不确定如何开始」「用户想要逐步引导」，不限语言。
- 两个模式添加**默认规则**：当意图模糊时，偏好 `socratic`/`plan` 而非 `full` — 先引导比较安全。
- 双层架构：Layer 1（skill 启动）用双语关键字提高匹配信心；Layer 2（mode 路由）用语言无关的意图信号。

### v2.6.1 (2026-03-09) — 双语触发关键字
- **deep-research**：添加繁体中文触发关键字，涵盖一般启动和苏格拉底模式。
- **academic-paper**：添加繁体中文触发关键字及 Plan Mode 触发区块。
- 两份 mode selection guide 加入双语范例及中文专属误选情境。

### v2.6 / v2.4 / v1.4 (2026-03-08) — 15+ 项改进
- **deep-research v2.3**：添加系统性文献回顾 / PRISMA 模式（第 7 模式）；3 个新 agent（risk_of_bias、meta_analysis、monitoring）；PRISMA 协议/报告模板；苏格拉底收敛准则（4 信号 + 自动结束）；快速模式选择指南
- **academic-paper v2.4**：2 个新 agent（visualization、revision_coach）；修订追踪模板含 4 种状态；引用格式转换（APA↔Chicago↔MLA↔IEEE↔Vancouver）；统计可视化标准；苏格拉底收敛准则；修订复原范例；**LaTeX 输出强化** — 强制 `apa7` document class、`ragged2e` + `etoolbox` 文本对齐修正、表格栏宽公式、双语摘要置中、标准字体集（Times New Roman + 思源宋体 VF + Courier New）、仅 tectonic 编译 PDF
- **academic-paper-reviewer v1.4**：0-100 质量量表含行为指针；决策对照（≥80 接受、65-79 小修、50-64 大修、<50 退稿）；快速模式选择指南
- **academic-pipeline v2.6**：自适应 checkpoint（FULL/SLIM/MANDATORY）；Phase E 主张验证；材料护照（Material Passport）支持中途进入；跨 skill 模式顾问（14 情境）；团队协作协议；强化衔接 schema（9 个含验证规则）；学术诚信审查失败复原范例

### v2.4 / v1.3 (2026-03-08)
- **academic-pipeline v2.4**：添加 Stage 6 过程记录 — 自动生成结构化论文创建过程记录（MD → LaTeX → PDF，中英双语）；必含最后一章：**协作质量评估**，6 个维度各计 1–100 分（方向设置、智识贡献、质量把关、迭代纪律、委派效率、后设学习），含诚实回馈与改进建议；pipeline 从 9 阶段扩展为 10 阶段

### v2.3 / v1.3 (2026-03-08)
- **academic-pipeline v2.3**：Stage 5 定稿阶段现在会先询问格式风格（APA 7.0 / Chicago / IEEE）；PDF 必须从 LaTeX 经 `tectonic` 编译（禁止 HTML-to-PDF）；APA 7.0 使用 `apa7` document class（`man` 模式）+ XeCJK 支持中英双语；字体：Times New Roman + 思源宋体 VF + Courier New

### v2.2 / v1.3 (2025-03-05)
- **跨 Agent 质量对齐**：统一定义（同行评审、时效规则、CRITICAL 严重度、来源分级）横跨所有 agent
- **deep-research v2.2**：synthesis 反模式、苏格拉底自动结束条件、DOI+WebSearch 验证、强化伦理与学术诚信审查、模式转换矩阵
- **academic-paper v2.2**：4 级论证强度评分、抄袭筛查、2 个新失败路径（F11 退稿复活、F12 研讨会转期刊）、Plan→Full 模式转换
- **academic-paper-reviewer v1.3**：DA vs R3 角色边界、CRITICAL 判定标准、共识分类（4/3/SPLIT/DA-CRITICAL）、信心分数加权、亚洲与区域期刊参考
- **academic-pipeline v2.2**：checkpoint 确认语意、模式切换矩阵、技能失败降级策略、状态所有权协议、素材版本控制

### v2.0.1 (2026-03)
- **精简 4 个 SKILL.md**（-371 行, -16.5%）：移除跨 skill 重复、内嵌模板改为文件引用、冗余路由表、重复模式选择区块
- 修复 academic-paper 与 academic-pipeline 之间修订循环上限的矛盾

### v2.0 (2026-02)
- **academic-pipeline v2.0**：5→9 阶段、强制学术诚信验证、两阶段审查、苏格拉底修订指导、可复现性保证
- **academic-paper-reviewer v1.1**：+魔鬼代言人审查者（第 7 agent）、+re-review 模式（验收）、+审后苏格拉底指导
- 添加 agent：`integrity_verification_agent` — 100% 引用/数据验证，含审计轨迹
- 添加 agent：`devils_advocate_reviewer_agent` — 8 维度论点挑战
- 输出顺序：MD → Pandoc 可用时产出 DOCX（否则提供说明）→ 询问 LaTeX → 确认 → PDF

### v1.0 (2026-02)
- 初版发布
- deep-research v2.0（10 agents、6 模式含 socratic）
- academic-paper v2.0（10 agents、8 模式含 plan）
- academic-paper-reviewer v1.0（6 agents、4 模式含 guided）
- academic-pipeline v1.0（调度器）
