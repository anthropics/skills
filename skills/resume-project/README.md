# resume-project

**A Claude Code skill that transforms engineering project experience into industrial-strength resume bullets with architectural depth.**

Most engineers describe *what* they built. This skill forces you to describe *why* you made each architectural decision, *what was broken before* your solution existed, and *what measurably improved* after. The result reads like a Staff Engineer wrote it.

---

## Two input modes

**Mode A — Code repository**
Point it at a codebase. The skill scans the architecture, maps data flows (Producer → Sidecar → Consumer), detects scale signals, then interviews you to fill in business context and quantified results.

**Mode B — Paste a description**
Already have bullet drafts? Paste them in. The skill audits for the 3 weakest points and asks targeted questions before rewriting.

---

## Core mechanism: Interceptor

Before generating any bullet, the Interceptor blocks if any of these are missing:

- **Before state** — what was broken or missing before your solution?
- **Decision rationale** — why this approach and not the alternative?
- **Quantified result** — what actually improved, and by how much?

No placeholders, no estimates — only what you can confirm.

---

## Output format

Bilingual (Chinese + English), with:

- `[Topic labels]` on each bullet
- **Decision sentences**: *"Abandoned X (reason) in favor of Y, via mechanism Z, achieving result W"*
- Nested sub-bullets for multi-tier systems
- `[TBD]` placeholders for unconfirmed metrics — a reminder to fill before submitting

Results accumulate in `~/.claude/resume-library.md` across sessions.

---

## Installation

```bash
# From ClawHub
npx clawhub install resume-project

# From GitHub
claude skill install https://github.com/wwaguai/resume-project-skill
```

## Usage

```
/resume-project
```

Then either paste a project description or provide a path to a codebase.

---

## Example transformation

**Before (typical):**
> Responsible for the search module, implemented full-text search using Elasticsearch with sharding.

**After (with this skill):**
> **[Distributed Cache Architecture]** Abandoned per-request DB queries (latency unbounded under write contention) in favor of a write-through cache layer with TTL-based invalidation, eliminating hot-path read amplification at peak load — reducing P99 from [TBD]ms to [TBD]ms with zero consistency incidents over [TBD] months.

---

## License

MIT

---

---

# resume-project（中文说明）

**一个 Claude Code Skill，将工程项目经历转化为具备工业级冲击力的简历描述。**

大多数工程师写简历只描述"做了什么"。这个 Skill 会逼着你回答：当时为什么做这个架构决策？改动之前系统是什么状态？改完之后量化提升了多少？最终产出读起来像 Staff Engineer 写的。

---

## 两种输入模式

**模式 A — 代码仓库**
指向一个代码库，Skill 自动扫描架构拓扑、识别数据流向（Producer → Sidecar → Consumer）、检测规模信号，然后通过追问补全业务背景和量化数据。

**模式 B — 直接粘贴描述**
已经有草稿？直接粘贴进来，Skill 识别出说服力最弱的 3 个点，针对性追问后再改写。

---

## 核心机制：Interceptor（拦截器）

每一条 bullet 生成前，Interceptor 会强制检查以下三项，缺一不过：

- **改之前** — 你的方案出现之前，系统是什么状态？
- **决策依据** — 为什么选这个方案，而不是其他方案？
- **量化结果** — 具体改善了什么，改善了多少？

不允许估算，不允许占位——只写你能确认的数据。

---

## 输出格式

中英文双语输出，包含：

- 每条 bullet 前的 `[主题标签]`
- **决策句式**：*"放弃了 X（原因），引入 Y，通过 Z 机制，实现 W 结果"*
- 多层级系统展开为嵌套子列表
- 未确认数据用 `[待确认]` 占位，提醒投递前补充

分析结果自动累积保存至 `~/.claude/resume-library.md`。

---

## 安装

```bash
# 从 ClawHub 安装
npx clawhub install resume-project

# 从 GitHub 安装
claude skill install https://github.com/wwaguai/resume-project-skill
```

## 使用方法

```
/resume-project
```

然后粘贴项目描述，或者提供代码库路径即可。

---

## 改写示例

**改之前（典型简历写法）：**
> 负责搜索模块开发，使用 Elasticsearch 实现全文检索，支持分片。

**改之后（使用本 Skill）：**
> **[分布式缓存架构]** 放弃了写竞争下延迟不可控的逐请求 DB 查询方案，引入带 TTL 失效的 write-through 缓存层，消除高峰期热路径读放大——P99 从 [待确认]ms 降至 [待确认]ms，[待确认] 个月内零一致性事故。
