---
name: doc-init
description: 项目文档体系初始化。先检查并修复全局 AI 指令文件中的「项目文档管理」规范，再通过人机协同 Intake、业务域扫描、隐藏机制识别、可选数据库证据挖掘和必要的运行验证，建立 AI Coding Agent 可用的领域知识库与公共 Guide 知识网络。在无文档体系的新项目、或全局规范缺失时使用。Use when entering a project with no doc structure, or when the global AGENTS.md lacks the doc-governance standard.
---

# 文档体系初始化（doc-init）

执行分两个阶段：**先修复全局规范，再初始化项目文档**。

`<DOC_INIT_DIR>` = 当前 `SKILL.md` 所在目录（动态解析，禁止写死绝对路径）。

---

## 内置脚本速查

优先用内置脚本完成机械动作，把模型上下文留给业务判断：

| 脚本 | 用途 |
|------|------|
| `scripts/project_inventory.py` | 扫描语言栈、构建文件、子模块、文档、配置、入口候选；只产出候选事实，不决定业务域 |
| `scripts/doc_coverage.py` | 覆盖度闸门：代码功能入口 vs 地图锚点匹配 + 指纹基线，退出码 `COMPLETE(0)/STALE(2)/NEEDS_INIT(3)` |
| `scripts/upsert_agents_nav.py` | 幂等新增或更新根 `AGENTS.md` 文档导航条目 |
| `scripts/doc_nav_lint.py` | 检查根 `AGENTS.md`、`CLAUDE.md`、`docs/` 导航一致性 |
| `scripts/db_miner.py` | 数据库 catalog 和领域级表/字段证据挖掘 |
| `scripts/git_history_miner.py` | 轻量 Git 历史弱信号挖掘（热点、历史叫法、Q&A 线索）|
| `scripts/depth_scanner.py` | 深度知识提取：状态机、并发、幂等、事件、实体字段等模式 |
| `scripts/insert_doc_governance.py` | 版本检测 + 自动插入/升级全局 AI 指令文件中的「项目文档管理」章节 |

脚本输出是证据和防呆，不替代模型对业务边界、主称谓、KB/Guide 粒度和落档内容的判断。

---

## 阶段一：校验并修复全局 AI 指令文件

### Step 1 — 定位全局 AI 指令文件真身

探测以下文件，软链则跟到真身（`readlink -f`），对真身路径去重后得到待处理文件列表：

1. `~/.claude/CLAUDE.md`
2. `~/.codex/AGENTS.md`
3. `~/.codex/instructions.md`
4. `~/.config/opencode/AGENTS.md`

若均不存在，报告并询问用户路径后继续。

**禁止**把当前项目的 `AGENTS.md` 传给 `insert_doc_governance.py`——只处理上方列出的全局文件。

### Step 2 — 脚本校验并自动插入/升级

对每个真身文件运行：

```bash
python3 <DOC_INIT_DIR>/scripts/insert_doc_governance.py "<真身路径>"
```

| 输出前缀 | 含义 | 后续动作 |
|----------|------|----------|
| `[跳过]` | 已是最新版本 | 直接进 Step 3 |
| `[新增]` / `[完成]` | 首次插入成功 | 进 Step 3 |
| `[升级]` / `[完成]` | 旧版已替换 | 清理散落旧规则，再进 Step 3 |

**仅在 `[升级]` 时需要模型额外清理**（扫描并删除）：
- `## AGENTS.md 优先级` 整个章节
- `知识持久化` 章节下的 `### 检索在先、存储在后` 小节
- 其他以「文档放置」「文档索引」「AGENTS.md 导航」「docs/ 目录」为主题的散落段落

保留：`知识持久化` 章节的其余内容（禁用 memory 的规则）及所有与文档无关的章节。

### Step 3 — 输出阶段一报告

说明处理了哪些文件、每个文件的脚本输出结果，以及清理了哪些散落旧内容（若有）。

---

## 阶段二：初始化当前项目文档体系

**阶段二开始前先读取** `references/knowledge-network-design.md`，用它控制文档粒度、命名、KB/Guide 边界和预算受限行为。

### Step 6 — 判断是否需要初始化 / 续接 / 复核

完成判定的唯一锚点是根 `AGENTS.md` 的 `## 领域地图（doc-init）` 段：

1. **有地图段** → 读地图段，进入 Step 6.5 覆盖度复核，**禁止**因"已存在/全是已生成/无 backlog"就直接退出。
2. **无地图段** → 无论 `docs/` 是否非空，一律判为**初始化未完成**，进入 Step 7/8；建地图时复用已有文档，不重写。

若根目录已有 `AGENTS.md`，可先运行辅助判断（仅供参考）：

```bash
python3 <DOC_INIT_DIR>/scripts/doc_nav_lint.py --root .
```

### Step 6.5 — 覆盖度复核（地图存在时强制）

收工与否由 `doc_coverage.py` 退出码决定，禁止模型自陈"覆盖得差不多"：

```bash
python3 <DOC_INIT_DIR>/scripts/project_inventory.py --root . --output .doc-init-project-inventory.json
python3 <DOC_INIT_DIR>/scripts/doc_coverage.py --root . --inventory .doc-init-project-inventory.json
```

| 退出码 | 含义 | 动作 |
|--------|------|------|
| `3 NEEDS_INIT` | 实际没有地图段 | 回 Step 6 判定 2，走完整初始化 |
| `0 COMPLETE` | 锚点覆盖、无明显增长 | 把脚本建议的基线戳写回地图段，告知用户「文档体系覆盖当前代码，增量补充用 doc-update」后退出 |
| `2 STALE` | 覆盖不足/功能区新增/代码大涨/无基线戳 | **不算完成**，进入第三步 |

**STALE 时的后续**（细则见 `references/scan-and-boundary-report.md` 「覆盖度复核」一节）：
1. 未覆盖功能区 → 经产品北极星过滤（Step 7a）：真实功能加入地图；死代码/实现漂移列待确认发现。
2. 代码量大涨/无基线戳 → 对 `已生成` 领域做漂移点检；明显漂移降级为 `本次深写`，轻微差异转 doc-update。
3. 回 Step 7a → Step 8/9 深写本批；已确认仍准确的 `已生成` 领域不重扫。

阈值默认：`--min-coverage 0.85`、`--max-uncovered-area-entries 3`、`--max-growth-pct 0.25`。入口稀疏的纯库/脚手架被判 STALE 时人工读未覆盖列表确认，不调低阈值绕过闸门。

### Step 7 — 产品北极星先行 + 人机协同 Intake

读取 `references/human-intake.md`。

**Step 7a：先确立产品北极星**——按 `human-intake.md`「产品北极星先行」流程确立（① 项目 AGENTS.md 产品指针 → ② PRD/路线图 → ③ 征询用户 → ④ 硬卡停下）。

**确认真相后就地修正冲突文档**：任何阶段确立的真相若与 `docs/` 已有文档相冲突，必须在当次会话内改正，不允许同时留两份矛盾结论。裁定、防拉锯、传播规则详见 `references/conflict-resolution.md`。

**Step 7b：人机协同 Intake**。除非用户明确禁止提问，做轻量 Intake（资料入口、业务叫法、运行验证入口、老手经验）。用户禁止提问时跳过，在自评中标注「缺少用户经验输入」。

**Step 7c：跨项目技术规范引用检查**。读全局 AI 指令文件真身（Step 1 已定位），看其中是否声明了「跨项目技术规范文档」的位置约定（按语言/技术栈组织的公共规范目录，不同用户的声明位置和目录名可能不同，不能假设固定路径，找不到声明就跳过本步、不臆造路径）。声明存在时：
1. 按当前项目主语言/技术栈，在声明的位置下找匹配的规范文档。
2. 找到且项目根 `AGENTS.md` 尚未引用 → 在文件顶部（产品简介之后、正文章节之前）补一行引用，格式仿照声明位置里的既有用法（如 `通用工程规范：[Go 规范](<相对路径>/go.md)`），相对路径按当前项目实际目录层级调整。
3. 项目涉及多个技术栈（如后端 + 移动端）→ 每个匹配到的规范文档各占一个链接，同一行用 `·` 分隔。

### Step 8 — 扫描项目并输出完整领域地图与知识边界报告

读取 `references/scan-and-boundary-report.md`。

**交付物顺序：产品北极星摘要 → 完整领域地图 → per-域详细报告**。

**建地图前先盘点已有文档**：交叉比对 `docs/` 现有文档和根 `AGENTS.md` 已有导航条目，已覆盖领域直接标「已生成（复用现有）」，不重写；仅在内容明显过期或与当前代码/产品真相冲突时才更新。

**业务域划分硬约束**（详见 `references/knowledge-network-design.md` 「业务域 ≠ 代码模块」一节）：

- 领域 = 业务概念，不是子模块/目录名
- 一份 KB 涵盖该业务域在各模块（配置/执行/实体/接口）的全部入口
- 同一模块内有多个独立业务对象时，必须拆成独立 KB

**脚本执行（按顺序）**：

```bash
# Step 8 开始时先并行运行
python3 <DOC_INIT_DIR>/scripts/project_inventory.py --root . --output .doc-init-project-inventory.json
python3 <DOC_INIT_DIR>/scripts/git_history_miner.py --root . --output .doc-init-git-history.json

# inventory 完成后
python3 <DOC_INIT_DIR>/scripts/depth_scanner.py --root . --inventory .doc-init-project-inventory.json --output .doc-init-depth-scan.json
```

读取 `references/depth-patterns.md`，将 depth_scanner 输出的机械信号转化为 per-域知识候选（见该文件的信号→KB 段映射表）。误报的信号丢弃，不要机械复制。

若当前环境支持并行且用户未限制，**积极并行探索**：多候选域的代码入口探索可同时进行，每个 sub-agent 按业务域（而非模块）分配边界。

识别语言栈后，按需读取 `references/hidden-semantics/` 下的语言专项文档（语言列表见 `references/scan-and-boundary-report.md`「语言栈与隐藏语义」一节）。

读取 `references/multi-source-evidence.md`，结合 inventory 的 `evidence_sources` 做轻量多源证据发现；具体深挖围绕候选业务域进行，不在本步全量深挖。

### Step 8.5 — 数据库证据挖掘（可选增强）

若项目存在数据库配置，或候选业务域明显依赖数据库事实（状态、金额、余额、分表、流程、字典等），读取 `references/database-mining/workflow.md`，使用 `scripts/db_miner.py` 做轻量 catalog。

本阶段只做：表清单、字段清单、主键/索引和注释——不做全库 count/distinct/profile/sample-table。完成后可调用 `db_miner.py summarize-catalog` 生成目录级摘要（只读本地 JSON，不连库）。

缺少连接或用户禁止时，在知识边界报告和自评中标注「缺少真实数据口径」。

### Step 8.7 — 领域地图确认与深写优先级协商（交互门）

**除非用户明确禁止提问**，在知识边界报告输出后、进入 Step 9 前，必须向用户确认领域地图。**优先使用环境提供的内置选择工具**（如 `AskUserQuestion`），退化到纯文本时再用开放式提问。

**分步选择**：

**第一步：展示领域地图全景 + 确认边界划分**

先用纯文本输出完整领域地图（一屏可读），按三段分组：`已有文档覆盖（A 个）` → `本次深写（M 个，含理由）` → `Backlog（K 个，含锚点）`。

然后用结构化选择工具提问：

| 问题 | 选项 |
|------|------|
| 领域划分是否需要调整？ | ① 划分合理，继续（推荐）/ ② 需要拆分某个域 / ③ 需要合并某些域 / ④ 有域需要删除（废弃代码）|

**第二步：确认深写优先级**（仅当第一步选"划分合理"后才进入）

| 问题 | 选项 |
|------|------|
| 深写优先级是否需要调整？ | ① 当前顺序可以（推荐）/ ② 我近期常改某块，想提前 / ③ backlog 中有想提前深写的 |

**设计原则**：
- 推荐选项放第一个并标注"推荐"，多数情况用户直接确认即过
- 分步提问不拉锯：第一步如果用户要调整边界，调整完毕后直接进入 Step 9，不再问第二步（边界变了优先级自然要重排）

**用户选择后的行为**：

| 用户选择 | 行为 |
|---------|------|
| 两步都选推荐项 | 按当前地图和优先级进入 Step 9 |
| 要求拆分/合并/删除 | 调整地图后**不再二次确认**，直接进入 Step 9 |
| 调整优先级 | 按用户指定顺序重排，直接进入 Step 9 |
| 工具不支持 / 超时无回复 | 按模型判断继续 |

**禁止的反模式**：每个 KB 写完后问"写得对吗"；每发现一个模式问"这个重要吗"；"我要开始扫描了，确认吗"；用户确认后二次追问"你确定吗"。

### Step 9 — 针对性 Q&A 与文档生成

读取 `references/human-intake.md` 中的精准 Q&A 规则；读取 `references/document-templates.md`。

**时序约束（严格按序）**：
1. **Q&A 先于 sub-agent 派遣**：主 Agent 对本次深写主批的所有域集中做一轮 Q&A（用户未禁止时）。Q&A 聚焦代码看不到但影响 AI 改代码成败的问题（如业务峰值、哪些渠道最常出问题、审批流程、历史遗留约定）。
2. **Prompt 组装**：读取 `references/sub-agent-prompt-template.md`，为每个深写域组装结构化 prompt（域定义 + 入口清单 + depth_scanner 信号 + 主称谓 + Q&A 结果 + 质量闸门）。**禁止只给 sub-agent 一句"深写 X 域"的模糊指令**——模糊 prompt 产出骨架级文档，结构化 prompt 产出可用级文档。
3. **派遣 sub-agent**（若环境支持且主批 ≥ 2 个域）：无强耦合的域可并行；A 域依赖 B 域公共机制时串行。
4. **汇总阶段**（sub-agent 全部返回后主 Agent 强制执行）：
   - 公共机制提取检查：同一机制在 ≥2 篇 KB 中重复描述 → 判断是否抽取为 `*_GUIDE.md`
   - 交叉引用对齐：各 KB §8 互相引用跨域关系
   - 主称谓一致性校验：确认各 KB 对同一概念使用相同主称谓
   - 运维速查合并：多 host 模块项目逐一枚举端口

**并行时的禁止行为**：sub-agent 不得修改根 `AGENTS.md`、其他域的 KB 或公共 Guide——这些统一由主 Agent 在汇总阶段完成。

**生成文档**（本次深写主批逐域生成）：
- `docs/<DOMAIN>_KNOWLEDGE_BASE.md`（DOMAIN 必须是业务概念名，禁止用模块名）
- `docs/<TOPIC>_GUIDE.md`（公共横向机制才单独抽取；门槛见 `knowledge-network-design.md`）
- 项目根 `AGENTS.md`
- 项目根 `CLAUDE.md`（只写单行 `@AGENTS.md`）

**深写规范与质量闸门**见 `references/document-templates.md`「深写规范」章节，每个 KB 生成后必须立即对照质量闸门自检，不满足则回补。

**回写根 `AGENTS.md` 导航**（每生成一份文档后立即执行）：

```bash
python3 <DOC_INIT_DIR>/scripts/upsert_agents_nav.py --root . --path docs/<DOMAIN>_KNOWLEDGE_BASE.md --when-to-read "<任务触发句>"
```

`--when-to-read` 只写该文档覆盖的业务范围关键词（如「客户资料变更、状态流转、标签批量操作」），不要每条都重复「改、评审或排查…前必读」——通用触发模式应在导航段表头统一声明一次。

**登记 backlog**（主批写完后，把所有待补充领域全部登记，不得静默丢弃）：

```bash
python3 <DOC_INIT_DIR>/scripts/upsert_agents_nav.py \
  --root . --backlog \
  --name "<领域名> KB" \
  --anchor "<入口目录>" \
  --when-to-read "<触发场景>"
```

**持久化领域地图**（**必须**，即使本次已全部覆盖也要写）：

把完整领域地图写入根 `AGENTS.md` 的 `## 领域地图（doc-init）` 段。此段**仅服务于 `doc_coverage.py` 覆盖度闸门**，不重复文档导航已有的路径和触发句。

格式：基线戳 + 两列表格（领域 | 入口锚点），**禁止添加"状态"、"备注"等过程元数据列**——"已生成/本次深写/待补充"对后续工作模型无价值，文档路径已在文档导航段登记。

```markdown
## 领域地图（doc-init）

<!-- 覆盖度复核基线：2026-06-21 · 源码指纹 扫描 1573 文件 / Go 412 · TS 88 / 11 子模块 · 基线提交 a1b2c3d -->

| 领域 | 入口锚点 |
|------|---------|
| 渠道体系 | src/channels/ |
| Agent 执行循环 | src/agents/ |
| 插件体系 | src/plugins/ |
```

指纹值取自 inventory（`scan.scanned_files`、各 `languages[].file_count`、`submodules` 数量）和 `git rev-parse --short HEAD`。地图段登记的领域必须与文档导航段覆盖的领域一致（地图段不登记 backlog——backlog 通过 `upsert_agents_nav.py --backlog` 统一管理）。

**运维速查条件生成**：若 depth_scanner 输出的 `runnable_project.type` 不是 `library/cli/unknown`，在根 AGENTS.md 中生成「运维速查」段（格式见 `document-templates.md`）。多 host 模块项目必须逐一列出所有含 `spring-boot-maven-plugin`/`mainClass` 的子模块及其端口。

### Step 10 — 运行验证与 Operations 条件生成

只有项目存在本地运行价值时，读取 `references/operations-validation.md`。

运行验证产生的证据按语义分流：启动命令/探活/配置/日志路径进 `OPERATIONS_GUIDE.md`；业务接口真实行为/状态变化/错误码进对应领域 KB；跨领域共享机制进 `*_GUIDE.md`。

生成条件：
- 有至少一条可复用运行经验或启动阻碍 → 生成或更新 `docs/OPERATIONS_GUIDE.md`
- 未执行验证但项目存在运行面 → 只生成薄版「运行假设与待验证清单」
- 项目无本地运行面 → 不生成，把验证方式写进根 `AGENTS.md`

### Step 11 — 自我评估报告

先运行文档导航一致性检查：

```bash
python3 <DOC_INIT_DIR>/scripts/doc_nav_lint.py --root .
```

将 lint 的 error/warning 纳入自评。error 应先修复再报告完成。

**覆盖度账目（必须给出数字）**：

- 领域地图总数 N = 已生成（复用）A + 本次深写 M + 候选死代码/漂移 D + backlog B
- 断言：A + M + D + B = N ✓（不等则存在静默丢域，必须补录 backlog）
- 断言：根 `AGENTS.md` 的 `## 领域地图（doc-init）` 段已写入且与账目一致 ✓
- 断言：地图段已带「覆盖度复核基线」戳 ✓

**若走过 Step 6.5**，额外输出覆盖度复核账目（G 个缺口 + R 个过期需刷新；G + R == 0 才允许判定真正完成）。

自评内容还需覆盖（逐项给出，不能笼统一段话带过）：
- 每份 KB 的深写质量闸门通过情况（§2/§3/§4/§6/§7 是否满足最低要求，不满足的标明原因和补救）
- depth_scanner 信号利用率（输出多少信号、写入 KB 多少、丢弃多少及原因）
- 领域语言覆盖（主称谓是否统一、是否存在未消歧的同名异义）
- Git 弱信号覆盖（是否可用、热点和 fix/revert 线索是否只作为待确认候选）
- 数据库证据覆盖（是否连接成功、哪些域做了 catalog、哪些关键表未分析）
- 多源证据覆盖（哪些证据源可用、哪些深挖了、哪些高价值缺失）
- 高风险未覆盖项（概念未消歧、状态流转不明、机制生效条件不清、验证路径缺失）
- Operations 验证覆盖（已执行哪些步骤、哪些仍是低置信假设）
- 后续沉淀建议（哪些应由 doc-update 补入、哪些适合 doc-compact 整理）

### Step 12 — 深入探究提议（强制，不可跳过）

自评完成后**必须**向用户提出至少 3 个可继续深入探究的方向。**使用结构化多选工具**（如 `AskUserQuestion multiSelect: true`），每个选项格式：`[域名/机制名] — [当前状态] — [可继续做什么]`。

提议来源（必须基于本次实际发现，不要凭空编造）：
- 质量闸门中标记"补救"或"模板级"的条目
- depth_scanner 信号中"丢弃/无法确认"的候选
- §6 中标"低置信"的约束
- backlog 中与已深写域耦合最紧的 1-2 个域
- 跨域事件/MQ 联动未展开的
- §7 验证路径只有模板、缺真实参数的

**用户选择后的执行**：

- ≥ 2 个独立方向 → 派 sub-agent 并行；有依赖的先串行前置，再并行后续
- 1 个方向 → 主 Agent 直接执行
- 每轮完成后再次提议（继续用多选工具），直到用户主动终止

**每轮深入完成后强制更新**：领域地图段状态、backlog 段、文档导航，并输出 1-2 行增量摘要（如"地图 8 域中已深写 4 → 5"）。
