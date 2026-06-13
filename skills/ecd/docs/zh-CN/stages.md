# ECD 阶段模型

## 等级模型 `[v1.1]`

ECD v1.1 使用 3 问题复杂度分类器将任务路由到三个执行等级，防止简单任务承受完整的 10 阶段流程。

### 复杂度分类器

执行任何阶段前，先静默回答以下 3 个问题：

| 问题 | L1 (轻量) | L2 (标准) | L3 (重量) |
|------|-----------|-----------|-----------|
| **Q1** 代码影响面 | ≤3 文件 | 4-10 文件 | >10 文件 |
| **Q2** 安全/正确性风险 | 仅UI（样式、文案） | 功能逻辑、API | 数据丢失、认证、支付、PII |
| **Q3** 需求清晰度 | 清晰无歧义 | 部分细节待定 | 模糊（如"让它变快"） |

`最终等级 = max(Q1, Q2, Q3)`。Q3 为"模糊"时 → 强制 L3。Greenfield 项目 → Q1 默认为 L2。用户可覆盖：`--tier lite|standard|full`。

### 等级定义

| 等级 | 触发条件 | 阶段 | 子Agent | Token预算 | 适用任务示例 |
|------|---------|------|---------|----------|------------|
| **L1 ECD-Lite** | max=1 | A-Lite → J-Lite → code → achieve-Lite | 0 | 15k-30k | 暗色模式切换、修bug、文案修改、单组件改动 |
| **L2 ECD-Standard** | max=2 | A → B → C → D(可选) → E(精简) → H(可选) → J → code → achieve | 0-2 可选 | 35k-55k | 新增API、中等功能、多文件改动 |
| **L3 ECD-Full** | max=3 | A → B → C → D → E → F → G → H → J → code → achieve | 5 强制 | 65k-105k | 认证系统、架构变更、安全敏感、需求模糊 |

**L3 完全等同于 ECD v1.0。** 已有 bundle 若缺失 tier 字段，默认视为 L3。

### Lite 阶段变体

- **A-Lite**：最多 3 个反问，冻结重述目标、范围边界、验收检查、关键假设。跳过方案发散和深度拆解。
- **J-Lite**：将 A-Lite 输出直接编译为最小 `90-code-handoff.md`。无伴侣文档（91/92/95/96/98/99）。
- **achieve-Lite**：运行验证命令 → 检查首次打开体验 → 裁决。简化的基于证据的关闭。

### L2 可选阶段规则

- **D (批判)**：需求单元 >5 或存在横切关注点时运行
- **H (评审)**：交接包有 >3 个实现单元时运行
- **E (补全)**：精简模式 — 仅解决高影响依赖缺口，跳过执行链编译

## 阶段总览

ECD 把交付过程拆成带所有权边界的阶段。每条边界都是为了阻止某一种语义漂移。

| 阶段 | 等级 | 所有者 | 核心目的 | 主产物 | 是否必须独立子 Agent |
| --- | --- | --- | --- | --- | --- |
| `pre` / A | L1,L2,L3 | 主模型 | 追问请求并冻结 approval target | `10-a-preprocess.md` | 可选 support agents |
| B | L2,L3 | 主模型 | 生成真正不同的保留路径 | `20-b-divergence.md` | 否 |
| C | L2,L3 | 主模型 | 冻结需求单元与后续 coding cut line | `30-c-requirements.md` | 否 |
| D | L2,L3 | critique agent + 主模型 | 独立攻击模糊或浪费的需求 | `40-d-critique.md` | L3: 是 / L2: 可选 |
| E | L2,L3 | 主模型 | 闭合依赖缺口和执行前置条件 | `50-e-closure.md` | 否 |
| F | L3 | 主模型 | 用 repo / 环境现实验证规划 | `60-f-probes.md` | 否 |
| G | L3 | red agent + blue agent + 主模型 | 攻击并防守保留路径 | `70-g-red-blue.md` | L3: 是（两次调用） |
| H | L2,L3 | review agent + 主模型 | 判断下一个 coder 是否还得发明含义 | `80-h-review.md` | L3: 是 / L2: 可选 |
| J | L1,L2,L3 | compile-for-code agent + 主模型 | 把 A-H 编译成 code-ready package | `98-j-compile-for-code.md`、`99-code-handoff.md` | L3: 是 / L2: 可选 / L1: 否 |
| `code` | L1,L2,L3 | coding model | 严格按 handoff 执行 | `Runs/<run-id>/00-code-run.md` | 否 |
| `achieve` | L1,L2,L3 | closure model | 判断结果是否真的满足验收 | `Runs/<run-id>/03-achieve.md` | 否 |

## 共享真值面

整个流程里最关键的两份文件是：

- `05-constraint-ledger.md`：共享规划真值面
- `90-code-handoff.md`：唯一真实的 `code` 入口

配套 companion bundle 负责把这些真值展开成可检查、可执行的表面：

- `91-canonical-contracts.md`
- `92-constraint-crosswalk.md`
- `95-execution-manifest.md`
- `96-code-batches.md`
- `97-code-preflight.md`
- `98-j-compile-for-code.md`
- `99-code-handoff.md`

## A-Lite 阶段 `[L1]`

**适用等级：** L1 专属。

面向简单任务的精简预处理。最多 3 个反问。

### 输入

- 原始请求
- repo 现实
- 本地文档、测试、配置

### 输出

- 重述请求
- 保留范围 / 排除范围
- 验收检查（3-5 项）
- 关键假设
- 紧凑审批包

### 退出门

用户明确批准紧凑审批包。剩余未知项是真正的低影响实现细节。

### 为什么要有 A-Lite

对于"加个暗色模式切换"这类需求，完整 A 阶段的追问（7+ 问题、深层语义挖掘）是过度工程。A-Lite 刚好冻结了安全执行所需的足够语义。

## `pre` 与 A 阶段 `[L2, L3]`

`pre` 拥有 approval gate。

### 输入

- 原始请求
- repo 现实
- 本地文档、测试、配置、产品线索

### 输出

- reframed request
- ambiguity list
- hidden assumptions
- scenario fragments
- approval pack

### 退出门

只有用户明确批准了重述后的方向，才允许离开 Stage A。

### A 为什么存在

如果这里问得不够狠，后面的每个阶段都会变成替用户补语义。

## B / Divergence `[L2, L3]`

Stage B 强制在收敛前展开选项空间。

### 输入

- 已经过 Stage A 冻结的理解

### 输出

- 真正不同的 options
- retained option id
- dropped options

### 退出门

必须且只能保留一条路径。样式微调不算真实 option。

## C / Requirements `[L2, L3]`

Stage C 把保留下来的路径翻成实现相关的需求单元。

### 输入

- retained option
- constraint ledger

### 输出

- requirement units
- interface contracts
- validation targets
- frozen terms

### 退出门

内容必须具体到让 coder 不再需要发明产品含义。

## D / Critique `[L2, L3]`

Stage D 是第一个独立攻击阶段。**L3 强制，L2 可选**（需求单元 >5 或存在横切关注点时运行）。

### 输入

- 保留后的 requirement package

### 输出

- critique findings
- conflicts
- dropped pseudo-requirements
- resolution decisions

### Claude Code 实现

使用 `Agent` 工具启动独立 critique 子 Agent：
```
Agent(description: "Independent critique of requirements", subagent_type: "general-purpose", prompt: "你是一名独立评论员...")
```

### 退出门

如果 `Agent` 工具不可用，必须诚实地把阶段标成 `blocked_by_agent_unavailable`，而不是假装 complete。

## E / Closure `[L2, L3]`

Stage E 负责补齐依赖链上的漏洞。**L2（精简）：** 仅解决高影响缺口，跳过执行链编译。**L3（完整）：** 完整依赖链加执行排序。

### 输入

- retained requirements
- critique 决策

### 输出

- end-to-end dependency chain
- dependency gap resolutions
- completion chain

### 退出门

进入编码前，不能再留高影响依赖缺口。

## F / Probes `[L3]`

Stage F 让规划接受 repo 和环境现实的检验。

### 输入

- 关于 repo、命令或环境的假设

### 输出

- probes
- discarded paths
- surviving paths

### Claude Code 实现

使用 `Bash` 工具实际运行探针代码，验证技术路径可行性。

### 退出门

complete 状态必须伴随可执行证据，或者伴随明确的无法探测说明。

## G / Red-Blue `[L3]`

Stage G 在批准前强制加入对抗压力。

### 输入

- retained path
- dependency chain
- probe evidence

### 输出

- red-team attacks
- blue-team mitigations
- residual risks

### Claude Code 实现

使用 `Agent` 工具启动两次独立调用——先红方、后蓝方。两次调用必须独立，不可由主模型自己扮演。

### 退出门

所有攻击要么被缓解，要么被明确写成残余风险。

## H / Review `[L2, L3]`

Stage H 是 coding-readiness gate。**L3 强制，L2 可选**（交接包有 >3 个实现单元时运行）。

### 输入

- 完整的 A-H package

### 输出

- verdict
- blockers 或 approval conditions
- rationale
- 如果被拒绝，应该回到哪个阶段

### Claude Code 实现

使用 `Agent` 工具启动独立 review 子 Agent。不得将主模型的偏好答案传递给 Review Agent。

### 退出门

只要下一位 coder 还需要补产品语义、验证含义、状态行为或者依赖行为，H 就必须拒绝。

## J-Lite / Compile For Code `[L1]`

**适用等级：** L1 专属。

将 A-Lite 输出直接编译为最小交接包。

### 输入

- 已批准的 A-Lite 输出
- repo 事实

### 输出

- 最小 `90-code-handoff.md`（无伴侣文档）
- `97-code-preflight.md`

### 退出门

`code_ready=true` 仅当最小交接包使编码者无需发明产品语义即可实现。

## J / Compile For Code `[L1, L2, L3]`

Stage J 负责把规划真值编译成 coder 真正可执行的产物。

### 输入

- 已收敛的 A-H package
- 当前 handoff 状态

### 输出

- code-ready verdict
- companion docs
- final handoff summary
- reopen stage if blocked

### Claude Code 实现

使用 `Agent` 工具启动独立 compile 子 Agent。

### 退出门

只有当下一个编码模型不需要重新解释产品含义时，才允许把 `code_ready` 标成 `true`。

## achieve-Lite `[L1]`

**适用等级：** L1 专属。

面向 L1 任务的轻量级关闭。基于最小交接包。

### 输入

- 已验证的 L1 bundle
- 最新 code run 证据
- 验收检查
- 验证证据

### 输出

- achieve 裁决：`achieved` / `not_achieved`
- 归档状态：`archived` / `left_open`
- `Runs/<run-id>/03-achieve.md`

### 退出门

验收检查通过且首次打开体验无明显损坏。

## `code` `[L1, L2, L3]`

`code` 是执行阶段，不是解释阶段。

### 必要入场条件

- 存在 bundle path 或 handoff path
- `90-code-handoff.md` 存在
- `ecl.code_handoff.code_ready=true`
- repo target 存在

### 必要行为

- 只读 handoff 和显式引用的文件
- 用 `TaskCreate`/`TaskUpdate` 跟踪实现单元进度
- 严格按 implementation units 顺序执行
- 每个 unit 后都用 `Bash` 运行验证
- 更新 `97-code-preflight.md`
- 用 `Write` 写回 `00-code-run.md` 和 `01-verification.md`

### 回流规则

只要出现高影响语义缺口，就必须停止，并回流到最早破掉的阶段。

## `achieve` `[L1, L2, L3]`

`achieve` 决定证据是否足以支持 closure。

### 输入

- 已通过校验的 bundle
- 最近一次真实 code run
- acceptance checks
- verification evidence

### 输出

- achieve verdict
- archive status
- archive reason
- next actions

### Claude Code 实现

运行 `python scripts/ecd.py achieve --case /abs/path/to/bundle` 渲染 achieve 判定。

### 退出门

只要验收失败或者首开体验明显有问题，这个 case 就必须保持 open。
