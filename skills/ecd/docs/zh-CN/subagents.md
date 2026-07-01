# 真实子代理协议 — Claude Code 适配

## 为什么 ECD 必须使用真实子代理

ECD 强制引入真实子 Agent，是为了对抗一个非常稳定的失败模式：父模型一旦锚定了自己的解释，就会下意识为它辩护。

所以这些独立阶段不是装饰性的"多叫几个 agent 看看"，而是结构性质量门。

## 硬规则

下面这些阶段必须使用 Claude Code `Agent` 工具启动真实独立子 Agent：

- D / critique — 一个独立 critique Agent
- G / red-blue — 两次独立 Agent 调用（红方 + 蓝方）
- H / review — 一个独立 review Agent
- J / compile-for-code — 一个独立 compile Agent

Stage A 可以使用支持 Agent，但 preprocess 的所有权和写入权仍然属于主模型。

## Claude Code Agent 工具用法

每个强制子 Agent 阶段使用以下模式：

```
Agent(
  description: "简短描述任务（3-5词）",
  subagent_type: "general-purpose",
  prompt: "<阶段相关的上下文和指令>"
)
```

子 Agent 的结果包含在工具返回值中。主模型读取返回后发现后，将其整合进对应的 bundle 阶段笔记中。

## 通用协议

所有子 Agent 都遵循同一套基础规则：

- 只接收当前阶段的局部上下文（原始需求 + 当前 ledger 快照 + 相关源产物）
- 不接收父模型偏好的最终答案
- 返回结构化增量（delta），而不是直接写最终 note
- 不允许直接改 bundle 文件
- bundle 的唯一写入者始终是主模型（通过 `Write`/`Edit` 工具）

## 共享 delta 结构

所有独立 Agent 默认返回这一结构：

```json
{
  "facts": [],
  "challenges": [],
  "conflicts": [],
  "gaps": [],
  "discard_recommendations": [],
  "follow_up_questions": [],
  "confidence": "medium",
  "evidence_refs": []
}
```

这样主模型就能集成独立发现，而不会把 bundle 的规范写入权交出去。

## Stage A 的 support agents

这些 Agent 是可选的。它们主要用在原始请求很模糊、过于 solution-biased 或者内部矛盾明显的时候。

### Intent Extractor（意图提取器）

用途：

- 推断用户字面请求背后的真实目标
- 挖出隐藏假设
- 产出值得追问的例子和反例

适用场景：

- 用户一上来就先讲解决方案，没有讲真实问题
- 请求听起来很笼统，但语气又很确定

### Reality Gap Checker（现实差距检查器）

用途：

- 挑战可能是错的、残缺的、和 repo 现实不符的说法
- 揪出请求与客观现实之间的落差

适用场景：

- 用户用主观判断描述 repo 行为
- 拟议方案依赖的基础设施可能根本不存在

### Blind Spot Scout（盲区侦察员）

用途：

- 找出用户还没意识到应该说出来的维度
- 逼出 non-goals、边界条件、验收含义和失败处理

适用场景：

- 请求一上来就直接进入功能构建
- 重要工作流边缘很可能还没有被命名

## D / Critique Agent

Stage D 需要一个独立 critique Agent。

### 任务

- 识别伪需求
- 揪出矛盾
- 删除不可验证或浪费的需求
- 在需求冻结前挑战糟糕的拆解方式

### Claude Code 调用

```
Agent(description: "Independent critique of requirements", subagent_type: "general-purpose", prompt: "你是一名独立评论员。审查保留的需求包。识别伪需求、矛盾需求、不可验证需求、范围浪费、隐藏假设和错误分解。建议应丢弃、拆分或重写的内容。仅返回结构化增量。上下文：[当前 ledger 快照 + 保留需求包]")
```

### 它为什么存在

如果没有 D，Stage C 很容易把"写得很像样的错误需求"冻结下来。

## G / Red And Blue Agents

Stage G 需要两次独立的 `Agent` 调用。

### Red（红方攻击）

任务：

- 攻击边界条件
- 攻击滥用路径
- 攻击依赖故障
- 攻击非法状态转换
- 攻击恢复行为中的模糊地带

```
Agent(description: "Red team attack on plan", subagent_type: "general-purpose", prompt: "攻击保留路径。聚焦边界情况、滥用、缺失假设、依赖断裂、不可能的状态转换、模糊的恢复行为、无效输入和未处理的环境失败。仅返回攻击向量和缺口发现。上下文：[保留路径 + 依赖链 + 探针证据]")
```

### Blue（蓝方防守）

任务：

- 对攻击给出缓解方式
- 把攻击转成明确规则
- 如果这版做不到，就把它写成残余风险

```
Agent(description: "Blue team defense of plan", subagent_type: "general-purpose", prompt: "防守保留路径。对每个可能的攻击或失败模式，要么提供缓解方案、验收规则、监控要求，要么在问题无法在此版本中解决时显式声明残余风险。仅返回结构化增量。上下文：[保留路径 + 红方攻击结果]")
```

### 为什么两者缺一不可

只有 red 没有 blue，会只剩下焦虑。只有 blue 没有 red，会只剩下乐观。两者一起才会逼出清晰的防守面。

## H / Review Agent

Stage H 需要一个独立 review Agent。

### 任务

- 判断下一位 coder 是否还得发明含义
- 返回 `approved`、`approved_with_conditions` 或 `rejected`
- 如果 rejected，指出最早该回流到哪个阶段

### Claude Code 调用

```
Agent(description: "Review package for code readiness", subagent_type: "general-purpose", prompt: "审查完整的 A-H 包以判定编码就绪性。如果下一个编码模型仍需要发明核心含义、产品语义、验证含义或依赖行为，则拒绝它。返回一个裁决：approved、approved_with_conditions 或 rejected。返回阻塞项、条件、理由，以及在拒绝时应重开的最早阶段。上下文：[完整 A-H package]")
```

### H 保护的是什么

H 保护的是"假的 ready"。一个 bundle 看起来写得很多，不代表它真的没有高影响语义缺口。

## J / Compile-for-Code Agent

Stage J 需要一个独立 compile Agent。

### 任务

- 吸收已收敛的 A-H package
- 判断这份 package 是否真的 code-ready
- 编译 execution-facing companion docs
- 确认下一条直接可执行的 code command

### Claude Code 调用

```
Agent(description: "Compile A-H results for code", subagent_type: "general-purpose", prompt: "读取收敛后的 A-H 包加当前交接状态。将保留结果编译为冻结的伴侣文档和最终的代码就绪摘要。确认包是否 code_ready、必须引用哪些契约文档、直接的下一步 code 命令应是什么，以及在尚未就绪时保持了 case 打开的阻塞项有哪些。上下文：[收敛后的 A-H package + 当前 handoff]")
```

### 为什么 J 不等于 H

H 判断的是 ready 不 ready，J 负责把 ready 的结果编译成真正可执行的产物。一个 package 可能通过了 review，但仍然没有被编译成好用的 handoff。

## 故障处理

如果某个必需 Agent 无法创建（`Agent` 工具不可用或返回错误）：

- 阶段 note 仍然要写
- `status` 必须写成 `blocked_by_agent_unavailable`
- `agent_mode` 必须写成 `blocked`
- 依赖这个阶段的后续阶段不能继续假装 complete

ECD 不允许在失去独立性的前提下伪造完成状态。

## 在 Claude Code 里的实践建议

在 Claude Code 里实现这套协议时：

- 子 Agent prompt 要严格保持 stage-local
- 不要把你自己的答案当默认答案喂给子 Agent
- 把 delta 写回 note 之前，要再次对照 repo 现实（用 `Read`/`Glob`/`Grep`）
- evidence refs 要保留下来，方便 validator 和后来的人审计整个推理链
