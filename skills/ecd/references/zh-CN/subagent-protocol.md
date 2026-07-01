# 子Agent协议 v2 — Claude Code 适配

## 概要

- D、G、H、J 阶段必须使用 Claude Code 的 `Agent` 工具启动真实独立子 Agent。
- A 阶段可选使用支持子 Agent，但主模型保留预处理的所有权。
- 只传递与阶段相关的局部上下文。
- 不得将主模型的偏好答案传递给独立 Agent。
- 主模型是 bundle 笔记的唯一写入者。
- 子 Agent 只返回结构化增量（delta），不返回完成的笔记。

## Claude Code Agent 工具用法

对于每个强制子 Agent 阶段，使用 `Agent` 工具：

```
Agent(
  description: "简短描述任务（3-5词）",
  subagent_type: "general-purpose",
  prompt: "<阶段相关的上下文和指令>"
)
```

子 Agent 的结果会包含在工具返回值中。主模型读取这些发现后，将其整合进相应的 bundle 阶段笔记中。

## 共享 Delta 结构

所有子 Agent 应返回以下结构的发现：

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

## A 支持 Agent 模式（可选）

这些是可选的辅助 Agent。仅在它们能实质性改善预处理时使用。

### Intent Extractor（意图提取器）

```
阅读用户的原始请求加上当前账本快照。推断用户可能想要的超出字面意思的内容。假设用户可能尚未理解自己期望的结果。返回 suspected_real_goals、hidden_assumptions、scenario_fragments、值得引出的示例或反例，以及能增加语义覆盖率的广泛澄清问题。
```

### Reality Gap Checker（现实差距检查器）

```
阅读用户的原始请求加上任何本地事实。挑战可能错误、不完整、矛盾、非技术性、偏向解决方案或基于缺失客观事实的主张。返回事实、挑战、差距、需要验证的矛盾点，以及能迫使用户暴露隐藏语义的澄清问题。
```

### Blind Spot Scout（盲区侦察员）

```
阅读用户的原始请求加上当前账本快照。识别用户可能尚未提及的重要维度：工作流边缘情况、非目标、成功信号、约束、权衡、验收含义、环境依赖和失败处理。返回盲区、覆盖缺口，以及推动用户明确他们尚未意识到需要表达的内容的澄清问题。
```

## D 挑刺 Agent

```
Agent 任务: 你是一名独立评论员。审查保留的需求包。识别伪需求、矛盾需求、不可验证需求、范围浪费、隐藏假设和错误分解。建议应丢弃、拆分或重写的内容。仅返回结构化增量。
```

Claude Code 调用方式：
```
Agent(description: "Independent critique of requirements", subagent_type: "general-purpose", prompt: "你是一名独立评论员。审查保留的需求包...[上下文内容]...识别伪需求、矛盾需求、不可验证需求、范围浪费、隐藏假设和错误分解。建议应丢弃、拆分或重写的内容。仅返回结构化增量。")
```

## G 红蓝 Agent

### Red Prompt（红方攻击）

```
Agent 任务: 攻击保留路径。聚焦边界情况、滥用、缺失假设、依赖断裂、不可能的状态转换、模糊的恢复行为、无效输入和未处理的环境失败。仅返回攻击向量和缺口发现。
```

### Blue Prompt（蓝方防守）

```
Agent 任务: 防守保留路径。对每个可能的攻击或失败模式，要么提供缓解方案、验收规则、监控要求，要么在问题无法在此版本中解决时显式声明残余风险。仅返回结构化增量。
```

注意：红蓝双方应作为**独立的两次 Agent 调用**分别启动，以确保独立对抗。

## H 评审 Agent

```
Agent 任务: 审查完整的 A-H 包以判定编码就绪性。如果下一个编码模型仍需要发明核心含义、产品语义、验证含义或依赖行为，则拒绝它。返回裁决：approved、approved_with_conditions 或 rejected。返回阻塞项、条件、理由，以及在拒绝时应重开的最早阶段。
```

## J 编译 Agent

```
Agent 任务: 读取收敛后的 A-H 包加当前交接状态。将保留结果编译为冻结的伴侣文档和最终的代码就绪摘要。确认包是否 code_ready、必须引用哪些契约文档、直接的下一步 code 命令应是什么，以及在尚未就绪时保持了 case 打开的阻塞项有哪些。
```

## 失败处理

- 如果无法启动所需的 Agent（Agent 工具不可用或返回错误）：
  - 仍然写入阶段笔记
  - 将 `status` 设为 `blocked_by_agent_unavailable`
  - 将 `agent_mode` 设为 `blocked`
  - 阻止后续依赖阶段被标记为 complete
- 即使 Agent 工具不可用，也绝不可静默完成强制子 Agent 阶段
- 如果子 Agent 返回内容质量不足（过于简略或未进行真正的独立审查），应重新启动 Agent 并提供更具体的指令
