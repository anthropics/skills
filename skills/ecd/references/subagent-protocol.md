# Subagent Protocol v2 — Claude Code 适配

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
Read the user's raw request plus the current ledger snapshot. Infer what the user probably wants beyond the literal wording. Assume the user may not understand their own desired outcome yet. Return suspected_real_goals, hidden_assumptions, scenario_fragments, examples or counterexamples worth eliciting, and broad clarification questions that increase semantic coverage.
```

### Reality Gap Checker（现实差距检查器）

```
Read the user's raw request plus any local facts. Challenge claims that may be false, incomplete, contradictory, non-technical, solution-biased, or based on missing objective facts. Return facts, challenges, gaps, contradictions to verify, and clarification questions that would force the user to expose hidden semantics.
```

### Blind Spot Scout（盲区侦察员）

```
Read the user's raw request plus the current ledger snapshot. Identify important dimensions the user likely has not named yet: workflow edges, non-goals, success signals, constraints, tradeoffs, acceptance meaning, environmental dependencies, and failure handling. Return blind spots, coverage gaps, and clarification questions that push the user to specify what they have not realized they need to say.
```

## D Critique Agent（挑刺 Agent）

```
Agent 任务: 你是一名独立评论员。审查保留的需求包。识别伪需求、矛盾需求、不可验证需求、范围浪费、隐藏假设和错误分解。建议应丢弃、拆分或重写的内容。仅返回结构化增量。
```

Claude Code 调用方式：
```
Agent(description: "Independent critique of requirements", subagent_type: "general-purpose", prompt: "You are an independent critic. Review the retained requirement package...[上下文内容]...Identify pseudo-requirements, contradictory requirements, unverifiable requirements, scope waste, hidden assumptions, and incorrect decompositions. Recommend what should be discarded, split, or rewritten. Return structured deltas only.")
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

## H Review Agent（评审 Agent）

```
Agent 任务: 审查完整的 A-H 包以判定编码就绪性。如果下一个编码模型仍需要发明核心含义、产品语义、验证含义或依赖行为，则拒绝它。返回裁决：approved、approved_with_conditions 或 rejected。返回阻塞项、条件、理由，以及在拒绝时应重开的最早阶段。
```

## J Compile Agent（编译 Agent）

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
