# ECD Agent 接口定义 — Claude Code

Claude Code 使用 `Agent` 工具启动子 Agent。每个强制阶段需要特定的 Agent 配置。

## 通用接口

```yaml
interface:
  display_name: "Evolutionary Constraint Development"
  short_description: "Strict ECD pre/plan/code/achieve delivery loop"
  default_prompt: "Use ecd (Evolutionary Constraint Development) to turn a raw product or engineering request into a Stage A approval workspace, then a frozen code-ready handoff, execute only from that handoff, and verify the delivered result with the strict pre/plan/code/achieve contract."
```

## 强制子 Agent 阶段

### D — Critique Agent（挑刺）

- **类型**: `general-purpose`
- **目标**: 独立攻击需求和方案，剔除不合理项
- **必须拥有**: Read、Grep、Glob 工具访问权限（读取 bundle 和 repo 上下文）
- **返回**: 结构化增量 — critique_findings、conflicts、dropped_requirements、resolution_decisions

### G — Red Agent（红方攻击）

- **类型**: `general-purpose`
- **目标**: 独立攻击保留路径，发现边界问题和漏洞
- **返回**: 结构化增量 — attack_vectors

### G — Blue Agent（蓝方防守）

- **类型**: `general-purpose`
- **目标**: 独立评估攻击面，提供缓解方案
- **返回**: 结构化增量 — mitigations、residual_risks

### H — Review Agent（评审）

- **类型**: `general-purpose`
- **目标**: 独立判定包是否编码就绪
- **返回**: 结构化增量 — verdict、approval_conditions、blockers、rationale、reentry_stage_if_rejected

### J — Compile Agent（编译交接）

- **类型**: `general-purpose`
- **目标**: 独立编译 A-H 结果为代码就绪包
- **返回**: 结构化增量 — code_ready、blocking_gaps、frozen_contract_refs、handoff_entry

## 可选支持 Agent（阶段 A）

- **Intent Extractor**: 推断用户真实意图
- **Reality Gap Checker**: 挑战不符合事实的主张
- **Blind Spot Scout**: 发现用户未提及的维度
