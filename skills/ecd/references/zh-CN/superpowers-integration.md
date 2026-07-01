# Superpowers 互补集成 `[v1.1]`

## 目的

ECD 和 Superpowers 解决交付问题的不同半场。ECD 擅长语义冻结（pre/plan），Superpowers 擅长工程纪律（TDD、code review、分支管理）。两者组合形成完整的交付流水线。

## 分工

| 能力 | ECD | Superpowers |
|------|-----|-------------|
| 语义冻结 (pre/plan) | **主力** — 阶段 A-J 在代码触碰仓库前冻结所有产品含义 | 无 |
| TDD 强制 | 无 — 指定验证命令但不强制 TDD 门控 | **主力** — `test-driven-development` skill 强制红-绿-重构 |
| 独立对抗审查 | **主力** — 基于子Agent（D 挑刺、G 红蓝、H 评审、J 编译） | 辅助 — `requesting-code-review` skill（合规导向） |
| 分支隔离 | 无 | **主力** — `using-git-worktrees` skill |
| 执行规划 | **主力** — 带契约的冻结实现单元 | **主力** — `writing-plans` + `executing-plans`（2-5 分钟任务） |
| 完成前验证 | `achieve` 阶段（基于证据的关闭） | `verification-before-completion` skill |
| 调试 | `references/diagnosis-and-observability.md` | `systematic-debugging` skill（4 阶段方法） |

## 推荐工作流

### 方案 A：ECD Plan + Superpowers Execute

最适合需要语义保真和工程质量的中大型功能。

```
1. ECD pre/plan (A 到 J)
   → 产出含 90-code-handoff.md 的冻结 bundle
   → 语义已锁定，不再有产品决策

2. Superpowers using-git-worktrees
   → 为变更隔离工作区

3. Superpowers test-driven-development
   → 从 ECD 的函数契约和验收检查编写测试
   → 先看到测试 FAIL

4. 从 ECD 交接包执行
   → Superpowers executing-plans 消费 ECD 的实现单元
   → 适用 ECD 的 code-playbook 规则：不发明产品含义

5. Superpowers verification-before-completion
   → 验证所有验收检查通过
   → 确认首次打开 UX 没有损坏

6. ECD achieve
   → 带 archive/left_open 裁决的基于证据的关闭
```

### 方案 B：ECD Lite + Superpowers TDD

最适合需要 TDD 但不需要完整对抗审查的中小型功能。

```
1. ECD A-Lite → J-Lite（L1 或 L2 等级）
   → 带紧凑交接包的快速语义冻结

2. Superpowers test-driven-development
   → 从交接包的验证命令进行 TDD

3. Superpowers verification-before-completion
   → 关闭前验证

4. ECD achieve-Lite
   → 快速基于证据的关闭
```

### 方案 C：仅 Superpowers

最适合 bug 修复、重构或需求已无歧义的任务。完全跳过 ECD — 仅 Superpowers 就足够。

## 交接格式：ECD → Superpowers

当 ECD 的 plan 阶段交接给 Superpowers 的 executing-plans 时：

| ECD 输出 | 映射到 Superpowers 输入 |
|----------|------------------------|
| `90-code-handoff.md` → `implementation_units` | `writing-plans` 任务列表 |
| `90-code-handoff.md` → `function_contracts` | TDD 测试规格 |
| `90-code-handoff.md` → `verification_commands` | `verification-before-completion` 检查项 |
| `90-code-handoff.md` → `acceptance_checks` | 最终验收清单 |
| `05-constraint-ledger.md` → `frozen_constraints` | "不要重新解释"护栏 |

## 反模式

- ❌ **不要**为简单改动跑 ECD Full (L3)"以求稳妥" — 用 ECD-Lite 或仅 Superpowers
- ❌ **不要**在绿地项目中跳过 ECD 的 pre — Superpowers brainstorming 不等同于 ECD Stage A 的语义挖掘
- ❌ **不要**在复杂/模糊需求上用 Superpowers brainstorming 做语义发现 — 那是 ECD 的领域
- ❌ **不要**用 ECD 替代 TDD — 把 Superpowers 的 `test-driven-development` skill 加入工作流
- ✅ **要**让 ECD 管含义，Superpowers 管执行质量 — 边界清晰

## 何时使用（决策矩阵）

| 场景 | 推荐 |
|------|------|
| 新绿地应用，需求不清晰 | ECD Full (L3) pre/plan → Superpowers execute |
| 给已有应用加认证 | ECD Full (L3) pre/plan → Superpowers execute |
| 新 API 端点，规格明确 | ECD Standard (L2) → Superpowers TDD |
| 暗色模式切换 | ECD Lite (L1) 或仅 Superpowers |
| 已知根因的 bug 修复 | 仅 Superpowers（systematic-debugging + TDD） |
| 性能优化（"让它变快"） | ECD Full (L3) Stage A 先 — 有指标前阻塞 |
| 重构（保持行为不变） | 仅 Superpowers |
