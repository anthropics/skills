# 编码执行手册 v2 — Claude Code 适配

Claude Code 工具映射：`Read`/`Glob`/`Grep` 用于仓库落地，`Bash` 用于运行验证命令和 CLI 脚本，`Write`/`Edit` 用于代码修改和运行记录，`TaskCreate`/`TaskUpdate` 用于跟踪实现单元进度。

## 目的

当用户明确要求 ECL 从规划继续进入实现时使用此手册。`/code` 的目的是执行冻结的交接包，而非重新解释产品意图。

## 入场条件

仅当以下**全部**成立时才进入 `/code`：

- 调用者提供了 `--case <bundle-dir>` 或 `--handoff <绝对路径-to-90-code-handoff.md>`
- `ecl.code_handoff.code_ready=true`
- 引用的仓库目标存在
- 交接包没有未解决的高影响缺口

如果任何门控失败：

- 不修改仓库
- 仍然写入运行记录
- 写入重入请求
- 将 plan 指回最早受影响的 A-H 阶段

## 必须已冻结的交接面

编码开始前，确认交接包显式包含：

- `repo_grounding`
- `frozen_product_decisions`
- `domain_model`
- `data_contract`
- `ui_contract`
- `function_contracts`
- `file_plan`
- `implementation_units`
- `verification_commands`
- `browser_checks`
- `acceptance_checks`

## 允许的决策

`/code` 仅可决定低影响的工程细节，如：

- 在已冻结范围内的辅助函数拆分
- import 接线
- 包锁文件更新
- 不改变行为的微小文件放置细节

`/code` 不得决定：

- 用户目标含义
- 已冻结的产品语义
- 规划遗漏的数据或状态行为
- 验证含义
- 成功标准
- 依赖行为
- 评审条件
- 验收语义
- 交接包仍表述为可选的可见 UI 选择

## 必读内容

仅阅读：

- `90-code-handoff.md`
- `97-code-preflight.md`
- `read_first` 下列出的文件
- 执行冻结单元所需的目标仓库文件

除非交接包显式引用，否则不要重新打开阶段笔记做新的产品解释。

使用 `97-code-preflight.md` 作为共享执行工作台。它可在编码开始前和编码过程中更新，但仅限于执行状态，如当前焦点、进度、剩余工作、镜像任务状态、阻碍和暂停原因。

## 执行规则

1. 解析和验证
   - 从 `--case` 或 `--handoff` 解析 bundle
   - 确认 `90-code-handoff.md` 是唯一入口
   - 如果交接包不真实，fail closed
2. 在仓库现实中落地
   - 检查仓库存在性、当前文件、清单、命令可用性及相关现有代码
   - 在编辑前将仓库实际与交接包对比
3. 按顺序执行
   - 严格遵循 `implementation_units` 的顺序
   - 不静默跳过或重排单元
4. 增量验证
   - 在继续之前运行每个单元的验证
   - 在标记运行完成之前运行交接包级验证
5. 同步共享工作台
   - 在第一次编辑前更新 `97-code-preflight.md`，包含活跃上下文包、起始进度快照和第一个单元或批次
   - 当一个单元完成、进度有实质性变化以及运行暂停时再次更新
   - 如果存在导出的 OpenSpec `tasks.md`，也同步任务完成状态
6. 保护 UX 质量
   - 如果变更是用户可见的，确认首次打开体验没有明显损坏
7. 写回
   - 追加 `Runs/<run-id>/00-code-run.md`
   - 追加 `Runs/<run-id>/01-verification.md`
   - 当被阻塞或拒绝时追加 `Runs/<run-id>/02-reentry.md`

## 重入映射

- `goal_conflict` -> 重开 `A`
- `option_space_gap` -> 重开 `B`
- `requirement_conflict` -> 重开 `C`
- `critique_conflict` -> 重开 `D`
- `dependency_conflict` -> 重开 `E`
- `probe_invalidated` -> 重开 `F`
- `attack_surface_gap` -> 重开 `G`
- `review_gate_conflict` -> 重开 `H`
- `gate_refusal` -> 重开交接包中指定的最早真实阶段
