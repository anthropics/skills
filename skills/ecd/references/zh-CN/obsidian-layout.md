# Obsidian 布局

## 默认文件夹

在以下路径渲染 bundle：

`<vault-root>/Topics/Evolution-Constraint-Language/<date>-<case-slug>/`

如果提供了 `output_root`，则使用该基础文件夹。如果调用者传递了 `--output`，则使用显式目录。

## 必需文件

- `00-overview.md`
- `05-constraint-ledger.md`
- `10-a-preprocess.md`
- `20-b-divergence.md`
- `30-c-requirements.md`
- `40-d-critique.md`
- `50-e-closure.md`
- `60-f-probes.md`
- `70-g-red-blue.md`
- `80-h-review.md`
- `90-code-handoff.md`
- `91-canonical-contracts.md`
- `92-constraint-crosswalk.md`
- `95-execution-manifest.md`
- `96-code-batches.md`
- `97-code-preflight.md`
- `98-j-compile-for-code.md`
- `99-code-handoff.md`

可选：

- `00-overview-map.canvas`
- `Runs/<run-id>/00-code-run.md`
- `Runs/<run-id>/01-verification.md`
- `Runs/<run-id>/02-reentry.md` — 仅当 `/code` 阻塞或拒绝时
- `Runs/<run-id>/03-achieve.md` — 当 `/achieve` 执行时；此笔记是验收与归档关闭记录
- `OpenSpec/changes/<case-slug>/proposal.md`
- `OpenSpec/changes/<case-slug>/design.md`
- `OpenSpec/changes/<case-slug>/tasks.md`
- `OpenSpec/specs/<case-slug>/spec.md`

## 章节顺序

对于 `00-overview.md`：

1. 标题
2. 摘要
3. 原始请求
4. 最终结果
5. 阶段状态索引
6. 路径
7. 结构化块

对于每个阶段笔记：

1. 标题
2. 导航行
3. 目标
4. 叙述
5. 关键点
6. 决策
7. 待解决问题
8. 下一步动作
9. 结构化块

对于 `05` 和 `90` 等产物笔记：

1. 标题
2. 链接回 `[[00-overview]]`
3. 目标或角色摘要
4. 暴露冻结内容的关键章节
5. 结构化块

## 链接约定

- 每个笔记链接回 `[[00-overview]]`。
- 当存在时，将阶段笔记链接到紧邻的前一个和后一个笔记。
- 保持 wikilinks 基于文件名，不带 `.md`。
- 将 `00-code-run.md` 链接到 `[[90-code-handoff]]`。
- 将 `01-verification.md`、`02-reentry.md` 和 `03-achieve.md` 链接回 `[[00-code-run]]`。
