# 验收关闭手册

当用户在 `/code` 之后要求最终验证、关闭、验收或归档判断时使用此手册。

## 目标

`/achieve` 判断交付结果是否满足 `90-code-handoff.md` 中冻结的验收含义，然后记录该 case 是应作为已关闭证据归档还是保持打开。

## 输入

- 已验证的 bundle
- 最近一次真实的 code 运行证据
- 交接包中的验收检查
- 来自测试、构建和浏览器检查的验证证据

## 必需输出

写入 `Runs/<run-id>/03-achieve.md`，包含：

- verdict（裁决）
- archive_status（归档状态）
- archive_reason（归档理由）
- acceptance_results（验收结果）
- verification_summary（验证摘要）
- residual_issues（残留问题）
- next_actions（下一步动作）
- archive_refs（归档引用）
- evidence_refs（证据引用）

## 允许的裁决

- `achieved` — 已达成
- `achieved_with_followups` — 已达成，有跟进项
- `not_achieved` — 未达成

## 归档状态

- `archived` — 已归档
- `left_open` — 保持打开

## 规则

- 不得事后弱化验收含义
- 如果首次加载体验明显损坏，不得声称运行已达成
- 如果结果为 achieved 或 achieved_with_followups，将 case 归档为真实关闭记录
- 如果结果为 not_achieved，保持 case 打开，并建议最小的真实重开阶段或重跑动作
- 这里的"归档"指 bundle 内部的已记录关闭状态，而非将文件移动到其他文件夹
